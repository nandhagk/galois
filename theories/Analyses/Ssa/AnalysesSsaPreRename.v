(** * Ordered paths and nearest expression definitions

    Point paths project to block paths without losing parallel incoming edge identities.
    For example, internal instruction edges disappear and each crossing edge stays in order.
    Builds on: AnalysesSsaPreFrg and ProgramSsaPoints. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseIndex BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Framework Require Import FrameworkUtil FrameworkBitvector.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg.
Import List.ListNotations Cost.Notations.

Module PreRename.

Local Open Scope nat_scope.

(** Invalid frames retain their nearest definition and accumulated real-use provenance. *)
Record frame (B E U : Type) := Frame {
  selected : PreFrg.operand B E U;
  available : bool
}.
Arguments Frame {B E U}.
Arguments selected {B E U}.
Arguments available {B E U}.

(** Every scope shares the prepared expression dictionary and stores frames under dense IDs. *)
Record scope (B E U : Type) := Scope {
  symbols : Intern.t U;
  bindings : Map.t positive (frame B E U)
}.
Arguments Scope {B E U}.
Arguments symbols {B E U}.
Arguments bindings {B E U}.

Definition empty_scope {B E U} : scope B E U := Scope Intern.empty Map.empty.

Section Paths.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Let s := Pre.points (Pre.input c).

Definition missing (u : U) : frame B E U :=
  Frame (PreFrg.Operand (PreFrg.Unavailable u) false) false.
Definition top_id_c (frames : scope B E U) id u :=
  Map.find_or_c positive_encoding (missing u) id (bindings frames).
Definition top_id frames id u := Cost.value (top_id_c frames id u).
Definition top_c (frames : scope B E U) u :=
  let* id := Intern.find_c (Pre.eu (Pre.keys c)) u (symbols frames) in
  match id with
  | None => Cost.ret (missing u)
  | Some id => top_id_c frames id u
  end.
Definition top frames u := Cost.value (top_c frames u).

(** Missing scope bindings denote unavailable versions of the very same expression. *)
Theorem top_equation frames u :
  top frames u =
    match Intern.find (Pre.eu (Pre.keys c)) u (symbols frames) with
    | None => missing u
    | Some id => Map.find_or positive_encoding (missing u) id (bindings frames)
    end.
Proof.
  unfold top, top_c; rewrite Cost.value_bind.
  fold (Intern.find (Pre.eu (Pre.keys c)) u (symbols frames)).
  destruct (Intern.find (Pre.eu (Pre.keys c)) u (symbols frames)); reflexivity.
Qed.

Definition store_c (frames : scope B E U) id frame :=
  let* updated := Map.set_c positive_encoding id frame (bindings frames) in
  Cost.ret (Scope (symbols frames) updated).
Definition store frames id frame := Cost.value (store_c frames id frame).

(** Scope updates retain the shared symbol table and modify exactly one dense frame binding. *)
Theorem store_equation frames id frame :
  store frames id frame =
    Scope (symbols frames) (Map.set positive_encoding id frame (bindings frames)).
Proof.
  unfold store, store_c; rewrite Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

Definition initial_frame_c u : Cost.t (frame B E U) :=
  Cost.step ;;
  let* yes := Pre.initial_c (Pre.input c) u in
  Cost.ret (Frame
    (PreFrg.Operand (if yes then PreFrg.Initial u else PreFrg.Unavailable u) false) yes).
Definition initial_frame u := Cost.value (initial_frame_c u).

(** Entry frames distinguish actual initially available expressions from unavailable sentinels. *)
Theorem initial_frame_equation u :
  initial_frame u = Frame
    (PreFrg.Operand (if Pre.initial c u then PreFrg.Initial u else PreFrg.Unavailable u) false)
    (Pre.initial c u).
Proof.
  unfold initial_frame, initial_frame_c; autorewrite with galois_cost; reflexivity.
Qed.

Definition initial_scope_c family :=
  let* names := Intern.of_list_c (Pre.eu (Pre.keys c)) family in
  let* entries := Map.elements_c (Intern.inverse names) in
  let* pairs := map_c (fun pair =>
    let* frame := initial_frame_c (snd pair) in Cost.ret (fst pair, frame)) entries in
  let* frames := Map.of_list_c positive_encoding pairs in
  Cost.ret (Scope names frames).
Definition initial_scope family := Cost.value (initial_scope_c family).

(** Initial scopes materialize the supplied family once and retain every initial callback charge. *)
Theorem initial_scope_equation family :
  initial_scope family =
    Scope (Intern.of_list (Pre.eu (Pre.keys c)) family)
      (Map.of_list positive_encoding (map (fun pair => (fst pair, initial_frame (snd pair)))
        (Map.elements (Intern.inverse (Intern.of_list (Pre.eu (Pre.keys c)) family))))).
Proof.
  unfold initial_scope, initial_scope_c; rewrite !Cost.value_bind, value_map_c, Cost.value_ret.
  assert (Hpairs : forall entries : list (positive * U), map
    (fun pair => Cost.value
      (let* frame := initial_frame_c (snd pair) in Cost.ret (fst pair, frame))) entries =
    map (fun pair => (fst pair, initial_frame (snd pair))) entries).
  { intro entries; apply map_ext; intros [id u].
    rewrite Cost.value_bind, Cost.value_ret; reflexivity. }
  rewrite Hpairs; reflexivity.
Qed.

Fixpoint project_edges_c (es : list E) : Cost.t (list BE) :=
  match es with
  | [] => Cost.ret []
  | e :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* edge := SsaPoints.block_edge_of_c s e in
    let* tail := project_edges_c rest in
    Cost.ret (match edge with None => tail | Some be => be :: tail end)
  end.
Definition project_edges es := Cost.value (project_edges_c es).

(** Projection drops internal instructions and retains ordered incoming edge occurrences. *)
Theorem project_edges_equation es :
  project_edges es = flat_map (fun e =>
    match SsaPoints.block_edge_of s e with None => [] | Some be => [be] end) es.
Proof.
  unfold project_edges; induction es as [|e rest IH]; [reflexivity|].
  cbn [project_edges_c flat_map]; autorewrite with galois_cost; rewrite IH.
  fold (SsaPoints.block_edge_of s e); destruct (SsaPoints.block_edge_of s e); reflexivity.
Qed.

(** Point-to-block projection preserves both endpoints and the ordered sequence of crossings. *)
Theorem project_path :
  Pre.laws c ->
  forall start es finish, In start (Graph.nodes (Pre.pg c)) ->
    path (Pre.pg c) start es finish ->
    path (Pre.bg c) (SsaPoints.block_of_point s start) (project_edges es)
      (SsaPoints.block_of_point s finish).
Proof.
  intros Hlaw start es finish Hstart Hpath.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  revert Hstart; induction Hpath as [n|e rest finish Hedge Hpath IH]; intro Hstart.
  - rewrite project_edges_equation; cbn [flat_map]; constructor.
  - pose proof (out_target_in (points_graph_wf Hpoints) _ e Hstart Hedge) as Htarget.
    specialize (IH Htarget).
    pose proof (point_edge_projection Hpoints _ e Hstart Hedge) as Hprojection.
    rewrite project_edges_equation; cbn [flat_map].
    fold s in Hprojection.
    destruct (SsaPoints.block_edge_of s e) as [be|] eqn:Hcross.
    + destruct Hprojection as [Hout [Hblock Hrest]]; cbn [app].
      change (Graph.target (Pre.bg c) be =
        SsaPoints.block_of_point s (Graph.target (Pre.pg c) e)) in Hblock.
      rewrite <- Hblock in IH.
      pose proof (out_source (blocks_graph_wf Hpoints) _ be Hout) as Hsource.
      rewrite <- Hsource; constructor.
      * rewrite Hsource; exact Hout.
      * rewrite project_edges_equation in IH; exact IH.
    + cbn [app]; rewrite Hprojection.
      rewrite <- project_edges_equation; exact IH.
Qed.

(** Nearest definitions are ordered by semantic point dominance among the graph's own versions. *)
Definition nearest_version (g : PreFrg.frg B BE E U) u n d : Prop :=
  In d (PreFrg.versions g) /\ PreFrg.version_expr d = u /\
  exists q, PreFrg.version_point c d = Some q /\ dominates (Pre.pg c) q n /\
    forall other p, In other (PreFrg.versions g) -> PreFrg.version_expr other = u ->
      PreFrg.version_point c other = Some p -> dominates (Pre.pg c) p n ->
      dominates (Pre.pg c) p q.

(** An unused frame has no selected real occurrence whose target dominates the query point. *)
Definition no_dominating_real_use (g : PreFrg.frg B BE E U) n d : Prop :=
  forall e, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d ->
    ~ dominates (Pre.pg c) (Graph.target (Pre.pg c) e) n.

(** Reuse requires a nearest version and kill-free paths that do not revisit its definition. *)
Definition reusable (g : PreFrg.frg B BE E U) u n d : Prop :=
  nearest_version g u n d /\
  exists q, PreFrg.version_point c d = Some q /\
    forall es, path (Pre.pg c) q es n ->
      Forall (fun e => Graph.target (Pre.pg c) e <> q) es ->
      Forall (fun e => Pre.killed c e u = false) es.

(** A graph definition is nearest at its own completed definition point. *)
Theorem nearest_at_definition (g : PreFrg.frg B BE E U) d {q} :
  In d (PreFrg.versions g) -> PreFrg.version_point c d = Some q ->
    nearest_version g (PreFrg.version_expr d) q d.
Proof.
  intros Hd Hpoint; split; [exact Hd|]; split; [reflexivity|].
  exists q; split; [exact Hpoint|]; split; [apply dominates_refl|].
  intros other point Hother Hexpr Hdefinition Hdominance; exact Hdominance.
Qed.

(** Two nearest definitions have mutually dominating definition points. *)
Lemma nearest_points_mutual (g : PreFrg.frg B BE E U) :
  forall u n d other, nearest_version g u n d -> nearest_version g u n other ->
  exists q p, PreFrg.version_point c d = Some q /\
    PreFrg.version_point c other = Some p /\
    dominates (Pre.pg c) q n /\ dominates (Pre.pg c) p n /\
    dominates (Pre.pg c) q p /\ dominates (Pre.pg c) p q.
Proof.
  intros u n d other [Hd [Hexpr [q [Hq [Hdom Hnearest]]]]]
    [Hother [Hexpr' [p [Hp [Hdom' Hnearest']]]]].
  exists q, p; repeat split; try assumption.
  - exact (Hnearest' d q Hd Hexpr Hq Hdom).
  - exact (Hnearest other p Hother Hexpr' Hp Hdom').
Qed.

(** At a reachable point, eligible source definitions determine
    at most one nearest graph version. *)
Theorem nearest_version_unique (g : PreFrg.frg B BE E U) :
  Pre.laws c ->
  (forall d, In d (PreFrg.versions g) -> PreFrg.definition_domain c d) ->
  forall u n d other, reachable (Pre.pg c) n ->
    nearest_version g u n d -> nearest_version g u n other -> d = other.
Proof.
  intros Hlaw Hdomain u n d other Hn Hd Hother.
  destruct (nearest_points_mutual g u n d other Hd Hother)
    as [q [p [Hq [Hp [Hqn [Hpn [Hqp Hpq]]]]]]].
  assert (Hsame : q = p).
  { apply (dominates_antisym_reachable (Pre.en (Pre.keys c))
      (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c) q p).
    - exact (DomCheck.dominator_reachable (Pre.pg c) q n Hn Hqn).
    - exact (DomCheck.dominator_reachable (Pre.pg c) p n Hn Hpn).
    - exact Hqp.
    - exact Hpq. }
  subst p; destruct Hd as [Hd [Hexpr _]], Hother as [Hother [Hexpr' _]].
  eapply PreFrg.definition_points_unique; [exact Hlaw|apply Hdomain; exact Hd|
    apply Hdomain; exact Hother|congruence|exact Hq|exact Hp].
Qed.

End Paths.

(** Each ordered chain prefix reaches its selected later point by a prefix of instruction edges. *)
Lemma chain_prefix_path {N E} (g : Graph.t N E) {ns es} :
  graph_wf g -> point_chain g ns es ->
  forall n rest target, ns = n :: rest -> In target ns ->
    exists prefix, path g n prefix target /\ incl prefix es.
Proof.
  intros Hwf Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH].
  - intros first rest target Heq Hin; inversion Heq; subst first rest.
    destruct Hin as [<-|[]]; exists []; split; [constructor|intros e []].
  - intros first rest target Heq Hin; inversion Heq; subst first rest.
    destruct Hin as [<-|Hin].
    + exists []; split; [constructor|intros e []].
    + destruct (IH next ns target eq_refl Hin) as [prefix [Hpath Hsub]].
      exists (edge :: prefix); split.
      * pose proof (out_source Hwf n edge Hedge) as Hsource.
        rewrite <- Hsource; constructor.
        -- rewrite Hsource; exact Hedge.
        -- rewrite Htarget; exact Hpath.
      * intros e [<-|He]; [now left|right; exact (Hsub e He)].
Qed.

(** Graph path concatenation retains the shared endpoint and every ordered edge occurrence. *)
Lemma path_app {N E} (g : Graph.t N E) :
  forall start es mid tail finish, path g start es mid -> path g mid tail finish ->
    path g start (es ++ tail) finish.
Proof.
  intros start es mid tail finish Hprefix Htail.
  induction Hprefix as [n|e rest mid Hedge Hpath IH]; [exact Htail|].
  cbn [app]; constructor; [exact Hedge|apply IH; exact Htail].
Qed.

(** A path endpoint is its start or the target of one of its ordered edge occurrences. *)
Lemma path_endpoint {N E} (g : Graph.t N E) {start es finish} :
  path g start es finish ->
  finish = start \/ exists e, In e es /\ Graph.target g e = finish.
Proof.
  intro Hpath; induction Hpath as [n|e rest finish Hedge Hpath IH].
  - now left.
  - right; destruct IH as [Heq|[a [Ha Htarget]]].
    + exists e; split; [now left|symmetry; exact Heq].
    + exists a; split; [now right|exact Htarget].
Qed.

(** Every nonempty path ends in a real final edge and a prefix reaching that edge's source. *)
Lemma path_last {N E} (g : Graph.t N E) {start es finish} :
  path g start es finish -> es <> [] ->
  exists prefix e, es = prefix ++ [e] /\ path g start prefix (Graph.source g e) /\
    Graph.target g e = finish /\ In e (Graph.out g (Graph.source g e)).
Proof.
  intro Hpath; induction Hpath as [n|a rest finish Hedge Hpath IH]; intro Hnonempty.
  - contradiction.
  - destruct rest as [|b rest].
    + inversion Hpath; subst finish; exists [], a; split; [reflexivity|].
      split; [constructor|auto].
    + destruct (IH ltac:(discriminate)) as [prefix [e [Hes [Hprefix [Htarget He]]]]].
      exists (a :: prefix), e; split; [cbn [app]; now rewrite Hes|].
      split; [constructor; assumption|auto].
Qed.

(** A visited edge has a prefix path reaching its source
    without adding unrelated edge occurrences. *)
Lemma path_prefix_source {N E} (g : Graph.t N E) {start es finish e} :
  path g start es finish -> In e es ->
  exists prefix, path g start prefix (Graph.source g e) /\ incl prefix es.
Proof.
  intro Hpath; induction Hpath as [n|a rest finish Hedge Hpath IH]; intro Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - exists []; split; [constructor|intros x []].
  - destruct (IH Hin) as [prefix [Hprefix Hsub]].
    exists (a :: prefix); split; [constructor; assumption|].
    intros x [<-|Hx]; [now left|right; exact (Hsub x Hx)].
Qed.

(** A visited edge has a prefix path reaching its target and using only original occurrences. *)
Lemma path_prefix_target {N E} (g : Graph.t N E) {start es finish e} :
  path g start es finish -> In e es ->
  exists prefix, path g start prefix (Graph.target g e) /\ incl prefix es.
Proof.
  intro Hpath; induction Hpath as [n|a rest finish Hedge Hpath IH]; intro Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - exists [a]; split; [constructor; [exact Hedge|constructor]|].
    intros x [<-|[]]; now left.
  - destruct (IH Hin) as [prefix [Hprefix Hsub]].
    exists (a :: prefix); split; [constructor; assumption|].
    intros x [<-|Hx]; [now left|right; exact (Hsub x Hx)].
Qed.

(** A selected path occurrence splits the same edge list into its exact prefix and suffix. *)
Lemma path_split {N E} (g : Graph.t N E) {start es finish e} :
  path g start es finish -> In e es ->
  exists prefix suffix, es = prefix ++ e :: suffix /\
    path g start prefix (Graph.source g e) /\ path g (Graph.target g e) suffix finish.
Proof.
  intro Hpath; induction Hpath as [n|a rest finish Hedge Hpath IH]; intro Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - exists [], rest; split; [reflexivity|split; [constructor|exact Hpath]].
  - destruct (IH Hin) as [prefix [suffix [Hsplit [Hprefix Hsuffix]]]].
    exists (a :: prefix), suffix; split; [cbn [app]; now rewrite Hsplit|].
    split; [constructor; assumption|exact Hsuffix].
Qed.

(** A visited nonterminal point is the source of a later edge in the same path. *)
Lemma path_leaves {N E} (g : Graph.t N E) {start es finish point} :
  path g start es finish -> point <> finish ->
  (point = start \/ exists e, In e es /\ Graph.target g e = point) ->
  exists e, In e es /\ Graph.source g e = point.
Proof.
  intro Hpath; induction Hpath as [n|e rest finish Hedge Hpath IH]; intros Hne Hvisit.
  - destruct Hvisit as [Heq|[e [[] _]]]; congruence.
  - destruct Hvisit as [Heq|[a [[<-|Ha] Htarget]]].
    + exists e; split; [now left|symmetry; exact Heq].
    + destruct (IH Hne (or_introl (eq_sym Htarget))) as [a [Ha Hsource]].
      exists a; split; [now right|exact Hsource].
    + destruct (IH Hne (or_intror (ex_intro _ a (conj Ha Htarget)))) as [next [Hnext Hsource]].
      exists next; split; [now right|exact Hsource].
Qed.

(** An ordered instruction chain is a path from its first point to its last point. *)
Lemma chain_path {N E} (g : Graph.t N E) {ns es first default} :
  graph_wf g -> point_chain g ns es -> nth_error ns 0 = Some first ->
    path g first es (last ns default).
Proof.
  intros Hwf Hchain; revert first.
  induction Hchain as [n|n next ns e es Hedge Htarget Hchain IH]; intros first Hfirst;
    cbn [nth_error] in Hfirst; inversion Hfirst; subst first.
  - constructor.
  - change (path g n (e :: es) (last (next :: ns) default)).
    rewrite <- (out_source Hwf n e Hedge); constructor.
    + rewrite (out_source Hwf n e Hedge); exact Hedge.
    + rewrite Htarget; apply IH; reflexivity.
Qed.

(** Every chain member is reached by an instruction prefix from its actual first point. *)
Lemma chain_prefix {N E} (g : Graph.t N E) {ns es first} :
  graph_wf g -> point_chain g ns es -> nth_error ns 0 = Some first ->
  forall n, In n ns -> exists prefix, path g first prefix n /\ incl prefix es.
Proof.
  intros Hwf Hchain Hfirst n Hmember.
  destruct ns as [|head rest]; cbn [nth_error] in Hfirst; [discriminate|].
  inversion Hfirst; subst head.
  exact (chain_prefix_path g Hwf Hchain first rest n eq_refl Hmember).
Qed.

(** If each instruction source dominates its target, every point dominates the end of its block. *)
Lemma chain_member_dominates_last {N E} (g : Graph.t N E) {ns es default} :
  graph_wf g -> point_chain g ns es ->
  (forall e, In e es -> dominates g (Graph.source g e) (Graph.target g e)) ->
  forall q, In q ns -> dominates g q (last ns default).
Proof.
  intros Hwf Hchain.
  induction Hchain as [n|n next ns e es Hedge Htarget Hchain IH]; intros Hedges q Hq.
  - destruct Hq as [<-|[]]; apply dominates_refl.
  - assert (Htail : forall a, In a es -> dominates g (Graph.source g a) (Graph.target g a)).
    { intros a Ha; apply Hedges; now right. }
    change (dominates g q (last (next :: ns) default)).
    destruct Hq as [<-|Hq]; [|exact (IH Htail q Hq)].
    eapply dominates_trans with (b := next).
    + pose proof (Hedges e (or_introl eq_refl)) as Hdom.
      rewrite (out_source Hwf n e Hedge), Htarget in Hdom; exact Hdom.
    + apply IH; [exact Htail|now left].
Qed.

(** A strict dominator of an edge's target also dominates its source along every entry path. *)
Lemma strict_target_dominates_source {N E} (g : Graph.t N E) :
  forall e q, In e (Graph.out g (Graph.source g e)) ->
    strictly_dominates g q (Graph.target g e) -> dominates g q (Graph.source g e).
Proof.
  intros e q Hedge [Hdom Hne] start es Hentry Hpath.
  assert (Hsingle : path g (Graph.source g e) [e] (Graph.target g e)).
  { constructor; [exact Hedge|constructor]. }
  destruct (Hdom start (es ++ [e]) Hentry (path_app g _ _ _ _ _ Hpath Hsingle))
    as [Heq|[edge [Hin Htarget]]]; [now left|].
  apply in_app_iff in Hin; destruct Hin as [Hin|[<-|[]]].
  - right; exists edge; auto.
  - exfalso; apply Hne; symmetry; exact Htarget.
Qed.

(** Dominance of every ordered path edge composes to dominance of its endpoint. *)
Lemma path_dominance_chain {N E} (g : Graph.t N E) {start es finish} :
  path g start es finish ->
  (forall e, In e es -> dominates g (Graph.source g e) (Graph.target g e)) ->
    dominates g start finish.
Proof.
  intro Hpath; induction Hpath as [n|e rest finish He Hpath IH]; intro Hedges.
  - apply dominates_refl.
  - eapply dominates_trans; [apply Hedges; now left|].
    apply IH; intros edge Hedge; apply Hedges; now right.
Qed.

(** Forward textual indexes imply point dominance
    along an internally dominating instruction chain. *)
Lemma chain_index_dominates {N E} (g : Graph.t N E) {ns es} :
  graph_wf g -> point_chain g ns es ->
  (forall e, In e es -> dominates g (Graph.source g e) (Graph.target g e)) ->
  forall i j q n, nth_error ns i = Some q -> nth_error ns j = Some n -> i <= j ->
    dominates g q n.
Proof.
  intros Hwf Hchain.
  induction Hchain as [head|head next ns e es Hedge Htarget Hchain IH];
    intros Hedges i j q n Hq Hn Horder.
  - assert (Hi : i < length [head]) by (apply nth_error_Some; congruence).
    assert (Hj : j < length [head]) by (apply nth_error_Some; congruence).
    cbn [length] in Hi, Hj; assert (Hi0 : i = 0) by lia; assert (Hj0 : j = 0) by lia.
    subst i j; cbn [nth_error] in Hq, Hn.
    inversion Hq; inversion Hn; subst; apply dominates_refl.
  - destruct i as [|i], j as [|j]; cbn [nth_error] in Hq, Hn; try lia.
    + inversion Hq; inversion Hn; subst; apply dominates_refl.
    + inversion Hq; subst q; eapply dominates_trans with (b := next).
      * pose proof (Hedges e (or_introl eq_refl)) as Hdom.
        rewrite (out_source Hwf head e Hedge), Htarget in Hdom; exact Hdom.
      * apply (IH ltac:(intros a Ha; apply Hedges; now right) 0 j next n eq_refl Hn); lia.
    + apply (IH ltac:(intros a Ha; apply Hedges; now right) i j q n Hq Hn); lia.
Qed.

(** Accumulated graph output records each fresh definition when its real occurrence is visited. *)
Record accumulator (B BE E U : Type) := Accumulator {
  occurrence_index : Map.t E (PreFrg.version B E U);
  fresh_index : FinSet.t E;
  link_index : Map.t ((B * U) * BE) (PreFrg.operand B E U);
  unsafe_index : FinSet.t (B * U);
  created : list (PreFrg.version B E U)
}.
Arguments Accumulator {B BE E U}.
Arguments occurrence_index {B BE E U}.
Arguments fresh_index {B BE E U}.
Arguments link_index {B BE E U}.
Arguments unsafe_index {B BE E U}.
Arguments created {B BE E U}.

Definition empty_accumulator {B BE E U} : accumulator B BE E U :=
  Accumulator Map.empty FinSet.empty Map.empty FinSet.empty [].

(** Instruction events contain prepared dense expression IDs and retain ordered kill occurrences. *)
Record event (N U : Type) := Event {
  evaluation : option (positive * U);
  alterations : list (positive * U);
  endpoint : N
}.
Arguments Event {N U}.
Arguments evaluation {N U}.
Arguments alterations {N U}.
Arguments endpoint {N U}.

(** Each outgoing argument remembers the exact incoming edge and its simultaneous translation. *)
Record argument (B BE U : Type) := Argument {
  argument_phi : B * U;
  argument_edge : BE;
  argument_input : U;
  argument_id : option positive
}.
Arguments Argument {B BE U}.
Arguments argument_phi {B BE U}.
Arguments argument_edge {B BE U}.
Arguments argument_input {B BE U}.
Arguments argument_id {B BE U}.

(** Shared indexes are built once before the dominator walk and contain no semantic evidence. *)
Record prepared (B BE N E U : Type) := Prepared {
  eligible_family : list U;
  phi_keys : list (B * U);
  entry_scope : scope B E U;
  family_ids : list (positive * U);
  events : Map.t E (event N U);
  exit_points : FinSet.t N;
  phi_definitions : Index.t B (B * (positive * U));
  arguments : Index.t B (B * argument B BE U);
  children : Index.t positive (positive * positive);
  parent_pairs : list (positive * positive);
  root_ids : list positive;
  walk_budget : positive
}.
Arguments Prepared {B BE N E U}.
Arguments eligible_family {B BE N E U}.
Arguments phi_keys {B BE N E U}.
Arguments entry_scope {B BE N E U}.
Arguments family_ids {B BE N E U}.
Arguments events {B BE N E U}.
Arguments exit_points {B BE N E U}.
Arguments phi_definitions {B BE N E U}.
Arguments arguments {B BE N E U}.
Arguments children {B BE N E U}.
Arguments parent_pairs {B BE N E U}.
Arguments root_ids {B BE N E U}.
Arguments walk_budget {B BE N E U}.

Section Preparation.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition lookup_expression_c names u :=
  let* id := Intern.find_c (Pre.eu (Pre.keys c)) u names in
  Cost.ret (option_map (fun id => (id, u)) id).

Definition evaluation_c names e :=
  Cost.step ;;
  let* instance := Pre.recomputed_c (Pre.input c) e in
  match instance with
  | None => Cost.ret None
  | Some u =>
    Cost.step ;;
    let* pure := Pre.pure_c (Pre.input c) u in
    if pure then lookup_expression_c names u else Cost.ret None
  end.

Definition event_c names e :=
  let* instance := evaluation_c names e in
  Cost.step ;;
  let* kills := Bitvector.kill_c (Pre.expr (Pre.input c)) e in
  let* changes := Prepared.present_c (lookup_expression_c names) kills in
  Cost.step ;;
  let* target := Graph.target_c (Pre.pg c) e in
  Cost.ret (Event instance changes target).

Definition event_index_c names :=
  let* es := fw_edges_c (Pre.point_cfg c) in
  let* pairs := map_c (fun e =>
    let* description := event_c names e in Cost.ret (e, description)) es in
  Map.of_list_c (Pre.ee (Pre.keys c)) pairs.

Definition exits_c :=
  let* exits := filter_c (fun n =>
    Cost.step ;;
    let* ending := Pre.exit_point_c (Pre.input c) n in
    if ending then Cost.ret true else
      Cost.step ;;
      let* outgoing := Graph.out_c (Pre.pg c) n in
      Cost.ret (match outgoing with [] => true | _ :: _ => false end))
    (Graph.nodes (Pre.pg c)) in
  FinSet.of_list_c (Pre.en (Pre.keys c)) exits.

Definition phi_pairs_c names (keys : list (B * U)) :=
  Prepared.present_c (fun key =>
    let* id := Intern.find_c (Pre.eu (Pre.keys c)) (snd key) names in
    Cost.ret (option_map (fun id => (fst key, (id, snd key))) id)) keys.

Definition arguments_c names keys :=
  let* pairs := fw_flat_map_c (fun key =>
    let* es := Prepared.incoming_c (Pre.blocks c) (fst key) in
    fw_flat_map_c (fun be =>
      Cost.step ;;
      let* translated := Pre.translate_c (Pre.input c) be (snd key) in
      match translated with
      | None => Cost.ret []
      | Some u =>
        let* id := Intern.find_c (Pre.eu (Pre.keys c)) u names in
        Cost.step ;;
        let* source := Graph.source_c (Pre.bg c) be in
        Cost.ret [(source, Argument key be u id)]
      end) es) keys in
  Index.group_by_c (Pre.eb (Pre.keys c)) (fun pair => Cost.ret (fst pair)) pairs.

Definition rename_budget_c (roots : list positive) (parents : list (positive * positive)) :=
  let* roots := PreFamily.count_c roots in
  let* parents := PreFamily.count_c parents in
  let* total := PreFamily.add_c roots parents in
  PreFamily.bits_c total ;;
  Cost.ret (N.succ_pos total).

Definition prepare_c (data : PreFrg.phi_data) : Cost.t (prepared B BE N E U) :=
  let* family := filter_c (fun u => Cost.step ;; Pre.pure_c (Pre.input c) u)
    (PreFrg.all_family data) in
  let* scope := initial_scope_c c family in
  let names := symbols scope in
  let* ids := Map.elements_c (Intern.inverse names) in
  let* event_index := event_index_c names in
  let* endings := exits_c in
  let* all_keys := FinSet.elements_c (PreFrg.sites data) in
  let* phi_pairs := phi_pairs_c names all_keys in
  let* keys := map_c (fun pair => Cost.ret (fst pair, snd (snd pair))) phi_pairs in
  let* phis := Index.group_by_c (Pre.eb (Pre.keys c))
    (fun pair => Cost.ret (fst pair)) phi_pairs in
  let* args := arguments_c names keys in
  let* parents := Map.elements_c (Dom.idom (Pre.dom c)) in
  let* child_index := Index.group_by_c positive_encoding
    (fun pair => Cost.ret (snd pair)) parents in
  let roots := Prepared.entry_ids (Pre.blocks c) in
  let* budget := rename_budget_c roots parents in
  Cost.ret (Prepared family keys scope ids event_index endings phis args
    child_index parents roots budget).
Definition prepare data := Cost.value (prepare_c data).

(** Expression preparation retains the same client value and its actual dense lookup result. *)
Theorem lookup_expression_value names u :
  Cost.value (lookup_expression_c names u) =
    option_map (fun id => (id, u)) (Intern.find (Pre.eu (Pre.keys c)) u names).
Proof.
  unfold lookup_expression_c; rewrite Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

(** Eligible event preparation uses the original recomputation and purity callbacks. *)
Theorem evaluation_value names e :
  Cost.value (evaluation_c names e) =
    match Pre.recomputed c e with
    | None => None
    | Some u => if Pre.pure c u then
        option_map (fun id => (id, u)) (Intern.find (Pre.eu (Pre.keys c)) u names)
      else None
    end.
Proof.
  unfold evaluation_c; rewrite !Cost.value_bind.
  fold (Pre.recomputed c e); destruct (Pre.recomputed c e) as [u|]; [|reflexivity].
  rewrite !Cost.value_bind; fold (Pre.pure c u); destruct (Pre.pure c u);
    [apply lookup_expression_value|reflexivity].
Qed.

(** Event descriptions retain the ordered successful kill-ID lookups and actual endpoint. *)
Theorem event_value names e :
  Cost.value (event_c names e) =
    Event (Cost.value (evaluation_c names e))
      (Cost.value (Prepared.present_c (lookup_expression_c names)
        (Bitvector.kill (Pre.expr (Pre.input c)) e))) (Graph.target (Pre.pg c) e).
Proof.
  unfold event_c; do 6 rewrite Cost.value_bind at 1.
  rewrite Cost.value_ret; reflexivity.
Qed.

(** The event map is constructed from the original ordered point-edge occurrences. *)
Theorem event_index_value names :
  Cost.value (event_index_c names) = Map.of_list (Pre.ee (Pre.keys c))
    (map (fun e => (e, Cost.value (event_c names e))) (Cfg.edges (Pre.point_cfg c))).
Proof.
  unfold event_index_c; rewrite Cost.value_bind, fw_edges_value, Cost.value_bind, value_map_c.
  assert (Hpairs : map (fun e =>
    Cost.value (let* description := event_c names e in Cost.ret (e, description)))
      (Cfg.edges (Pre.point_cfg c)) =
    map (fun e => (e, Cost.value (event_c names e))) (Cfg.edges (Pre.point_cfg c))).
  { apply map_ext; intro e; rewrite Cost.value_bind, Cost.value_ret; reflexivity. }
  rewrite Hpairs; reflexivity.
Qed.

(** Exit preparation retains the original short-circuiting exit and successor observations. *)
Theorem exits_value :
  Cost.value exits_c = FinSet.of_list (Pre.en (Pre.keys c))
    (filter (fun n => Cost.value
      (Cost.step ;;
       let* ending := Pre.exit_point_c (Pre.input c) n in
       if ending then Cost.ret true else
         Cost.step ;;
         let* outgoing := Graph.out_c (Pre.pg c) n in
         Cost.ret (match outgoing with [] => true | _ :: _ => false end)))
      (Graph.nodes (Pre.pg c))).
Proof.
  unfold exits_c; rewrite Cost.value_bind, value_filter_c; reflexivity.
Qed.

Definition argument_pairs names keys :=
  flat_map (fun key => flat_map (fun be =>
    match Pre.translate c be (snd key) with
    | None => []
    | Some u => [(Graph.source (Pre.bg c) be,
        Argument key be u (Intern.find (Pre.eu (Pre.keys c)) u names))]
    end) (Cost.value (Prepared.incoming_c (Pre.blocks c) (fst key)))) keys.

(** Argument indexing preserves the ordered incoming-edge translations and optional dense IDs. *)
Theorem arguments_value names keys :
  Cost.value (arguments_c names keys) =
    Index.group_by (Pre.eb (Pre.keys c)) fst (argument_pairs names keys).
Proof.
  unfold arguments_c; rewrite Cost.value_bind, Index.group_by_c_value.
  assert (Hpairs : Cost.value (fw_flat_map_c (fun key =>
    let* es := Prepared.incoming_c (Pre.blocks c) (fst key) in
    fw_flat_map_c (fun be =>
      Cost.step ;;
      let* translated := Pre.translate_c (Pre.input c) be (snd key) in
      match translated with
      | None => Cost.ret []
      | Some u =>
        let* id := Intern.find_c (Pre.eu (Pre.keys c)) u names in
        Cost.step ;;
        let* source := Graph.source_c (Pre.bg c) be in
        Cost.ret [(source, Argument key be u id)]
      end) es) keys) = argument_pairs names keys).
  { rewrite fw_flat_map_value; unfold argument_pairs.
    induction keys as [|key rest IH]; [reflexivity|].
    cbn [flat_map]; rewrite IH, Cost.value_bind, fw_flat_map_value; f_equal.
    induction (Cost.value (Prepared.incoming_c (Pre.blocks c) (fst key)))
      as [|be edges IHedges]; [reflexivity|].
    cbn [flat_map]; rewrite IHedges; do 2 rewrite Cost.value_bind at 1.
    fold (Pre.translate c be (snd key)).
    destruct (Pre.translate c be (snd key)) as [u|]; [|reflexivity].
    do 3 rewrite Cost.value_bind at 1; rewrite Cost.value_ret; reflexivity. }
  rewrite Hpairs; reflexivity.
Qed.

(** The renaming budget is built in binary and leaves one step for the stopping callback. *)
Theorem rename_budget_equation roots parents :
  Cost.value (rename_budget_c roots parents) =
    N.succ_pos (N.of_nat (length roots) + N.of_nat (length parents))%N.
Proof.
  unfold rename_budget_c; rewrite !Cost.value_bind.
  fold (PreFamily.count roots); fold (PreFamily.count parents).
  rewrite !PreFamily.count_value, PreFamily.add_value, Cost.value_ret; reflexivity.
Qed.

(** Preparation exposes its literal cached observations without recomputing a program index. *)
Theorem prepare_equation data :
  prepare data =
    let family := filter (Pre.pure c) (PreFrg.all_family data) in
    let scope := initial_scope c family in
    let names := symbols scope in
    let pairs := Cost.value (phi_pairs_c names (FinSet.elements (PreFrg.sites data))) in
    let keys := map (fun pair => (fst pair, snd (snd pair))) pairs in
    let parents := Map.elements (Dom.idom (Pre.dom c)) in
    let roots := Prepared.entry_ids (Pre.blocks c) in
    Prepared family keys scope (Map.elements (Intern.inverse names))
      (Cost.value (event_index_c names)) (Cost.value exits_c)
      (Index.group_by (Pre.eb (Pre.keys c)) fst pairs)
      (Cost.value (arguments_c names keys))
      (Index.group_by positive_encoding snd parents) parents roots
      (N.succ_pos (N.of_nat (length roots) + N.of_nat (length parents)))%N.
Proof.
  unfold prepare, prepare_c.
  do 13 rewrite Cost.value_bind at 1.
  rewrite Cost.value_ret at 1.
  rewrite !(value_filter_c (fun u => Cost.step ;; Pre.pure_c (Pre.input c) u)).
  rewrite !(value_map_c (fun pair : B * (positive * U) =>
    Cost.ret (fst pair, snd (snd pair)))).
  rewrite (Index.group_by_c_value (Pre.eb (Pre.keys c))).
  rewrite (Index.group_by_c_value positive_encoding), rename_budget_equation; reflexivity.
Qed.

(** Walk roots, parent occurrences, child buckets and fuel are the actual supplied tree indexes. *)
Theorem prepare_walk_equations data :
  root_ids (prepare data) = Prepared.entry_ids (Pre.blocks c) /\
  parent_pairs (prepare data) = Map.elements (Dom.idom (Pre.dom c)) /\
  children (prepare data) =
    Index.group_by positive_encoding snd (Map.elements (Dom.idom (Pre.dom c))) /\
  walk_budget (prepare data) =
    N.succ_pos (N.of_nat (length (Prepared.entry_ids (Pre.blocks c))) +
      N.of_nat (length (Map.elements (Dom.idom (Pre.dom c)))))%N.
Proof.
  unfold prepare, prepare_c; rewrite !Cost.value_bind, Cost.value_ret.
  cbn [root_ids parent_pairs children walk_budget].
  rewrite Index.group_by_c_value, rename_budget_equation; repeat split; reflexivity.
Qed.

End Preparation.

Section Transfer.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition mark_c (frames : scope B E U) (acc : accumulator B BE E U) (key : positive * U) :=
  let* frame := top_id_c frames (fst key) (snd key) in
  match selected frame with
  | PreFrg.Operand (PreFrg.Phi b u) false =>
    let* marked := FinSet.add_c (PreFrg.phi_encoding c) (b, u) (unsafe_index acc) in
    Cost.ret (Accumulator (occurrence_index acc) (fresh_index acc) (link_index acc)
      marked (created acc))
  | _ => Cost.ret acc
  end.

Definition mark_exit_c (index : prepared B BE N E U) n
    (work : scope B E U * accumulator B BE E U) :=
  let* ending := FinSet.mem_c (Pre.en (Pre.keys c)) n (exit_points index) in
  if ending then
    let* acc := fold_left_c (mark_c (fst work)) (family_ids index) (snd work) in
    Cost.ret (fst work, acc)
  else Cost.ret work.

Definition occurrence_c e (instance : option (positive * U))
    (work : scope B E U * accumulator B BE E U) :=
  match instance with
  | None => Cost.ret (work, None)
  | Some (id, u) =>
    let '(frames, acc) := work in
    let* frame := top_id_c frames id u in
    let* same := if available frame then
      match PreFrg.operand_version (selected frame) with
      | PreFrg.Unavailable _ => Cost.ret false
      | d => eqb_c (Pre.eu (Pre.keys c)) (PreFrg.version_expr d) u
      end else Cost.ret false in
    let d := if same then PreFrg.operand_version (selected frame) else PreFrg.Fresh e u in
    let* occurrences := Map.set_c (Pre.ee (Pre.keys c)) e d (occurrence_index acc) in
    if same then
      let* frames := store_c frames id (Frame (PreFrg.Operand d true) true) in
      Cost.ret ((frames, Accumulator occurrences (fresh_index acc) (link_index acc)
        (unsafe_index acc) (created acc)), None)
    else
      let* fresh := FinSet.add_c (Pre.ee (Pre.keys c)) e (fresh_index acc) in
      Cost.ret ((frames, Accumulator occurrences fresh (link_index acc) (unsafe_index acc)
        (d :: created acc)), Some (id, u))
  end.

Definition alter_c (instance : option (positive * U))
    (work : scope B E U * accumulator B BE E U) (key : positive * U) :=
  let '(frames, acc) := work in
  let* same := match instance with
    | None => Cost.ret false
    | Some current => eqb_c positive_encoding (fst current) (fst key)
    end in
  let* acc := if same then Cost.ret acc else mark_c frames acc key in
  let* frame := top_id_c frames (fst key) (snd key) in
  let* frames := store_c frames (fst key) (Frame (selected frame) false) in
  Cost.ret (frames, acc).

Definition install_phi_c b (frames : scope B E U) (pair : B * (positive * U)) :=
  store_c frames (fst (snd pair))
    (Frame (PreFrg.Operand (PreFrg.Phi b (snd (snd pair))) false) true).

Definition definitions_c (index : prepared B BE N E U) b parameter e fresh frames :=
  let* frames := match fresh with
    | None => Cost.ret frames
    | Some (id, u) => store_c frames id (Frame (PreFrg.Operand (PreFrg.Fresh e u) true) true)
    end in
  let* is_parameter := eqb_c (Pre.ee (Pre.keys c)) e parameter in
  if is_parameter then
    let* phis := Index.find_c (Pre.eb (Pre.keys c)) b (phi_definitions index) in
    fold_left_c (install_phi_c b) phis frames
  else Cost.ret frames.

Definition instruction_c (index : prepared B BE N E U) b parameter
    (work : scope B E U * accumulator B BE E U) e :=
  let* info := Map.get_c (Pre.ee (Pre.keys c)) e (events index) in
  match info with
  | None => Cost.ret work
  | Some info =>
    let* observed := occurrence_c e (evaluation info) work in
    let* altered := fold_left_c (alter_c (evaluation info)) (alterations info) (fst observed) in
    let* frames := definitions_c index b parameter e (snd observed) (fst altered) in
    mark_exit_c index (endpoint info) (frames, snd altered)
  end.

Definition select_argument_c (frames : scope B E U) (acc : accumulator B BE E U)
    (arg : argument B BE U) :=
  let u := argument_input arg in
  let* frame := match argument_id arg with
    | None => Cost.ret (missing u)
    | Some id => top_id_c frames id u
    end in
  let* same := if available frame then
    eqb_c (Pre.eu (Pre.keys c)) (PreFrg.version_expr (PreFrg.operand_version (selected frame))) u
    else Cost.ret false in
  let operand := if same then selected frame else PreFrg.Operand (PreFrg.Unavailable u) false in
  let* links := Map.set_c (PreFrg.link_encoding c) (argument_phi arg, argument_edge arg)
    operand (link_index acc) in
  Cost.ret (Accumulator (occurrence_index acc) (fresh_index acc) links
    (unsafe_index acc) (created acc)).

Definition block_c (index : prepared B BE N E U) b frames acc :=
  Cost.step ;;
  let* points := SsaPoints.points_in_block_c (Pre.points (Pre.input c)) b in
  let* entered := match points with
    | [] => Cost.ret (frames, acc)
    | first :: _ => mark_exit_c index first (frames, acc)
    end in
  Cost.step ;;
  let* parameter := SsaPoints.parameter_edge_c (Pre.points (Pre.input c)) b in
  Cost.step ;;
  let* instructions := SsaPoints.instruction_edges_c (Pre.points (Pre.input c)) b in
  let* body := fold_left_c (instruction_c index b parameter) instructions entered in
  let* args := Index.find_c (Pre.eb (Pre.keys c)) b (arguments index) in
  let* acc := fold_left_c (fun acc pair => select_argument_c (fst body) acc (snd pair))
    args (snd body) in
  Cost.ret (fst body, acc).

Definition mark frames acc key := Cost.value (mark_c frames acc key).
Definition mark_exit index n work := Cost.value (mark_exit_c index n work).
Definition occurrence e instance work := Cost.value (occurrence_c e instance work).
Definition alter instance work key := Cost.value (alter_c instance work key).
Definition install_phi b frames pair := Cost.value (install_phi_c b frames pair).
Definition definitions index b parameter e fresh frames :=
  Cost.value (definitions_c index b parameter e fresh frames).
Definition instruction index b parameter work e :=
  Cost.value (instruction_c index b parameter work e).
Definition select_argument frames acc arg := Cost.value (select_argument_c frames acc arg).
Definition block index b frames acc := Cost.value (block_c index b frames acc).

Definition frame_reuse (frame : frame B E U) u :=
  if available frame then
    match PreFrg.operand_version (selected frame) with
    | PreFrg.Unavailable _ => false
    | d => eqb (Pre.eu (Pre.keys c)) (PreFrg.version_expr d) u
    end
  else false.

(** Dense top lookup defaults to the unavailable frame without changing the shared symbol table. *)
Theorem top_id_equation (frames : scope B E U) id {u : U} :
  top_id frames id u = Map.find_or positive_encoding (missing u) id (bindings frames).
Proof.
  reflexivity.
Qed.

(** Marking changes only the unsafe index of a phi that has no real use in the current frame. *)
Theorem mark_equation frames acc {key} :
  mark frames acc key =
    match selected (top_id frames (fst key) (snd key)) with
    | PreFrg.Operand (PreFrg.Phi b u) false =>
      Accumulator (occurrence_index acc) (fresh_index acc) (link_index acc)
        (FinSet.add (PreFrg.phi_encoding c) (b, u) (unsafe_index acc)) (created acc)
    | _ => acc
    end.
Proof.
  unfold mark, mark_c; rewrite Cost.value_bind; fold (top_id frames (fst key) (snd key)).
  destruct (top_id frames (fst key) (snd key)) as [[d real] yes].
  destruct d, real; autorewrite with galois_cost; reflexivity.
Qed.

(** Exit marking folds the eligible family only at a prepared exit or terminal point. *)
Theorem mark_exit_equation index n {work} :
  mark_exit index n work =
    if FinSet.mem (Pre.en (Pre.keys c)) n (exit_points index) then
      (fst work, fold_left (mark (fst work)) (family_ids index) (snd work))
    else work.
Proof.
  unfold mark_exit, mark_exit_c; rewrite Cost.value_bind.
  fold (FinSet.mem (Pre.en (Pre.keys c)) n (exit_points index)).
  destruct (FinSet.mem (Pre.en (Pre.keys c)) n (exit_points index));
    autorewrite with galois_cost; reflexivity.
Qed.

(** An eligible occurrence selects its available matching frame or records a fresh definition. *)
Theorem occurrence_equation {e instance work} :
  occurrence e instance work =
    match instance with
    | None => (work, None)
    | Some (id, u) =>
      let '(frames, acc) := work in
      let frame := top_id frames id u in
      let same := frame_reuse frame u in
      let d := if same then PreFrg.operand_version (selected frame) else PreFrg.Fresh e u in
      let occurrences := Map.set (Pre.ee (Pre.keys c)) e d (occurrence_index acc) in
      if same then
        ((store frames id (Frame (PreFrg.Operand d true) true),
          Accumulator occurrences (fresh_index acc) (link_index acc)
            (unsafe_index acc) (created acc)),
          None)
      else
        ((frames, Accumulator occurrences (FinSet.add (Pre.ee (Pre.keys c)) e (fresh_index acc))
          (link_index acc) (unsafe_index acc) (d :: created acc)), Some (id, u))
    end.
Proof.
  destruct instance as [[id u]|]; [|reflexivity].
  destruct work as [frames acc]; unfold occurrence, occurrence_c; rewrite Cost.value_bind.
  fold (top_id frames id u); destruct (top_id frames id u) as [[d real] yes].
  destruct yes, d; cbn [frame_reuse available selected PreFrg.operand_version PreFrg.version_expr];
    autorewrite with galois_cost; try reflexivity.
  all: match goal with
    | |- context [eqb ?enc ?x ?y] => fold (eqb enc x y); destruct (eqb enc x y)
    end; autorewrite with galois_cost; reflexivity.
Qed.

(** A killing occurrence retains definition/use provenance and clears only availability. *)
Theorem alter_equation instance {work key} :
  alter instance work key =
    let '(frames, acc) := work in
    let same := match instance with
      | None => false
      | Some current => eqb positive_encoding (fst current) (fst key)
      end in
    let acc := if same then acc else mark frames acc key in
    let frame := top_id frames (fst key) (snd key) in
    (store frames (fst key) (Frame (selected frame) false), acc).
Proof.
  destruct work as [frames acc]; unfold alter, alter_c.
  rewrite !Cost.value_bind; destruct instance as [current|];
    autorewrite with galois_cost; try reflexivity.
  fold (eqb positive_encoding (fst current) (fst key)).
  destruct (eqb positive_encoding (fst current) (fst key));
    autorewrite with galois_cost; reflexivity.
Qed.

(** Phi definitions replace the matching dense expression frame after parameter binding. *)
Theorem install_phi_equation b frames {pair} :
  install_phi b frames pair =
    store frames (fst (snd pair))
      (Frame (PreFrg.Operand (PreFrg.Phi b (snd (snd pair))) false) true).
Proof.
  reflexivity.
Qed.

(** Fresh definitions precede phi installation at the actual parameter-edge occurrence. *)
Theorem definitions_equation index b {parameter e fresh frames} :
  definitions index b parameter e fresh frames =
    let frames := match fresh with
      | None => frames
      | Some (id, u) => store frames id (Frame (PreFrg.Operand (PreFrg.Fresh e u) true) true)
      end in
    if eqb (Pre.ee (Pre.keys c)) e parameter then
      fold_left (install_phi b) (Index.find (Pre.eb (Pre.keys c)) b (phi_definitions index)) frames
    else frames.
Proof.
  unfold definitions, definitions_c; rewrite !Cost.value_bind.
  destruct fresh as [[id u]|]; autorewrite with galois_cost.
  all: fold (eqb (Pre.ee (Pre.keys c)) e parameter);
    destruct (eqb (Pre.ee (Pre.keys c)) e parameter);
    autorewrite with galois_cost; reflexivity.
Qed.

(** Each instruction performs occurrence selection, invalidation,
    definition installation and exit marking. *)
Theorem instruction_equation index b {parameter work e} :
  instruction index b parameter work e =
    match Map.get (Pre.ee (Pre.keys c)) e (events index) with
    | None => work
    | Some info =>
      let observed := occurrence e (evaluation info) work in
      let altered := fold_left (alter (evaluation info)) (alterations info) (fst observed) in
      let frames := definitions index b parameter e (snd observed) (fst altered) in
      mark_exit index (endpoint info) (frames, snd altered)
    end.
Proof.
  unfold instruction, instruction_c; rewrite Cost.value_bind.
  fold (Map.get (Pre.ee (Pre.keys c)) e (events index)).
  destruct (Map.get (Pre.ee (Pre.keys c)) e (events index)); autorewrite with galois_cost;
    reflexivity.
Qed.

(** Incoming operands use the pretranslated edge identity
    and fall back to its unavailable sentinel. *)
Theorem select_argument_equation frames acc {arg} :
  select_argument frames acc arg =
    let u := argument_input arg in
    let frame := match argument_id arg with None => missing u | Some id => top_id frames id u end in
    let same := if available frame then
      eqb (Pre.eu (Pre.keys c)) (PreFrg.version_expr (PreFrg.operand_version (selected frame))) u
      else false in
    let operand := if same then selected frame else PreFrg.Operand (PreFrg.Unavailable u) false in
    Accumulator (occurrence_index acc) (fresh_index acc)
      (Map.set (PreFrg.link_encoding c) (argument_phi arg, argument_edge arg)
        operand (link_index acc))
      (unsafe_index acc) (created acc).
Proof.
  unfold select_argument, select_argument_c; rewrite !Cost.value_bind.
  destruct (argument_id arg) as [id|]; autorewrite with galois_cost.
  - fold (top_id frames id (argument_input arg)).
    destruct (available (top_id frames id (argument_input arg)));
      autorewrite with galois_cost; reflexivity.
  - reflexivity.
Qed.

(** A block visits its ordered instruction list once
    and selects its indexed outgoing operands last. *)
Theorem block_equation index b {frames acc} :
  block index b frames acc =
    let entered := match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
      | [] => (frames, acc)
      | first :: _ => mark_exit index first (frames, acc)
      end in
    let parameter := SsaPoints.parameter_edge (Pre.points (Pre.input c)) b in
    let body := fold_left (instruction index b parameter)
      (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered in
    (fst body, fold_left (fun acc pair => select_argument (fst body) acc (snd pair))
      (Index.find (Pre.eb (Pre.keys c)) b (arguments index)) (snd body)).
Proof.
  unfold block, block_c; rewrite !Cost.value_bind.
  fold (SsaPoints.points_in_block (Pre.points (Pre.input c)) b).
  destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
    autorewrite with galois_cost; reflexivity.
Qed.

End Transfer.

Record work (B BE E U : Type) := Work {
  pending : list (positive * scope B E U);
  visited : FinSet.t positive;
  output : accumulator B BE E U
}.
Arguments Work {B BE E U}.
Arguments pending {B BE E U}.
Arguments visited {B BE E U}.
Arguments output {B BE E U}.

Record stopped (B BE E U : Type) := Stopped {
  stop_status : PreFrg.completion;
  stop_output : accumulator B BE E U
}.
Arguments Stopped {B BE E U}.
Arguments stop_status {B BE E U}.
Arguments stop_output {B BE E U}.

Section Walk.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition step_c (index : prepared B BE N E U) (current : work B BE E U)
    : Cost.t (work B BE E U + stopped B BE E U) :=
  match pending current with
  | [] => Cost.ret (inr (Stopped PreFrg.Completed (output current)))
  | (id, frames) :: rest =>
    let* seen := FinSet.mem_c positive_encoding id (visited current) in
    if seen then Cost.ret (inl (Work rest (visited current) (output current))) else
      let* name := Prepared.name_of_c (Pre.blocks c) id in
      match name with
      | None => Cost.ret (inr (Stopped PreFrg.MissingBlockName (output current)))
      | Some b =>
        let* final := block_c c index b frames (output current) in
        let* children := Index.find_c positive_encoding id (children index) in
        let* tasks := map_c (fun pair => Cost.ret (fst pair, fst final)) children in
        let* tasks := app_c tasks rest in
        let* seen := FinSet.add_c positive_encoding id (visited current) in
        Cost.ret (inl (Work tasks seen (snd final)))
      end
  end.

Definition initial_c (index : prepared B BE N E U) : Cost.t (work B BE E U) :=
  let* tasks := map_c (fun id => Cost.ret (id, entry_scope index)) (root_ids index) in
  Cost.ret (Work tasks FinSet.empty empty_accumulator).

Definition run_c (index : prepared B BE N E U) :=
  let* initial := initial_c index in
  let* result := iterate (step_c index) (walk_budget index) initial in
  Cost.ret (match result with
    | inl remaining => Stopped PreFrg.RenameExhausted (output remaining)
    | inr final => final
    end).
Definition run index := Cost.value (run_c index).
Definition step index current := Cost.value (step_c index current).
Definition initial index := Cost.value (initial_c index).

(** The dominator step reports missing names explicitly
    and gives every child the parent's final scope. *)
Theorem step_equation index current :
  step index current =
    match pending current with
    | [] => inr (Stopped PreFrg.Completed (output current))
    | (id, frames) :: rest =>
      if FinSet.mem positive_encoding id (visited current) then
        inl (Work rest (visited current) (output current))
      else match Prepared.name_of (Pre.blocks c) id with
        | None => inr (Stopped PreFrg.MissingBlockName (output current))
        | Some b =>
          let final := block c index b frames (output current) in
          inl (Work (map (fun pair => (fst pair, fst final))
              (Index.find positive_encoding id (children index)) ++ rest)
            (FinSet.add positive_encoding id (visited current)) (snd final))
        end
    end.
Proof.
  unfold step, step_c; destruct (pending current) as [|[id frames] rest]; [reflexivity|].
  rewrite Cost.value_bind; fold (FinSet.mem positive_encoding id (visited current)).
  destruct (FinSet.mem positive_encoding id (visited current)); [reflexivity|].
  rewrite Cost.value_bind; fold (Prepared.name_of (Pre.blocks c) id).
  destruct (Prepared.name_of (Pre.blocks c) id); autorewrite with galois_cost; reflexivity.
Qed.

(** Initial tasks retain ordered entry-ID occurrences and share the same prepared entry scope. *)
Theorem initial_equation index :
  initial index = Work (map (fun id => (id, entry_scope index)) (root_ids index))
    FinSet.empty empty_accumulator.
Proof.
  unfold initial, initial_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Raw exhaustion is retained separately from normal completion and missing block names. *)
Theorem run_equation index :
  run index =
    match Cost.value (iterate (step_c index) (walk_budget index) (initial index)) with
    | inl remaining => Stopped PreFrg.RenameExhausted (output remaining)
    | inr final => final
    end.
Proof.
  unfold run, run_c; rewrite !Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

(** Walk input duties concern the actual child index, naming tables and binary budget. *)
Record walk_domain (index : prepared B BE N E U) : Prop := WalkDomain {
  domain_children : children index = Index.group_by positive_encoding snd (parent_pairs index);
  domain_roots : forall id, In id (root_ids index) ->
    exists b, Prepared.name_of (Pre.blocks c) id = Some b;
  domain_child_names : forall child parent, In (child, parent) (parent_pairs index) ->
    exists b, Prepared.name_of (Pre.blocks c) child = Some b;
  domain_budget : length (root_ids index) + length (parent_pairs index) <
    Pos.to_nat (walk_budget index)
}.

(** Preparation proves walk duties from the supplied exact tree
    without assuming any output result. *)
Theorem prepare_walk_domain data :
  Pre.laws c -> walk_domain (prepare c data).
Proof.
  intro Hlaw; destruct (prepare_walk_equations c data) as [Hroots [Hparents [Hchildren Hbudget]]].
  pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
  constructor.
  - rewrite Hparents; exact Hchildren.
  - intros id Hid; rewrite Hroots in Hid.
    apply (Prepared.entry_ids_spec _ _ Hp) in Hid; destruct Hid as [b [_ Hb]].
    exists b; exact (Prepared.name_of_id_of _ _ _ Hp Hb).
  - intros child parent Hin; rewrite Hparents in Hin.
    apply (Map.elements_spec positive_encoding positive_encoding_laws) in Hin.
    + destruct (Dom.idom_domain _ _ (Pre.tree_exact c (Pre.graphs c Hlaw))
        child parent Hin) as [b [owner [Hb Hrest]]]; exists b; exact Hb.
    + exact (proj1 (Dom.maps_wf _ _ (Pre.tree_exact c (Pre.graphs c Hlaw)))).
  - rewrite Hroots, Hparents, Hbudget.
    remember (N.of_nat (length (Prepared.entry_ids (Pre.blocks c))) +
      N.of_nat (length (Map.elements (Dom.idom (Pre.dom c)))))%N as count.
    assert (Hpositive : Pos.to_nat (N.succ_pos count) = S (N.to_nat count)).
    { destruct count as [|p]; [reflexivity|]; cbn; rewrite Pos2Nat.inj_succ; reflexivity. }
    rewrite Hpositive, Heqcount, N2Nat.inj_add, !Nat2N.id; lia.
Qed.

Fixpoint parent_credit (parents : list (positive * positive)) (seen : FinSet.t positive) :=
  match parents with
  | [] => 0
  | (_, parent) :: rest =>
    if FinSet.mem positive_encoding parent seen then parent_credit rest seen
    else S (parent_credit rest seen)
  end.

Definition walk_measure (index : prepared B BE N E U) (current : work B BE E U) :=
  length (pending current) + parent_credit (parent_pairs index) (visited current).

Local Lemma parent_credit_empty parents :
  parent_credit parents FinSet.empty = length parents.
Proof.
  induction parents as [|[child parent] rest IH]; [reflexivity|].
  cbn [parent_credit length]; rewrite FinSet.mem_empty, IH; reflexivity.
Qed.

Local Lemma parent_credit_spent {parents seen id} :
  FinSet.wf positive_encoding seen -> FinSet.mem positive_encoding id seen = false ->
  parent_credit parents (FinSet.add positive_encoding id seen) +
    length (Index.find positive_encoding id (Index.group_by positive_encoding snd parents)) =
      parent_credit parents seen.
Proof.
  intros Hwf Hfresh; rewrite Index.find_group_by.
  induction parents as [|[child parent] rest IH]; [reflexivity|].
  cbn [parent_credit filter snd].
  rewrite FinSet.mem_add by exact Hwf.
  destruct (eqb positive_encoding parent id) eqn:Hsame.
  - apply (eqb_true_iff _ positive_encoding_laws) in Hsame; subst parent.
    rewrite Hfresh; cbn [orb length]; lia.
  - destruct (FinSet.mem positive_encoding parent seen); cbn [orb length]; lia.
Qed.

Local Lemma initial_measure index :
  walk_measure index (initial index) = length (root_ids index) + length (parent_pairs index).
Proof.
  rewrite initial_equation; unfold walk_measure; cbn [pending visited].
  rewrite length_map, parent_credit_empty; reflexivity.
Qed.

Local Lemma step_visited_wf {index current next} :
  FinSet.wf positive_encoding (visited current) ->
  step index current = inl next -> FinSet.wf positive_encoding (visited next).
Proof.
  intros Hwf Hstep; rewrite step_equation in Hstep.
  destruct (pending current) as [|[id frames] rest]; [discriminate|].
  destruct (FinSet.mem positive_encoding id (visited current));
    [inversion Hstep; subst next; exact Hwf|].
  destruct (Prepared.name_of (Pre.blocks c) id); [|discriminate].
  inversion Hstep; subst next; apply FinSet.wf_add; exact Hwf.
Qed.

Local Lemma step_measure {index current next} :
  walk_domain index -> FinSet.wf positive_encoding (visited current) ->
  step index current = inl next -> walk_measure index next < walk_measure index current.
Proof.
  intros Hdomain Hwf Hstep; rewrite step_equation in Hstep.
  destruct (pending current) as [|[id frames] rest] eqn:Hpending; [discriminate|].
  destruct (FinSet.mem positive_encoding id (visited current)) eqn:Hseen.
  - inversion Hstep; subst next; unfold walk_measure; rewrite Hpending.
    cbn [pending visited length]; lia.
  - destruct (Prepared.name_of (Pre.blocks c) id); [|discriminate].
    inversion Hstep; subst next; unfold walk_measure; rewrite Hpending.
    cbn [pending visited length]; rewrite length_app, length_map.
    rewrite (domain_children index Hdomain).
    pose proof (parent_credit_spent (parents := parent_pairs index) Hwf Hseen); lia.
Qed.

Local Lemma runs_exhaustion {index budget current final} :
  walk_domain index -> FinSet.wf positive_encoding (visited current) ->
  runs (step_c index) budget current (inl final) ->
  walk_measure index final + budget <= walk_measure index current.
Proof.
  intros Hdomain Hwf Hrun; remember (inl final) as result eqn:Hresult.
  revert final Hwf Hresult.
  induction Hrun as [current|budget current halted Hstop|
    budget current next result Hstep Hrun IH]; intros final Hwf Hresult.
  - inversion Hresult; subst; lia.
  - discriminate.
  - fold (step index current) in Hstep.
    specialize (IH final (step_visited_wf Hwf Hstep) Hresult).
    pose proof (step_measure Hdomain Hwf Hstep); lia.
Qed.

Definition tasks_named (current : work B BE E U) : Prop :=
  forall id frames, In (id, frames) (pending current) ->
    exists b, Prepared.name_of (Pre.blocks c) id = Some b.

Local Lemma step_named {index current next} :
  walk_domain index -> tasks_named current -> step index current = inl next -> tasks_named next.
Proof.
  intros Hdomain Hnamed Hstep; rewrite step_equation in Hstep.
  destruct (pending current) as [|[id frames] rest] eqn:Hpending; [discriminate|].
  destruct (FinSet.mem positive_encoding id (visited current)).
  - inversion Hstep; subst next; intros child scope Hin; apply (Hnamed child scope).
    rewrite Hpending; now right.
  - destruct (Prepared.name_of (Pre.blocks c) id); [|discriminate].
    inversion Hstep; subst next; intros child scope Hin.
    cbn [pending] in Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + apply in_map_iff in Hin; destruct Hin as [[key parent] [Heq Hchild]].
      inversion Heq; subst key scope.
      rewrite (domain_children index Hdomain), Index.find_group_by in Hchild.
      apply filter_In in Hchild; apply (domain_child_names index Hdomain child parent).
      exact (proj1 Hchild).
    + apply (Hnamed child scope); rewrite Hpending; now right.
Qed.

Local Lemma initial_named index :
  walk_domain index -> tasks_named (initial index).
Proof.
  intros Hdomain id frames Hin; rewrite initial_equation in Hin; cbn [pending] in Hin.
  apply in_map_iff in Hin; destruct Hin as [root [Heq Hroot]]; inversion Heq; subst root.
  apply (domain_roots index Hdomain); exact Hroot.
Qed.

Local Lemma runs_named {index budget current result} :
  walk_domain index -> tasks_named current -> runs (step_c index) budget current result ->
  match result with inl next => tasks_named next | inr _ => True end.
Proof.
  intros Hdomain Hnamed Hrun; revert Hnamed.
  induction Hrun as [current|budget current final Hstop|
    budget current next result Hstep Hrun IH]; intro Hnamed; [exact Hnamed|exact I|].
  apply IH; eapply step_named; [exact Hdomain|exact Hnamed|exact Hstep].
Qed.

Local Lemma terminal_completed {index current final} :
  tasks_named current -> step index current = inr final -> stop_status final = PreFrg.Completed.
Proof.
  intros Hnamed Hstop; rewrite step_equation in Hstop.
  destruct (pending current) as [|[id frames] rest] eqn:Hpending.
  - inversion Hstop; reflexivity.
  - destruct (FinSet.mem positive_encoding id (visited current)); [discriminate|].
    destruct (Hnamed id frames) as [b Hb]; [rewrite Hpending; now left|].
    rewrite Hb in Hstop; discriminate.
Qed.

(** The actual scoped walk completes before its prepared budget
    and never loses a valid block name. *)
Theorem run_completed index :
  walk_domain index -> stop_status (run index) = PreFrg.Completed.
Proof.
  intro Hdomain.
  pose proof (iterate_value (step_c index) (walk_budget index) (initial index)) as Hrun.
  rewrite run_equation.
  destruct (Cost.value (iterate (step_c index) (walk_budget index) (initial index)))
    as [remaining|final] eqn:Hresult.
  - assert (Hwf : FinSet.wf positive_encoding (visited (initial index))).
    { rewrite initial_equation; apply FinSet.wf_empty. }
    pose proof (runs_exhaustion Hdomain Hwf Hrun) as Hbound.
    rewrite initial_measure in Hbound; pose proof (domain_budget index Hdomain); exfalso; lia.
  - destruct (runs_inr_stop (step_c index) _ _ _ Hrun)
      as [used [last [_ [Hprefix Hstop]]]].
    apply (terminal_completed (index := index) (current := last)).
    + exact (runs_named Hdomain (initial_named index Hdomain) Hprefix).
    + exact Hstop.
Qed.

End Walk.

End PreRename.
