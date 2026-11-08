(** * Ordered paths and nearest expression definitions

    Point paths project to block paths without losing parallel incoming edge identities.
    For example, internal instruction edges disappear and each crossing edge stays in order.
    Builds on: AnalysesSsaPreFrg and ProgramSsaPoints. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseMap.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg.
Import List.ListNotations Cost.Notations.

Module PreRename.

(** Invalid frames retain their nearest definition and accumulated real-use provenance. *)
Record frame (B E U : Type) := Frame {
  selected : PreFrg.operand B E U;
  available : bool
}.
Arguments Frame {B E U}.
Arguments selected {B E U}.
Arguments available {B E U}.

Definition scope B E U := Map.t U (frame B E U).

Section Paths.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Let s := Pre.points (Pre.input c).

Definition missing (u : U) : frame B E U :=
  Frame (PreFrg.Operand (PreFrg.Unavailable u) false) false.
Definition top_c (frames : scope B E U) u :=
  Map.find_or_c (Pre.eu (Pre.keys c)) (missing u) u frames.
Definition top frames u := Cost.value (top_c frames u).

(** Missing scope bindings denote unavailable versions of the very same expression. *)
Theorem top_equation frames u :
  top frames u =
    match Map.get (Pre.eu (Pre.keys c)) u frames with
    | None => missing u
    | Some frame => frame
    end.
Proof.
  unfold top, top_c; fold (Map.find_or (Pre.eu (Pre.keys c)) (missing u) u frames).
  apply Map.find_or_equation.
Qed.

Definition initial_frame_c u : Cost.t (frame B E U) :=
  Cost.step ;;
  let* yes := Pre.initial_c (Pre.input c) u in
  Cost.ret (Frame
    (PreFrg.Operand (if yes then PreFrg.Initial u else PreFrg.Unavailable u) false) yes).

Definition initial_scope_c family :=
  let* pairs := map_c (fun u =>
    let* frame := initial_frame_c u in Cost.ret (u, frame)) family in
  Map.of_list_c (Pre.eu (Pre.keys c)) pairs.
Definition initial_scope family := Cost.value (initial_scope_c family).

(** Initial scopes materialize the supplied family once and retain every initial callback charge. *)
Theorem initial_scope_equation family :
  initial_scope family = Map.of_list (Pre.eu (Pre.keys c))
    (map (fun u => (u, Frame
      (PreFrg.Operand (if Pre.initial c u then PreFrg.Initial u else PreFrg.Unavailable u)
        false) (Pre.initial c u))) family).
Proof.
  unfold initial_scope, initial_scope_c; rewrite Cost.value_bind, value_map_c.
  assert (Hpairs : map
    (fun u => Cost.value (let* frame := initial_frame_c u in Cost.ret (u, frame))) family =
    map (fun u => (u, Frame
      (PreFrg.Operand (if Pre.initial c u then PreFrg.Initial u else PreFrg.Unavailable u)
        false) (Pre.initial c u))) family).
  { apply map_ext; intro u; unfold initial_frame_c.
    autorewrite with galois_cost; reflexivity. }
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

End PreRename.
