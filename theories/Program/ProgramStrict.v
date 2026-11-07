(** * Strict SSA and guard transport

    Strict SSA preserves bindings away from their definition homes.
    For example, an operand guarded by an edge retains its value at a dominated read.
    Builds on: ProgramRuns, ProgramSsa and GraphFrontierSpec. *)

From Stdlib Require Import List Bool Arith Lia Wf_nat PArith.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFrontierSpec
  GraphReach GraphCheckDom.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink
  ProgramRuns ProgramSsa ProgramEdgeProjection.
Import List.ListNotations Cost.Notations.

(** Strict SSA retains all six legacy clauses and quantifies guard homes over every operand. *)
Record strict_ssa_laws {S O N E V K G C} (m : semantics S O) (p : Ssa.t N E V K G)
    (sl : SsaLink.t S O N E V C) : Prop := {
  redefine_in_stay : forall x, on_steps m (fun s l s' =>
    Link.stays (SsaLink.link sl) s l s' ->
    SsaLink.val sl s' x <> SsaLink.val sl s x ->
    Link.point (SsaLink.link sl) s = Ssa.home p x);
  redefine_on_edge : forall e x, on_steps m (fun s l s' =>
    Link.taken (SsaLink.link sl) s l s' e ->
    SsaLink.val sl s' x <> SsaLink.val sl s x ->
    Ssa.home p x = Link.point (SsaLink.link sl) s');
  frame_in_stay : forall x, on_steps m (fun s l s' =>
    Link.stays (SsaLink.link sl) s l s' ->
    Link.point (SsaLink.link sl) s <> Ssa.home p x ->
    SsaLink.val sl s' x = SsaLink.val sl s x);
  frame_on_edge : forall e x, on_steps m (fun s l s' =>
    Link.taken (SsaLink.link sl) s l s' e ->
    Ssa.home p x <> Link.point (SsaLink.link sl) s' ->
    SsaLink.val sl s' x = SsaLink.val sl s x);
  guard_home : forall e g ys x, In e (Cfg.edges (Ssa.cfg p)) ->
    In (g, ys) (Ssa.guards p e) -> In x ys ->
    dominates (Cfg.graph (Ssa.cfg p)) (Ssa.home p x)
      (Graph.source (Cfg.graph (Ssa.cfg p)) e);
  op_args_dominate : forall x o args y, Ssa.def p x = Op o args -> In y args ->
    dominates (Cfg.graph (Ssa.cfg p)) (Ssa.home p y) (Ssa.home p x)
}.
Arguments redefine_in_stay {S O N E V K G C m p sl}.
Arguments redefine_on_edge {S O N E V K G C m p sl}.
Arguments frame_in_stay {S O N E V K G C m p sl}.
Arguments frame_on_edge {S O N E V K G C m p sl}.
Arguments guard_home {S O N E V K G C m p sl}.
Arguments op_args_dominate {S O N E V K G C m p sl}.

Local Lemma listed_nodes_eq {A} (xs : list A) : NoDup xs ->
  forall x y, In x xs -> In y xs -> x = y \/ x <> y.
Proof.
  intro Hdistinct; induction Hdistinct as [|a xs Hfresh Hdistinct IH];
    intros x y Hx Hy; [contradiction|].
  destruct Hx as [Hx|Hx], Hy as [Hy|Hy].
  - left; congruence.
  - right; intro Heq; subst; contradiction.
  - right; intro Heq; subst; contradiction.
  - apply IH; assumption.
Qed.

Local Lemma edge_path_prefix {N E} (g : Graph.t N E) s es n e :
  path g s es n -> In e es ->
  exists pre, path g s pre (Graph.source g e) /\ length pre < length es.
Proof.
  intro Hpath; induction Hpath as [v|a es n Hedge Hpath IH]; intro Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists []; split; [constructor|cbn; lia].
    + destruct (IH Hin) as [pre [Hpre Hlength]].
      exists (a :: pre); split; [constructor; assumption|cbn; lia].
Qed.

Local Lemma prefix_target {N E} (g : Graph.t N E) s es n e :
  path g s es n -> In e es ->
  exists pre, path g s pre (Graph.target g e) /\ incl pre es.
Proof.
  intro Hpath; induction Hpath as [v|a es n Hedge Hpath IH]; intro Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists [a]; split; [constructor; [exact Hedge|constructor]|].
      intros b [<-|Hbad]; [left; reflexivity|contradiction].
    + destruct (IH Hin) as [pre [Hpre Hsub]].
      exists (a :: pre); split; [constructor; assumption|].
      intros b [<-|Hinb]; [left; reflexivity|right; apply Hsub; exact Hinb].
Qed.

Local Lemma graph_path_app {N E} (g : Graph.t N E) s u t es fs :
  path g s es u -> path g u fs t -> path g s (es ++ fs) t.
Proof.
  intro Hpath; induction Hpath as [s|e es u Hedge Hpath IH]; intro Htail.
  - exact Htail.
  - cbn; constructor; [exact Hedge|apply IH; exact Htail].
Qed.

(** Dominance of a reachable node implies reachability of the edge's source. *)
Theorem dominated_edge_source_reachable {N E} (g : Graph.t N E) e n :
  reachable g n -> edge_dominates g e n -> reachable g (Graph.source g e).
Proof.
  intros Hreach Hdom; apply reachable_iff_path in Hreach.
  destruct Hreach as [s [es [Hentry Hpath]]].
  destruct (edge_path_prefix g s es n e Hpath (Hdom s es Hentry Hpath)) as [pre [Hpre _]].
  apply reachable_iff_path; exists s, pre; split; assumption.
Qed.

Local Lemma dominated_suffix_contains {N E} (g : Graph.t N E) e d n fs :
  reachable g (Graph.source g e) -> dominates g d (Graph.source g e) ->
  edge_dominates g e n -> path g d fs n -> In e fs.
Proof.
  intros Hreach Hhome Hdom Hsuffix.
  apply reachable_iff_path in Hreach; destruct Hreach as [s [es [Hentry Hpath]]].
  remember (length es) as k eqn:Hlength; revert es Hpath Hlength.
  induction k as [k IH] using lt_wf_ind; intros es Hpath Hlength.
  destruct (Hhome s es Hentry Hpath) as [Hstart|[a [Hin Htarget]]].
  - subst d; exact (Hdom s fs Hentry Hsuffix).
  - destruct (prefix_target g s es (Graph.source g e) a Hpath Hin) as [pre [Hpre Hsub]].
    rewrite Htarget in Hpre.
    pose proof (Hdom s (pre ++ fs) Hentry (graph_path_app g _ _ _ _ _ Hpre Hsuffix))
      as Hinfull.
    apply in_app_or in Hinfull; destruct Hinfull as [Hinpre|Hinfs]; [|exact Hinfs].
    assert (Hines : In e es) by (apply Hsub; exact Hinpre).
    destruct (edge_path_prefix g s es (Graph.source g e) e Hpath Hines)
      as [short [Hshort Hsmaller]].
    eapply (IH (length short)); [lia|exact Hshort|reflexivity].
Qed.

(** An edge cannot dominate its reachable source. *)
Theorem edge_source_not_dominated {N E} (g : Graph.t N E) e :
  reachable g (Graph.source g e) -> ~ edge_dominates g e (Graph.source g e).
Proof.
  intros Hreach Hdom.
  pose proof (dominated_suffix_contains g e (Graph.source g e) (Graph.source g e) []
    Hreach (dominates_refl g _) Hdom (path_nil _)) as Hfalse; contradiction.
Qed.

Local Lemma exec_in_start {S O} (m : semantics S O) (P : S -> Prop) s tr t :
  exec_in m P s tr t -> P s.
Proof.
  intro Hrun; destruct Hrun; assumption.
Qed.

Section LinkedRuns.

Context {S O N E : Type} (m : semantics S O) (c : Cfg.t N E)
  (lk : Link.t S O N E) (Hlink : link_laws m (Cfg.graph c) lk).

Local Lemma exec_in_edge_free e s tr t :
  reachable_state m s ->
  exec_in m (fun u => Link.point lk u <> Graph.source (Cfg.graph c) e) s tr t ->
  exists es, path (Cfg.graph c) (Link.point lk s) es (Link.point lk t) /\ ~ In e es.
Proof.
  intros Hreach Hrun; revert Hreach.
  induction Hrun as [s Haway|s l s' tr t Haway Hstep Hrun IH]; intro Hreach.
  - exists []; split; [constructor|intro Hin; contradiction].
  - destruct (IH (reachable_state_step m s l s' Hreach Hstep)) as [es [Hpath Hfree]].
    destruct (edge_covers Hlink s l s' Hreach Hstep) as [Hstay|[a Htaken]].
    + exists es; split; [|exact Hfree].
      rewrite <- (stays_point Hlink s l s' Hreach Hstep Hstay); exact Hpath.
    + destruct (link_taken_edge m c lk s l s' a Hlink Hreach Hstep Htaken)
        as [_ [Hsource Htarget]].
      exists (a :: es); split.
      * rewrite <- Hsource; constructor.
        -- rewrite Hsource; exact (proj1 (taken_edge Hlink a s l s' Hreach Hstep Htaken)).
        -- rewrite Htarget; exact Hpath.
      * intros [Heq|Hin]; [subst a; apply Haway; symmetry; exact Hsource|exact (Hfree Hin)].
Qed.

Local Lemma exec_last_point d s tr t :
  In d (Graph.nodes (Cfg.graph c)) -> reachable_state m s -> exec m s tr t ->
  exec_in m (fun u => Link.point lk u <> d) s tr t \/ Link.point lk t = d \/
  exists u l v tail, reachable_state m u /\ Link.point lk u = d /\ step m u l v /\
    exec_in m (fun w => Link.point lk w <> d) v tail t.
Proof.
  intros Hd Hreach Hrun; revert Hreach.
  induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intro Hreach.
  - destruct (listed_nodes_eq _ (nodes_nodup (cfg_wf Hlink)) (Link.point lk s) d
      (reachable_point_in_nodes m _ lk s Hlink Hreach) Hd) as [Heq|Hneq].
    + right; left; exact Heq.
    + left; constructor; exact Hneq.
  - destruct (IH (reachable_state_step m s l s' Hreach Hstep)) as [Haway|Hlast].
    + destruct (listed_nodes_eq _ (nodes_nodup (cfg_wf Hlink)) (Link.point lk s) d
        (reachable_point_in_nodes m _ lk s Hlink Hreach) Hd) as [Heq|Hneq].
      * right; right; exists s, l, s', tr; repeat split; assumption.
      * left; econstructor; eassumption.
    + right; exact Hlast.
Qed.

Local Lemma exec_in_away_home e d s tr t :
  reachable (Cfg.graph c) (Graph.source (Cfg.graph c) e) ->
  dominates (Cfg.graph c) d (Graph.source (Cfg.graph c) e) ->
  edge_dominates (Cfg.graph c) e (Link.point lk t) -> reachable_state m s ->
  exec_in m (fun u => Link.point lk u <> Graph.source (Cfg.graph c) e) s tr t ->
  exec_in m (fun u => Link.point lk u <> d) s tr t.
Proof.
  intros Hsource Hhome Hdom Hreach Hrun; revert Hreach Hdom.
  induction Hrun as [s Haway|s l s' tr t Haway Hstep Hrun IH]; intros Hreach Hdom.
  - constructor; intro Heq.
    pose proof (dominated_suffix_contains (Cfg.graph c) e d (Link.point lk s) []
      Hsource Hhome Hdom) as Hcontains.
    rewrite Heq in Hcontains; specialize (Hcontains (path_nil d)); contradiction.
  - assert (Hcurrent : Link.point lk s <> d).
    { intro Heq.
      destruct (exec_in_edge_free e s (l ++ tr) t Hreach
        (exec_in_step s l s' tr t Haway Hstep Hrun)) as [es [Hpath Hfree]].
      rewrite Heq in Hpath; apply Hfree; eapply dominated_suffix_contains; eassumption. }
    econstructor; [exact Hcurrent|exact Hstep|].
    apply IH; [eapply reachable_state_step; eassumption|exact Hdom].
Qed.

Local Lemma last_edge_departure s e u l v tail :
  edge_dominates (Cfg.graph c) e (Link.point lk s) ->
  reachable (Cfg.graph c) (Graph.source (Cfg.graph c) e) ->
  reachable_state m u -> Link.point lk u = Graph.source (Cfg.graph c) e ->
  step m u l v ->
  exec_in m (fun w => Link.point lk w <> Graph.source (Cfg.graph c) e) v tail s ->
  Link.taken lk u l v e.
Proof.
  intros Hdom Hsource Hu Hpoint Hstep Htail.
  assert (Hv : reachable_state m v) by (eapply reachable_state_step; eassumption).
  pose proof (exec_in_start m _ v tail s Htail) as Hvaway.
  destruct (edge_covers Hlink u l v Hu Hstep) as [Hstay|[a Htaken]].
  - exfalso; apply Hvaway; rewrite (stays_point Hlink u l v Hu Hstep Hstay); exact Hpoint.
  - destruct (link_taken_edge m c lk u l v a Hlink Hu Hstep Htaken)
      as [_ [Hasource Hatarget]].
    destruct (exec_in_edge_free e v tail s Hv Htail) as [es [Hpath Hfree]].
    assert (Hfull : path (Cfg.graph c) (Graph.source (Cfg.graph c) e)
      (a :: es) (Link.point lk s)).
    { rewrite <- Hpoint, <- Hasource; constructor.
      - rewrite Hasource; exact (proj1 (taken_edge Hlink a u l v Hu Hstep Htaken)).
      - rewrite Hatarget; exact Hpath. }
    destruct (dominated_suffix_contains (Cfg.graph c) e (Graph.source (Cfg.graph c) e)
      (Link.point lk s) (a :: es) Hsource (dominates_refl _ _) Hdom Hfull) as [Heq|Hin].
    + subst a; exact Htaken.
    + exfalso; exact (Hfree Hin).
Qed.

(** A reachable dominated read has a last matching edge followed by source-avoiding states. *)
Theorem last_dominating_edge s e :
  reachable_state m s -> edge_dominates (Cfg.graph c) e (Link.point lk s) ->
  exists u l v tail, reachable_state m u /\ step m u l v /\ Link.taken lk u l v e /\
    exec_in m (fun w => Link.point lk w <> Graph.source (Cfg.graph c) e) v tail s.
Proof.
  intros Hreach Hdom.
  assert (Hsource : reachable (Cfg.graph c) (Graph.source (Cfg.graph c) e)).
  { eapply dominated_edge_source_reachable; [eapply reachable_point; eassumption|exact Hdom]. }
  destruct Hreach as [s0 [tr [Hinitial Hrun]]].
  assert (Hstart : reachable_state m s0).
  { exists s0, []; split; [exact Hinitial|constructor]. }
  destruct (exec_last_point (Graph.source (Cfg.graph c) e) s0 tr s
    (reachable_in_nodes _ _ (cfg_wf Hlink) Hsource) Hstart Hrun)
    as [Haway|[Hend|[u [l [v [tail [Hu [Hpoint [Hstep Htail]]]]]]]]].
  - destruct (exec_in_edge_free e s0 tr s Hstart Haway) as [es [Hpath Hfree]].
    exfalso; apply Hfree; apply Hdom with (Link.point lk s0).
    + apply (entry_points Hlink); exact Hinitial.
    + exact Hpath.
  - exfalso; apply (edge_source_not_dominated (Cfg.graph c) e Hsource).
    rewrite <- Hend; exact Hdom.
  - exists u, l, v, tail; split; [exact Hu|]; split; [exact Hstep|].
    split; [eapply last_edge_departure; eassumption|exact Htail].
Qed.

End LinkedRuns.

Section Bindings.

Context {S O N E V K G C : Type} (m : semantics S O) (p : Ssa.t N E V K G)
  (sl : SsaLink.t S O N E V C) (eval : K -> list C -> option C)
  (holds : G -> list C -> Prop) (Hssa : ssa_laws m p sl eval holds)
  (Hstrict : strict_ssa_laws m p sl).

Local Lemma exec_frame_away x s tr t :
  reachable_state m s ->
  exec_in m (fun u => Link.point (SsaLink.link sl) u <> Ssa.home p x) s tr t ->
  SsaLink.val sl t x = SsaLink.val sl s x.
Proof.
  intros Hreach Hrun; revert Hreach.
  induction Hrun as [s Haway|s l s' tr t Haway Hstep Hrun IH]; intro Hreach.
  - reflexivity.
  - rewrite (IH (reachable_state_step m s l s' Hreach Hstep)).
    destruct (edge_covers (link_ok Hssa) s l s' Hreach Hstep) as [Hstay|[a Htaken]].
    + eapply frame_in_stay; eassumption.
    + eapply frame_on_edge; try eassumption.
      pose proof (exec_in_start m _ s' tr t Hrun) as Htarget; congruence.
Qed.

Local Lemma dominated_value_preserved e x u l v tail s :
  reachable_state m u -> step m u l v -> Link.taken (SsaLink.link sl) u l v e ->
  exec_in m
    (fun w => Link.point (SsaLink.link sl) w <> Graph.source (Cfg.graph (Ssa.cfg p)) e)
    v tail s ->
  edge_dominates (Cfg.graph (Ssa.cfg p)) e (Link.point (SsaLink.link sl) s) ->
  dominates (Cfg.graph (Ssa.cfg p)) (Ssa.home p x) (Graph.source (Cfg.graph (Ssa.cfg p)) e) ->
  SsaLink.val sl s x = SsaLink.val sl u x.
Proof.
  intros Hu Hstep Htaken Htail Hdom Hhome.
  assert (Hv : reachable_state m v) by (eapply reachable_state_step; eassumption).
  destruct (link_taken_edge m (Ssa.cfg p) (SsaLink.link sl) u l v e
    (link_ok Hssa) Hu Hstep Htaken) as [_ [Hsource _]].
  assert (Hreachable : reachable (Cfg.graph (Ssa.cfg p))
    (Graph.source (Cfg.graph (Ssa.cfg p)) e)).
  { rewrite Hsource; eapply reachable_point; [exact (link_ok Hssa)|exact Hu]. }
  pose proof (exec_in_away_home m (Ssa.cfg p) (SsaLink.link sl) (link_ok Hssa)
    e (Ssa.home p x) v tail s Hreachable Hhome Hdom Hv Htail) as Haway.
  rewrite (exec_frame_away x v tail s Hv Haway).
  eapply frame_on_edge; try eassumption.
  pose proof (exec_in_start m _ v tail s Haway); congruence.
Qed.

Local Lemma operand_values_preserved s t args cs :
  Forall2 (fun y d => SsaLink.val sl s y = Some d) args cs ->
  (forall y, In y args -> SsaLink.val sl t y = SsaLink.val sl s y) ->
  Forall2 (fun y d => SsaLink.val sl t y = Some d) args cs.
Proof.
  intro Hargs; induction Hargs as [|y d args cs Hvalue Hargs IH]; intro Hpreserve.
  - constructor.
  - constructor.
    + rewrite Hpreserve; [exact Hvalue|left; reflexivity].
    + apply IH; intros z Hin; apply Hpreserve; right; exact Hin.
Qed.

(** Every dominating edge's guards and operand equations hold at a reachable dominated read. *)
Theorem dominated_guard_holds s e :
  reachable_state m s ->
  edge_dominates (Cfg.graph (Ssa.cfg p)) e (Link.point (SsaLink.link sl) s) ->
  (forall g ys, In (g, ys) (Ssa.guards p e) ->
    exists cs, Forall2 (fun y c => SsaLink.val sl s y = Some c) ys cs /\ holds g cs) /\
  guard_ops_consistent p sl eval s e.
Proof.
  intros Hreach Hdom.
  destruct (last_dominating_edge m (Ssa.cfg p) (SsaLink.link sl) (link_ok Hssa)
    s e Hreach Hdom) as [u [l [v [tail [Hu [Hstep [Htaken Htail]]]]]]].
  pose proof (proj1 (link_taken_edge m (Ssa.cfg p) (SsaLink.link sl)
    u l v e (link_ok Hssa) Hu Hstep Htaken)) as Hedge.
  assert (Hpreserve : forall x,
    dominates (Cfg.graph (Ssa.cfg p)) (Ssa.home p x)
      (Graph.source (Cfg.graph (Ssa.cfg p)) e) ->
    SsaLink.val sl s x = SsaLink.val sl u x).
  { intros x Hhome; eapply dominated_value_preserved; eassumption. }
  split.
  - intros g ys Hguard.
    destruct (guards_hold Hssa e u l v Hu Hstep Htaken g ys Hguard) as [cs [Hargs Hholds]].
    exists cs; split; [|exact Hholds].
    eapply operand_values_preserved; [exact Hargs|].
    intros x Hin; apply Hpreserve; eapply guard_home; eassumption.
  - intros g ys x o args Hguard Hin Hdef.
    destruct (guard_op_defined Hssa e u l v Hu Hstep Htaken g ys x o args Hguard Hin Hdef)
      as [cs [c [Hargs [Hvalue Heval]]]].
    exists cs, c; split.
    + eapply operand_values_preserved; [exact Hargs|].
      intros y Hy; apply Hpreserve.
      eapply dominates_trans.
      * eapply op_args_dominate; eassumption.
      * eapply guard_home; eassumption.
    + split; [rewrite Hpreserve; [exact Hvalue|eapply guard_home; eassumption]|exact Heval].
Qed.

End Bindings.

(** * Prepared edge-dominance queries *)

(** Reachable incoming edges whose source is not dominated by their target are candidates. *)
Definition edge_candidates {N E} (p : Prepared.t N E) (t : Dom.tree)
    (live : FinSet.t positive) v :=
  filter (fun ei => FinSet.mem positive_encoding (snd ei) live &&
    negb (DomCheck.dominates_b t v (snd ei))) (Prepared.pred_edges p v).

(** A non-entry target has an indexed edge exactly when its candidate list is a singleton. *)
Definition edge_choice {N E} (p : Prepared.t N E) t live v : option E :=
  if existsb (Pos.eqb v) (Prepared.entry_ids p) then None else
  match edge_candidates p t live v with
  | [(e, _)] => Some e
  | _ => None
  end.

(** Contexts retain the supplied prepared graph and tree and materialise edge choices once. *)
Record dom_context (N E : Type) := DomContext {
  dc_prepared : Prepared.t N E;
  dc_tree : Dom.tree;
  dc_index : Map.t positive (option E);
  dc_fuel : positive
}.
Arguments DomContext {N E}.
Arguments dc_prepared {N E}.
Arguments dc_tree {N E}.
Arguments dc_index {N E}.
Arguments dc_fuel {N E}.

(** Reference preparation consumes a candidate tree without a producer or semantic argument. *)
Definition make_dom_context {N E} (p : Prepared.t N E) (t : Dom.tree) : dom_context N E :=
  let live := Reach.set p Reach.unrestricted (Prepared.entry_ids p) in
  DomContext p t (Map.of_list positive_encoding
    (map (fun v => (v, edge_choice p t live v)) (Reach.universe p)))
    (Pos.of_succ_nat (Map.size (Dom.idom t))).

(** Each hot query step uses charged map lookups and stops at an absent parent. *)
Definition dom_walk_step_c {N E} (ctx : dom_context N E)
    (state : option positive * list E) : Cost.t ((option positive * list E) + list E) :=
  match state with
  | (None, es) => Cost.ret (inr es)
  | (Some v, es) =>
    let* parent := Map.get_c positive_encoding v (Dom.idom (dc_tree ctx)) in
    let* selected := Map.get_c positive_encoding v (dc_index ctx) in
    Cost.ret (inl (parent, match selected with Some (Some e) => e :: es | _ => es end))
  end.

(** A query follows the retained parent chain and returns collected edges in ancestor order. *)
Definition dominating_edges_in_c {N E} (ctx : dom_context N E) (n : N) :=
  let* start := Prepared.id_of_c (dc_prepared ctx) n in
  let* result := iterate (dom_walk_step_c ctx) (dc_fuel ctx) (start, []) in
  Cost.ret (match result with inl (_, es) | inr es => es end).

Definition dominating_edges_in {N E} (ctx : dom_context N E) n :=
  Cost.value (dominating_edges_in_c ctx n).

Local Lemma first_arrival_aux {N E} (enc : encoding N) (HE : encoding_laws enc)
    (g : Graph.t N E) v s pre u es :
  path g s pre u -> In s (Graph.entries g) -> v <> s ->
  (forall a, In a pre -> Graph.target g a <> v) -> v <> u -> path g u es v ->
  exists e, In e es /\ In e (Graph.out g (Graph.source g e)) /\
    Graph.target g e = v /\ reachable g (Graph.source g e) /\
    ~ dominates g v (Graph.source g e).
Proof.
  intros Hpre Hentry Hstart Hfree Hcurrent Hpath.
  remember v as dest eqn:Hdest in Hpath.
  revert s pre Hpre Hentry Hstart Hfree Hcurrent Hdest.
  induction Hpath as [u|e es w Hedge Hpath IH];
    intros s pre Hpre Hentry Hstart Hfree Hcurrent Hdest.
  - congruence.
  - destruct (eqb_dec enc HE (Graph.target g e) v) as [Htarget|Htarget].
    + exists e; split; [left; reflexivity|]; split; [exact Hedge|]; split; [exact Htarget|].
      split.
      * apply reachable_iff_path; exists s, pre; split; assumption.
      * intros Hdom; destruct (Hdom s pre Hentry Hpre) as [Heq|[a [Hin Ha]]].
        -- contradiction.
        -- exact (Hfree a Hin Ha).
    + assert (Hsnoc : path g s (pre ++ [e]) (Graph.target g e)).
      { eapply graph_path_app; [exact Hpre|constructor; [exact Hedge|constructor]]. }
      destruct (IH s (pre ++ [e]) Hsnoc Hentry Hstart) as [a [Hin Hrest]].
      * intros a Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hin]].
        -- apply Hfree; exact Hin.
        -- subst a; exact Htarget.
        -- contradiction.
      * congruence.
      * exact Hdest.
      * exists a; split; [right; exact Hin|exact Hrest].
Qed.

Local Lemma first_arrival {N E} (p : Prepared.t N E) v s es :
  Prepared.ready p -> ~ In v (Graph.entries (Prepared.graph p)) ->
  In s (Graph.entries (Prepared.graph p)) -> path (Prepared.graph p) s es v ->
  exists e, In e es /\ In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) /\
    Graph.target (Prepared.graph p) e = v /\ reachable (Prepared.graph p)
      (Graph.source (Prepared.graph p) e) /\
    ~ dominates (Prepared.graph p) v (Graph.source (Prepared.graph p) e).
Proof.
  intros Hready Hnot Hentry Hpath.
  eapply (first_arrival_aux (Prepared.node_enc p)
    (Prepared.encoding_valid p (proj2 (proj2 Hready))) _ v s [] s es).
  - constructor.
  - exact Hentry.
  - intro Heq; subst; contradiction.
  - intros a Hin; contradiction.
  - intro Heq; subst; contradiction.
  - exact Hpath.
Qed.

Local Lemma map_of_list_property {K V} enc (HE : encoding_laws enc)
    (R : K -> V -> Prop) rows :
  (forall k v, In (k, v) rows -> R k v) ->
  forall k v, Map.get enc k (Map.of_list enc rows) = Some v -> R k v.
Proof.
  intros Hrows k v; rewrite Map.of_list_get.
  assert (Hfold : forall xs old,
    (forall a w, In (a, w) xs -> R a w) ->
    (forall w, old = Some w -> R k w) ->
    forall w, fold_left (fun old kv =>
      if eqb enc k (fst kv) then Some (snd kv) else old) xs old = Some w -> R k w).
  { intro xs; induction xs as [|[a w] xs IH]; intros old Hxs Hold z Hresult.
    - cbn in Hresult; apply Hold; exact Hresult.
    - cbn [fold_left fst snd] in Hresult; eapply IH; [| |exact Hresult].
      + intros b y Hin; apply Hxs; right; exact Hin.
      + destruct (eqb enc k a) eqn:Heq.
        * apply (eqb_true_iff enc HE) in Heq; subst a.
          intros y Heq; injection Heq as <-; apply Hxs; left; reflexivity.
        * exact Hold. }
  apply Hfold; [exact Hrows|intros w Hbad; discriminate].
Qed.

Local Lemma context_index_choice {N E} (p : Prepared.t N E) t v e :
  Map.get positive_encoding v (dc_index (make_dom_context p t)) = Some (Some e) ->
  edge_choice p t (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) v = Some e.
Proof.
  unfold make_dom_context; cbn [dc_index].
  intro Hget; symmetry.
  eapply (map_of_list_property _ positive_encoding_laws
    (fun v selected =>
      selected = edge_choice p t (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) v));
    [|exact Hget].
  intros k value Hin; apply in_map_iff in Hin; destruct Hin as [u [Heq _]].
  inversion Heq; reflexivity.
Qed.

Local Lemma candidate_present {N E} (p : Prepared.t N E) t v i e :
  Prepared.ready p -> Dom.exact p t -> reachable (Prepared.graph p) v ->
  Prepared.id_of p v = Some i ->
  In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) ->
  Graph.target (Prepared.graph p) e = v ->
  reachable (Prepared.graph p) (Graph.source (Prepared.graph p) e) ->
  ~ dominates (Prepared.graph p) v (Graph.source (Prepared.graph p) e) ->
  exists j, In (e, j)
    (edge_candidates p t (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) i).
Proof.
  intros Hready Ht Hv Hi Hedge Htarget Hsource Hnot.
  destruct Hready as [Hwf [Hdistinct Hp]].
  destruct (proj1 (Prepared.ids_domain p Hp _) (reachable_in_nodes _ _ Hwf Hsource))
    as [j Hj].
  exists j; unfold edge_candidates; apply filter_In; split.
  - apply (proj2 (Prepared.pred_agrees p Hp v i e j Hi)); repeat split; try assumption.
    eapply reachable_in_nodes; eassumption.
  - apply andb_true_iff; split.
    + apply (proj2 (Reach.entries_exact p _ j (conj Hwf (conj Hdistinct Hp)) Hj)); exact Hsource.
    + apply negb_true_iff; cbn [snd].
      destruct (DomCheck.dominates_b t i j) eqn:Hdom; [|reflexivity].
      exfalso; apply Hnot.
      eapply (proj1 (DomCheck.dominates_b_spec p t _ v j i
        (conj Hwf (conj Hdistinct Hp)) Ht Hsource Hv Hj Hi)); exact Hdom.
Qed.

Local Lemma indexed_edge_dominates {N E} (p : Prepared.t N E) t v i e :
  Prepared.ready p -> Dom.exact p t -> reachable (Prepared.graph p) v ->
  Prepared.id_of p v = Some i ->
  Map.get positive_encoding i (dc_index (make_dom_context p t)) = Some (Some e) ->
  edge_dominates (Prepared.graph p) e v.
Proof.
  intros Hready Ht Hv Hi Hget; apply context_index_choice in Hget.
  unfold edge_choice in Hget.
  destruct (existsb (Pos.eqb i) (Prepared.entry_ids p)) eqn:Hentry; [discriminate|].
  assert (Hnot : ~ In v (Graph.entries (Prepared.graph p))).
  { intro Hin.
    assert (Hid : In i (Prepared.entry_ids p)).
    { apply (proj2 (Prepared.entry_ids_spec p i (proj2 (proj2 Hready)))).
      exists v; split; assumption. }
    assert (Htrue : existsb (Pos.eqb i) (Prepared.entry_ids p) = true).
    { apply existsb_exists; exists i; split; [exact Hid|apply Pos.eqb_refl]. }
    congruence. }
  destruct (edge_candidates p t (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) i)
    as [|[a j] [|b rest]] eqn:Hcandidates; try discriminate.
  injection Hget as <-.
  intros s es Hs Hpath.
  destruct (first_arrival p v s es Hready Hnot Hs Hpath)
    as [e [Hin [Hedge [Htarget [Hsource Hnotdom]]]]].
  destruct (candidate_present p t v i e Hready Ht Hv Hi Hedge Htarget Hsource Hnotdom)
    as [k Hcandidate].
  rewrite Hcandidates in Hcandidate.
  destruct Hcandidate as [Heq|Hbad]; [inversion Heq; subst; exact Hin|contradiction].
Qed.

Local Lemma edge_dom_trans {N E} (g : Graph.t N E) e v n :
  edge_dominates g e v -> dominates g v n -> edge_dominates g e n.
Proof.
  intros Hedge Hdom s es Hentry Hpath.
  destruct (Hdom s es Hentry Hpath) as [Heq|[a [Hin Htarget]]].
  - subst v; specialize (Hedge s [] Hentry (path_nil s)); contradiction.
  - destruct (prefix_target g s es n a Hpath Hin) as [pre [Hpre Hsub]].
    rewrite Htarget in Hpre; apply Hsub; apply Hedge with s; assumption.
Qed.

Local Definition walk_invariant {E} (t : Dom.tree) (index : Map.t positive (option E))
    start (state : option positive * list E) : Prop :=
  (forall v, fst state = Some v -> idom_ancestor (Dom.idom t) v start) /\
  (forall e, In e (snd state) -> exists v,
    Map.get positive_encoding v index = Some (Some e) /\
      idom_ancestor (Dom.idom t) v start).

Local Definition result_invariant {N E} (ctx : dom_context N E) start result :=
  match result with
  | inl state => walk_invariant (dc_tree ctx) (dc_index ctx) start state
  | inr es => forall e, In e es -> exists v,
      Map.get positive_encoding v (dc_index ctx) = Some (Some e) /\
        idom_ancestor (Dom.idom (dc_tree ctx)) v start
  end.

Local Lemma walk_step_invariant {N E} (ctx : dom_context N E) start state :
  walk_invariant (dc_tree ctx) (dc_index ctx) start state ->
  result_invariant ctx start (Cost.value (dom_walk_step_c ctx state)).
Proof.
  destruct state as [[v|] es]; intros [Hcurrent Hedges];
    unfold dom_walk_step_c; autorewrite with galois_cost; [|exact Hedges].
  change (walk_invariant (dc_tree ctx) (dc_index ctx) start
    (Map.get positive_encoding v (Dom.idom (dc_tree ctx)),
      match Map.get positive_encoding v (dc_index ctx) with
      | Some (Some e) => e :: es
      | _ => es
      end)).
  unfold walk_invariant; cbn [fst snd].
  split.
  - intros u Hparent; eapply rt_trans.
    + apply rt_step; exact Hparent.
    + apply Hcurrent; reflexivity.
  - destruct (Map.get positive_encoding v (dc_index ctx)) as [[a|]|] eqn:Hget;
      cbn [snd].
    + intros e [Heq|Hin].
      * subst e; exists v; split; [exact Hget|apply Hcurrent; reflexivity].
      * apply Hedges; exact Hin.
    + exact Hedges.
    + exact Hedges.
Qed.

Local Lemma walk_runs_invariant {N E} (ctx : dom_context N E) start fuel state result :
  runs (dom_walk_step_c ctx) fuel state result ->
  walk_invariant (dc_tree ctx) (dc_index ctx) start state ->
  result_invariant ctx start result.
Proof.
  intro Hrun; induction Hrun as [state|fuel state es Hstop|
    fuel state next result Hnext Hrun IH]; intro Hinv.
  - exact Hinv.
  - pose proof (walk_step_invariant ctx start state Hinv) as Hresult.
    rewrite Hstop in Hresult; exact Hresult.
  - apply IH; pose proof (walk_step_invariant ctx start state Hinv) as Hresult.
    rewrite Hnext in Hresult; exact Hresult.
Qed.

Local Lemma query_edges_ancestor {N E} (ctx : dom_context N E) n start e :
  Prepared.id_of (dc_prepared ctx) n = Some start ->
  In e (dominating_edges_in ctx n) ->
  exists v, Map.get positive_encoding v (dc_index ctx) = Some (Some e) /\
    idom_ancestor (Dom.idom (dc_tree ctx)) v start.
Proof.
  intro Hstart; unfold dominating_edges_in, dominating_edges_in_c.
  rewrite !Cost.value_bind, Cost.value_ret.
  change (Prepared.id_of (dc_prepared ctx) n) with
    (Cost.value (Prepared.id_of_c (dc_prepared ctx) n)) in Hstart.
  rewrite Hstart.
  pose proof (walk_runs_invariant ctx start _ (Some start, []) _
    (iterate_value (dom_walk_step_c ctx) (dc_fuel ctx) (Some start, []))) as Hinv.
  specialize (Hinv ltac:(split;
    [intros v Heq; injection Heq as <-; apply rt_refl|intros a Hin; contradiction])).
  destruct (Cost.value (iterate (dom_walk_step_c ctx) (dc_fuel ctx) (Some start, [])))
    as [[current edges]|edges].
  - exact (proj2 Hinv e).
  - exact (Hinv e).
Qed.

Local Lemma ancestor_named {N E} (p : Prepared.t N E) t u v :
  Prepared.ready p -> Dom.exact p t -> idom_ancestor (Dom.idom t) u v ->
  (exists n, Prepared.id_of p n = Some v /\ reachable (Prepared.graph p) n) ->
  exists d, Prepared.id_of p d = Some u /\ reachable (Prepared.graph p) d.
Proof.
  intros Hready Ht Hanc.
  induction Hanc as [u v Hget|v|u w v Huw IHuw Hwv IHwv]; intro Hnamed.
  - destruct (Dom.idom_domain p t Ht v u Hget)
      as [n [d [Hnv [Hud [Hn Hd]]]]].
    exists d; split; [|exact Hd].
    exact (Prepared.id_of_name_of p u d (proj2 (proj2 Hready)) Hud).
  - exact Hnamed.
  - apply IHuw, IHwv; exact Hnamed.
Qed.

(** Queries against any ready graph and exact supplied tree return semantically dominating edges. *)
Theorem dominating_edges_in_sound {N E} (p : Prepared.t N E) t n e :
  Prepared.ready p -> Dom.exact p t ->
  In e (dominating_edges_in (make_dom_context p t) n) ->
  edge_dominates (Prepared.graph p) e n.
Proof.
  intros Hready Ht Hin s es Hentry Hpath.
  assert (Hn : reachable (Prepared.graph p) n).
  { apply reachable_iff_path; exists s, es; split; assumption. }
  destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) n)
    (reachable_in_nodes _ _ (proj1 Hready) Hn)) as [start Hstart].
  destruct (query_edges_ancestor (make_dom_context p t) n start e Hstart Hin)
    as [v [Hget Hanc]].
  destruct (ancestor_named p t v start Hready Ht Hanc ltac:(exists n; split; assumption))
    as [d [Hd Hreachd]].
  assert (Hdom : edge_dominates (Prepared.graph p) e n).
  { eapply edge_dom_trans.
    - eapply indexed_edge_dominates; eassumption.
    - apply (proj1 (DomCheck.ancestry_spec p t n d start v Hready Ht Hn Hstart Hd)).
      exact Hanc. }
  exact (Hdom s es Hentry Hpath).
Qed.

(** Duplicate-tolerant preparation indexes distinct edge occurrences before projecting answers. *)
Definition make_occurrence_dom_context {N E} enc (g : Graph.t N E) t :=
  make_dom_context (Prepared.prepare enc (EdgeProjection.occurrence_graph g)) t.

(** Projecting a query retains answer order and charges the projection traversal. *)
Definition dominating_edges_projected_c {N E} (ctx : dom_context N (E * nat)) n :=
  let* es := dominating_edges_in_c ctx n in
  map_c (fun ei => Cost.ret (fst ei)) es.

Definition dominating_edges_projected {N E} (ctx : dom_context N (E * nat)) n :=
  Cost.value (dominating_edges_projected_c ctx n).

(** Projected queries preserve every selected answer in its ancestor order. *)
Theorem dominating_edges_projected_equation {N E} (ctx : dom_context N (E * nat)) n :
  dominating_edges_projected ctx n = map fst (dominating_edges_in ctx n).
Proof.
  unfold dominating_edges_projected, dominating_edges_projected_c.
  rewrite Cost.value_bind, value_map_c; reflexivity.
Qed.

(** Occurrence-query answers dominate in the original graph even with duplicate outgoing values. *)
Theorem dominating_edges_projected_sound {N E} enc (g : Graph.t N E) t n e :
  encoding_laws enc -> graph_wf g ->
  Dom.exact (Prepared.prepare enc (EdgeProjection.occurrence_graph g)) t ->
  In e (dominating_edges_projected (make_occurrence_dom_context enc g t) n) ->
  edge_dominates g e n.
Proof.
  intros HE Hwf Ht Hin; rewrite dominating_edges_projected_equation in Hin.
  apply in_map_iff in Hin; destruct Hin as [ei [<- Hin]].
  eapply EdgeProjection.edge_dominance_project.
  - apply EdgeProjection.occurrence_projection.
  - pose proof (dominating_edges_in_sound
      (Prepared.prepare enc (EdgeProjection.occurrence_graph g)) t n ei) as Hsound.
    rewrite Prepared.prepare_graph in Hsound; apply Hsound; [|exact Ht|exact Hin].
    apply Prepared.prepare_ready; [exact HE| |].
    + apply EdgeProjection.occurrence_graph_wf; exact Hwf.
    + intro v; rewrite EdgeProjection.occurrence_out; apply EdgeProjection.occurrences_nodup.
Qed.
