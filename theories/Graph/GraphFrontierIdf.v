(** * Iterated frontier closure

    A finite work stack closes the supplied frontier map and filters every emitted target.
    For example, a loop header can reappear even when it is already a definition.
    Builds on: GraphFrontierSweep and the shared finite-closure driver. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphReach GraphWalk
  GraphDomSpec GraphFrontierSpec GraphFrontierSweep.
Import List.ListNotations Cost.Notations.

Module FrontierIdf.

(** Pruned closure requires a live target at every frontier step. *)
Inductive in_pruned_idf {V E} (g : Graph.t V E) (defs : list V) (live : V -> bool) :
    V -> Prop :=
  | pruned_seed : forall d x, In d defs -> in_df g d x -> live x = true ->
      in_pruned_idf g defs live x
  | pruned_step : forall d x, in_pruned_idf g defs live d -> in_df g d x ->
      live x = true -> in_pruned_idf g defs live x.

Definition successors_c df (live : positive -> Cost.t bool) d :=
  let* row := Map.find_or_c positive_encoding FinSet.empty d df in
  let* xs := FinSet.elements_c row in
  filter_c (fun x => Cost.step ;; live x) xs.

Definition successors df live d := Cost.value (successors_c df live d).

Local Lemma successors_spec df live d x :
  FrontierSweep.rows_wf df ->
  (In x (successors df live d) <->
    FrontierSweep.frontier_at df d x /\ Cost.value (live x) = true).
Proof.
  intros [Hmap Hrows]. unfold successors, successors_c.
  rewrite Cost.value_bind, Cost.value_bind, value_filter_c.
  fold (Map.find_or positive_encoding FinSet.empty d df).
  fold (FinSet.elements (Map.find_or positive_encoding FinSet.empty d df)).
  rewrite filter_In. autorewrite with galois_cost.
  rewrite Map.find_or_equation.
  unfold FrontierSweep.frontier_at.
  destruct (Map.get positive_encoding d df) as [row|] eqn:Hrow.
  - rewrite (FinSet.elements_spec positive_encoding positive_encoding_laws)
      by now apply (Hrows d row).
    split; [intros [Hm Hl]; split; [now exists row|exact Hl]|].
    intros [[row' [Heq Hm]] Hl]. inversion Heq; subst row'. auto.
  - rewrite (FinSet.elements_spec positive_encoding positive_encoding_laws)
      by apply FinSet.wf_empty.
    rewrite FinSet.mem_empty.
    split; [intros [Hfalse _]; discriminate|intros [[row [Hfalse _]] _]; discriminate].
Qed.

Definition seeds_c {V E} (p : Prepared.t V E) defs :=
  filter_map_c (Prepared.id_of_c p) defs.

Local Lemma seeds_spec {V E} (p : Prepared.t V E) defs i :
  In i (Cost.value (seeds_c p defs)) <->
    exists d, In d defs /\ Prepared.id_of p d = Some i.
Proof.
  unfold seeds_c. rewrite value_filter_map_c.
  induction defs as [|d rest IH]; cbn [filter_map fold_right].
  - split; [contradiction|intros [x [Hfalse _]]; contradiction].
  - destruct (Prepared.id_of_c p d) as [o ticks] eqn:Hcall.
    cbn. destruct o as [j|]; cbn [In].
    + rewrite IH. split.
      * intros [<-|[x [Hx Hi]]].
        -- exists d. split; [now left|]. unfold Prepared.id_of. rewrite Hcall. reflexivity.
        -- exists x. split; [now right|exact Hi].
      * intros [x [[<-|Hx] Hi]].
        -- left. unfold Prepared.id_of in Hi. rewrite Hcall in Hi. now inversion Hi.
        -- right. now exists x.
    + rewrite IH. split.
      * intros [x [Hx Hi]]. exists x. auto.
      * intros [x [[<-|Hx] Hi]].
        -- unfold Prepared.id_of in Hi. rewrite Hcall in Hi. discriminate.
        -- now exists x.
Qed.

Definition initial_c df live seeds :=
  fold_right_c (fun d rest =>
    let* fresh := successors_c df live d in
    app_c fresh rest) [] seeds.

Local Lemma initial_equation df live seeds :
  Cost.value (initial_c df live seeds) = flat_map (successors df live) seeds.
Proof.
  unfold initial_c. rewrite value_fold_right_c.
  induction seeds as [|d rest IH]; cbn [fold_right flat_map]; [reflexivity|].
  rewrite Cost.value_bind, value_app_c, IH. reflexivity.
Qed.

(** This reference IDF computes the least frontier closure and retains every live callback charge. *)
Definition idf_pruned_c {V E} (p : Prepared.t V E) t defs live :=
  let* df := FrontierSweep.dominance_frontier_c p t in
  let* seeds := seeds_c p defs in
  let* initial := initial_c df live seeds in
  let* all := FrontierSweep.universe_c p in
  FrontierSweep.closure_c (successors_c df live) all initial.

Definition idf_pruned {V E} (p : Prepared.t V E) t defs live :=
  Cost.value (idf_pruned_c p t defs live).

Definition idf_c {V E} (p : Prepared.t V E) t defs :=
  idf_pruned_c p t defs (fun _ => Cost.ret true).
Definition idf {V E} (p : Prepared.t V E) t defs := Cost.value (idf_c p t defs).

(** Pruned IDF always returns a canonical set, independently of semantic graph and tree duties. *)
Theorem pruned_idf_wf {V E} (p : Prepared.t V E) t defs live :
  FinSet.wf positive_encoding (idf_pruned p t defs live).
Proof.
  unfold idf_pruned, idf_pruned_c. rewrite Cost.value_bind.
  fold (FrontierSweep.dominance_frontier p t). do 3 rewrite Cost.value_bind.
  exact (FrontierSweep.closure_wf
    (successors_c (FrontierSweep.dominance_frontier p t) live)
    (Cost.value (FrontierSweep.universe_c p))
    (Cost.value (initial_c (FrontierSweep.dominance_frontier p t) live
      (Cost.value (seeds_c p defs))))).
Qed.

(** Ordinary IDF inherits canonical output from the same pruned closure computation. *)
Theorem idf_wf {V E} (p : Prepared.t V E) t defs :
  FinSet.wf positive_encoding (idf p t defs).
Proof.
  exact (pruned_idf_wf p t defs (fun _ => Cost.ret true)).
Qed.

(** Semantic liveness reads the same ID callback used by the executable closure. *)
Definition live_on {V E} (p : Prepared.t V E) (live : positive -> Cost.t bool) n :=
  match Prepared.id_of p n with
  | None => false
  | Some i => Cost.value (live i)
  end.

Local Lemma idf_closure {V E} (p : Prepared.t V E) t defs live j :
  Prepared.ready p ->
  (FinSet.mem positive_encoding j (idf_pruned p t defs live) = true <->
    Reach.closure (successors (FrontierSweep.dominance_frontier p t) live)
      (flat_map (successors (FrontierSweep.dominance_frontier p t) live)
        (Cost.value (seeds_c p defs))) j).
Proof.
  intro Hready. unfold idf_pruned, idf_pruned_c.
  rewrite Cost.value_bind. fold (FrontierSweep.dominance_frontier p t).
  rewrite !Cost.value_bind, initial_equation, FrontierSweep.universe_value.
  apply FrontierSweep.closure_exact.
  - unfold Reach.universe. apply NoDup_nodup.
  - intros x Hx. apply in_flat_map in Hx. destruct Hx as [d [_ Hx]].
    apply (successors_spec _ _ _ _ (FrontierSweep.dominance_frontier_wf p t)) in Hx.
    apply Reach.universe_spec.
    eapply FrontierSweep.frontier_target_valid; [exact Hready|exact (proj1 Hx)].
  - intros d x Hx.
    apply (successors_spec _ _ _ _ (FrontierSweep.dominance_frontier_wf p t)) in Hx.
    apply Reach.universe_spec.
    eapply FrontierSweep.frontier_target_valid; [exact Hready|exact (proj1 Hx)].
Qed.

Local Lemma path_targets {V E} (g : Graph.t V E) s es n :
  path g s es n -> reachable g s ->
  forall e, In e es -> reachable g (Graph.target g e).
Proof.
  intro Hpath. induction Hpath as [v|a rest n Ha Hpath IH]; intros Hs e Hin.
  - contradiction.
  - assert (Ht : reachable g (Graph.target g a)) by (eapply reachable_step; eassumption).
    destruct Hin as [<-|Hin]; [exact Ht|now apply IH].
Qed.

Local Lemma df_named {V E} (p : Prepared.t V E) d n :
  Prepared.ready p -> in_df (Prepared.graph p) d n ->
  exists i j, Prepared.id_of p d = Some i /\ Prepared.id_of p n = Some j.
Proof.
  intros Hready [e [Hs [He [Htarget [Hd _]]]]].
  assert (Hn : reachable (Prepared.graph p) n).
  { rewrite <- Htarget. eapply reachable_step; eassumption. }
  assert (Hdn : In d (Graph.nodes (Prepared.graph p))).
  { apply reachable_iff_path in Hs.
    destruct Hs as [s [es [Hentry Hpath]]].
    destruct (Hd s es Hentry Hpath) as [->|[a [Ha Hda]]].
    - exact (entries_in (proj1 Hready) s Hentry).
    - rewrite <- Hda. apply (reachable_in_nodes _ _ (proj1 Hready)).
      eapply path_targets; [exact Hpath|now apply reachable_entry|exact Ha]. }
  destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) d) Hdn) as [i Hi].
  destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) n)
    (reachable_in_nodes _ _ (proj1 Hready) Hn)) as [j Hj].
  exists i, j. auto.
Qed.

(** Pruned IDF is exact for all named queries and unrestricted definition lists. *)
Theorem pruned_idf_exact {V E} (p : Prepared.t V E) t defs live n j :
  Prepared.ready p -> Dom.exact p t -> Prepared.id_of p n = Some j ->
  (FinSet.mem positive_encoding j (idf_pruned p t defs live) = true <->
    in_pruned_idf (Prepared.graph p) defs (live_on p live) n).
Proof.
  intros Hready Htree Hn. rewrite idf_closure by exact Hready.
  set (df := FrontierSweep.dominance_frontier p t).
  assert (Hwf : FrontierSweep.rows_wf df) by apply FrontierSweep.dominance_frontier_wf.
  assert (Hnext : forall d x i k, Prepared.id_of p d = Some i ->
    Prepared.id_of p x = Some k ->
    (In k (successors df live i) <->
      in_df (Prepared.graph p) d x /\ live_on p live x = true)).
  { intros d x i k Hd Hx. rewrite successors_spec by exact Hwf.
    unfold df. rewrite (FrontierSweep.dominance_frontier_exact p t d x i k
      Hready Htree Hd Hx). unfold live_on. now rewrite Hx. }
  split.
  - intro Hclosure.
    assert (Hsound : forall k,
      Reach.closure (successors df live)
        (flat_map (successors df live) (Cost.value (seeds_c p defs))) k ->
      exists x, Prepared.id_of p x = Some k /\
        in_pruned_idf (Prepared.graph p) defs (live_on p live) x).
    { intros k Hk. induction Hk as [k Hroot|i k Hi [d [Hd Hderiv]] Hik].
      - apply in_flat_map in Hroot. destruct Hroot as [i [Hi Hik]].
        apply seeds_spec in Hi. destruct Hi as [d [Hdef Hd]].
        pose proof (proj1 (successors_spec df live i k Hwf) Hik) as [Hat _].
        destruct (FrontierSweep.frontier_target_valid p t i k Hready Hat)
          as [x [_ Hx]].
        apply (Hnext d x i k Hd Hx) in Hik. destruct Hik as [Hdf Hlive].
        exists x. split; [exact Hx|]. eapply pruned_seed; eassumption.
      - pose proof (proj1 (successors_spec df live i k Hwf) Hik) as [Hat _].
        destruct (FrontierSweep.frontier_target_valid p t i k Hready Hat)
          as [x [_ Hx]].
        apply (Hnext d x i k Hd Hx) in Hik. destruct Hik as [Hdf Hlive].
        exists x. split; [exact Hx|]. eapply pruned_step; eassumption. }
    destruct (Hsound j Hclosure) as [x [Hx Hderiv]].
    assert (x = n).
    { pose proof (Prepared.name_of_id_of p x j (proj2 (proj2 Hready)) Hx).
      pose proof (Prepared.name_of_id_of p n j (proj2 (proj2 Hready)) Hn). congruence. }
    now subst x.
  - intro Hderiv. revert j Hn.
    induction Hderiv as [d x Hdef Hdf Hlive|d x Hderiv IH Hdf Hlive]; intros j Hj.
    + destruct (df_named p d x Hready Hdf) as [i [k [Hi Hk]]].
      assert (k = j) by congruence. subst k.
      apply Reach.root, in_flat_map. exists i. split.
      * apply seeds_spec. now exists d.
      * now apply (Hnext d x i j Hi Hj).
    + destruct (df_named p d x Hready Hdf) as [i [k [Hi Hk]]].
      eapply Reach.edge; [exact (IH i Hi)|].
      now apply (Hnext d x i j Hi Hj).
Qed.

(** The all-live reference closure is exactly ordinary nonreflexive iterated dominance frontier. *)
Theorem idf_exact {V E} (p : Prepared.t V E) t defs n j :
  Prepared.ready p -> Dom.exact p t -> Prepared.id_of p n = Some j ->
  (FinSet.mem positive_encoding j (idf p t defs) = true <->
    in_idf (Prepared.graph p) defs n).
Proof.
  intros Hready Htree Hn.
  change (FinSet.mem positive_encoding j
    (idf_pruned p t defs (fun _ => Cost.ret true)) = true <->
    in_idf (Prepared.graph p) defs n).
  rewrite (pruned_idf_exact p t defs (fun _ => Cost.ret true) n j Hready Htree Hn).
  clear Hn j.
  split.
  - intro H. induction H as [d x Hdef Hdf _|d x Hderiv IH Hdf _].
    + eapply idf_seed; eassumption.
    + eapply idf_step; [exact IH|exact Hdf].
  - intro H. induction H as [d x Hdef Hdf|d x Hderiv IH Hdf].
    + eapply pruned_seed; [exact Hdef|exact Hdf|].
      destruct (df_named p d x Hready Hdf) as [i [k [Hi Hk]]].
      unfold live_on. rewrite Hk. reflexivity.
    + eapply pruned_step; [exact IH|exact Hdf|].
      destruct (df_named p d x Hready Hdf) as [i [k [Hi Hk]]].
      unfold live_on. rewrite Hk. reflexivity.
Qed.

End FrontierIdf.
