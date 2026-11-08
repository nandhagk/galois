(** * Tarjan producer guarantees

    Producer theorems concern the visitor state returned by the actual shared search.
    For example, an unknown supplied root has no component owner.
    Builds on: GraphTarjanRankTrace, GraphTarjanPartition and the public search guarantees. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchExact GraphSearchCost GraphSearchScopedCost GraphSccSpec GraphTarjan GraphTarjanState
  GraphTarjanLow GraphTarjanTrace GraphTarjanPartition GraphTarjanRankTrace.
Import List.ListNotations.

Module TarjanExact.

(** Popping splits the actual stack into precisely its consumed prefix and surviving suffix. *)
Theorem pop_split root i xs lows active own :
  let answer := Tarjan.pop root i xs lows active own in
  xs = Tarjan.members answer ++ Tarjan.tail answer /\
    (In root xs -> In root (Tarjan.members answer)).
Proof.
  apply TarjanStateFacts.pop_split.
Qed.

(** Every actual owner map has canonical storage even without preparation readiness. *)
Theorem compute_owners_wf {V E} (p : Prepared.t V E) scope roots :
  Map.wf positive_encoding (Scc.comp_of (Tarjan.compute p scope roots)).
Proof.
  apply TarjanStateFacts.compute_owners_wf.
Qed.

(** Discovery ranks agree with the same actual visitor run's preorder. *)
Theorem discovery_index {V E} (p : Prepared.t V E) scope roots v i :
  Prepared.ready p ->
  (Map.get positive_encoding v
    (Tarjan.disc (snd (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)))) = Some i <->
    nth_error (Search.preorder (fst (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))))
      (Nat.pred (Pos.to_nat i)) = Some v).
Proof.
  apply TarjanStateFacts.discovery_index.
Qed.

(** Every owner binding belongs to the admitted reachable region for arbitrary roots. *)
Theorem owners_reachable {V E} (p : Prepared.t V E) scope roots v i :
  Prepared.ready p ->
  Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some i ->
    Search.scoped_reachable p scope roots v.
Proof.
  apply TarjanStateFacts.owners_reachable.
Qed.

(** Every emitted member belongs to the admitted reachable region for arbitrary roots. *)
Theorem components_reachable {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> In v (concat (Scc.components (Tarjan.compute p scope roots))) ->
    Search.scoped_reachable p scope roots v.
Proof.
  apply TarjanStateFacts.components_reachable.
Qed.

(** Scope-rejected vertices have no owner in the actual computation. *)
Theorem rejected_unowned {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> Scope.admits scope v = false ->
    Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = None.
Proof.
  apply TarjanStateFacts.rejected_unowned.
Qed.

(** Unknown IDs have no owner even when the scope admits them. *)
Theorem unknown_unowned {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> ~ Prepared.valid_id p v ->
    Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = None.
Proof.
  apply TarjanStateFacts.unknown_unowned.
Qed.

(** The actual visitor state is the fold of the same actual Search event list. *)
Theorem compute_events {V E} (p : Prepared.t V E) scope roots :
  Tarjan.compute p scope roots =
    Tarjan.result (SearchRun.apply_events Tarjan.visitor
      (SearchRun.events p scope roots) Tarjan.initial).
Proof.
  apply TarjanStateFacts.compute_events.
Qed.

(** Empty supplied roots produce the empty component partition and owner map. *)
Theorem compute_empty {V E} (p : Prepared.t V E) scope :
  Tarjan.compute p scope [] = Scc.Result [] Map.empty.
Proof.
  apply TarjanStateFacts.compute_empty.
Qed.

(** The full SCC specification holds for empty roots without readiness. *)
Theorem empty_roots_exact {V E} (p : Prepared.t V E) scope :
  Scc.exact p scope [] (Tarjan.compute p scope []).
Proof.
  apply TarjanStateFacts.empty_roots_exact.
Qed.

(** One final Search core witnesses the actual visitor result and complete temporal trace. *)
Theorem compute_trace {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  exists final,
    fst (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)) =
      SearchRun.result final /\
    SearchRun.trace_roots p scope roots SearchRun.initial
      (SearchRun.events p scope roots) final /\
    Tarjan.compute p scope roots =
      Tarjan.result (SearchRun.apply_events Tarjan.visitor
        (SearchRun.events p scope roots) Tarjan.initial).
Proof.
  apply TarjanStateFacts.compute_trace.
Qed.

(** Every complete actual search leaves Tarjan's pending stack empty across all root boundaries. *)
Theorem stack_empty {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  Tarjan.stack (snd (Cost.value
    (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))) = [].
Proof.
  apply TarjanTrace.actual_stack_empty.
Qed.

(** The actual components form a duplicate-free flattened partition. *)
Theorem partition_unique {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> NoDup (concat (Scc.components (Tarjan.compute p scope roots))).
Proof.
  apply TarjanPartition.partition_unique.
Qed.

(** The actual partition covers exactly scoped reachability for arbitrary supplied roots. *)
Theorem partition_complete {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p ->
  (In v (concat (Scc.components (Tarjan.compute p scope roots))) <->
    Search.scoped_reachable p scope roots v).
Proof.
  apply TarjanPartition.partition_complete.
Qed.

(** The actual owner map is exactly the one-based index of each containing output component. *)
Theorem owners_exact {V E} (p : Prepared.t V E) scope roots v i :
  Prepared.ready p ->
  (Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some i <->
    exists c, nth_error (Scc.components (Tarjan.compute p scope roots))
      (Nat.pred (Pos.to_nat i)) = Some c /\ In v c).
Proof.
  apply TarjanPartition.owners_exact.
Qed.

(** Every scoped reachable vertex has its actual component owner without a default index. *)
Theorem visited_has_component {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> Search.scoped_reachable p scope roots v ->
  exists i, Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some i.
Proof.
  apply TarjanPartition.visited_has_component.
Qed.

(** Every pair of actual component members has scoped paths in both directions. *)
Theorem components_mutual {V E} (p : Prepared.t V E) scope roots c u v :
  Prepared.ready p -> In c (Scc.components (Tarjan.compute p scope roots)) ->
  In u c -> In v c ->
  (exists es, Search.scoped_path p scope u es v) /\
    (exists es, Search.scoped_path p scope v es u).
Proof.
  apply TarjanPartition.components_mutual.
Qed.

(** Every actual admitted arc from an owned source reaches a no-greater actual component owner. *)
Theorem compute_rank {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  forall u e v i, Map.get positive_encoding u (Scc.comp_of (Tarjan.compute p scope roots)) = Some i ->
    Prepared.arc p u e v -> Scope.admits scope v = true ->
    exists j, Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some j /\
      (j <= i)%positive.
Proof.
  intro Hready. rewrite Tarjan.compute_equation, Tarjan.result_equation.
  cbn [Scc.comp_of]. exact (TarjanRankTrace.actual_output_rank p scope roots Hready).
Qed.

Local Lemma path_start_admitted {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v -> Scope.admits scope u = true.
Proof.
  intro Hpath. destruct Hpath; assumption.
Qed.

Local Lemma path_end_admitted {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v -> Scope.admits scope v = true.
Proof.
  intro Hpath. induction Hpath; tauto.
Qed.

(** A scoped path starting at an actual owner ends at an actual owner of no greater index. *)
Theorem path_owner {V E} (p : Prepared.t V E) scope roots u es v i :
  Prepared.ready p -> Search.scoped_path p scope u es v ->
  Map.get positive_encoding u (Scc.comp_of (Tarjan.compute p scope roots)) = Some i ->
  exists j, Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some j /\
    (j <= i)%positive.
Proof.
  intros Hready Hpath. revert i.
  induction Hpath as [v Hv Ha|u e v es z Hu Ha Harc Hpath IH]; intros i Howner.
  - exists i. split; [exact Howner|apply Pos.le_refl].
  - destruct (compute_rank p scope roots Hready u e v i Howner Harc
      (path_start_admitted p scope v es z Hpath)) as [j [Hj Hji]].
    destruct (IH j Hj) as [k [Hk Hkj]].
    exists k. split; [exact Hk|]. eapply Pos.le_trans; eassumption.
Qed.

(** Mutual scoped paths from an owned vertex force the same actual component owner. *)
Theorem mutual_owner {V E} (p : Prepared.t V E) scope roots u v i :
  Prepared.ready p ->
  Map.get positive_encoding u (Scc.comp_of (Tarjan.compute p scope roots)) = Some i ->
  (exists es, Search.scoped_path p scope u es v) ->
  (exists es, Search.scoped_path p scope v es u) ->
    Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some i.
Proof.
  intros Hready Hu [first Hfirst] [last Hlast].
  destruct (path_owner p scope roots u first v i Hready Hfirst Hu) as [j [Hj Hji]].
  destruct (path_owner p scope roots v last u j Hready Hlast Hj) as [k [Hk Hkj]].
  assert (Heq : k = i) by congruence. subst k.
  assert (Hsame : j = i) by (apply Pos.le_antisym; assumption).
  now subst j.
Qed.

(** Every actual component is a nonempty maximal class for mutual scoped reachability. *)
Theorem block_exact {V E} (p : Prepared.t V E) scope roots c :
  Prepared.ready p -> In c (Scc.components (Tarjan.compute p scope roots)) ->
    Scc.block p scope roots c.
Proof.
  intros Hready Hc. split; [exact (TarjanPartition.components_nonempty p scope roots Hready c Hc)|].
  split; [exact (TarjanPartition.component_nodup p scope roots c Hready Hc)|]. split.
  - intros u Hu. apply (components_reachable p scope roots u Hready).
    apply in_concat. exists c. auto.
  - intros u v Hu. split.
    + intro Hv. split.
      * apply (components_reachable p scope roots v Hready). apply in_concat. exists c. auto.
      * exact (components_mutual p scope roots c u v Hready Hc Hu Hv).
    + intros [_ [Huv Hvu]].
      pose proof Hc as Hposition. apply In_nth_error in Hposition.
      destruct Hposition as [n Hnth].
      assert (Howner : Map.get positive_encoding u
        (Scc.comp_of (Tarjan.compute p scope roots)) = Some (Pos.of_succ_nat n)).
      { apply (owners_exact p scope roots u (Pos.of_succ_nat n) Hready).
        rewrite SuccNat2Pos.id_succ. exists c. auto. }
      pose proof (mutual_owner p scope roots u v (Pos.of_succ_nat n) Hready Howner Huv Hvu) as Hv.
      apply (owners_exact p scope roots v (Pos.of_succ_nat n) Hready) in Hv.
      destruct Hv as [other [Hother Hv]]. rewrite SuccNat2Pos.id_succ in Hother.
      cbn [Nat.pred] in Hother. rewrite Hnth in Hother. inversion Hother; subst other. exact Hv.
Qed.

Local Lemma arc_decreases {V E} (p : Prepared.t V E) scope roots u e v i j :
  Prepared.ready p -> Prepared.arc p u e v ->
  Map.get positive_encoding u (Scc.comp_of (Tarjan.compute p scope roots)) = Some i ->
  Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some j ->
  i <> j -> (j < i)%positive.
Proof.
  intros Hready Harc Hu Hv Hne.
  destruct (owners_reachable p scope roots v j Hready Hv) as [root [es [_ Hpath]]].
  destruct (compute_rank p scope roots Hready u e v i Hu Harc
    (path_end_admitted p scope root es v Hpath)) as [k [Hk Hki]].
  assert (Heq : k = j) by congruence. subst k.
  apply Pos.lt_eq_cases in Hki. intuition congruence.
Qed.

(** Ready preparation alone yields the complete maximal scoped SCC partition and exact owner map. *)
Theorem compute_exact {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> Scc.exact p scope roots (Tarjan.compute p scope roots).
Proof.
  intro Hready. constructor.
  - apply Forall_forall. intros c Hc. exact (block_exact p scope roots c Hready Hc).
  - exact (partition_unique p scope roots Hready).
  - intro v. exact (partition_complete p scope roots v Hready).
  - apply compute_owners_wf.
  - intros v i. exact (owners_exact p scope roots v i Hready).
  - intros u e v i j Harc Hu Hv Hne.
    exact (arc_decreases p scope roots u e v i j Hready Harc Hu Hv Hne).
Qed.

(** Actual cross-component arcs go strictly backwards in the chronological component indices. *)
Theorem reverse_topological {V E} (p : Prepared.t V E) scope roots u e v i j :
  Prepared.ready p -> Prepared.arc p u e v ->
  Map.get positive_encoding u (Scc.comp_of (Tarjan.compute p scope roots)) = Some i ->
  Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some j ->
  i <> j -> (j < i)%positive.
Proof.
  intro Hready.
  exact (Scc.reverse_topological _ _ _ _ (compute_exact p scope roots Hready) u e v i j).
Qed.

(** The actual flattened partition permutes the same actual Search run's discovered vertices. *)
Theorem partition_preorder_permutation {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  Permutation (concat (Scc.components (Tarjan.compute p scope roots)))
    (Search.preorder (fst (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)))).
Proof.
  intro Hready.
  pose proof (SearchExact.run_exact p Tarjan.visitor scope roots Tarjan.initial Hready) as Hsearch.
  apply NoDup_Permutation.
  - exact (partition_unique p scope roots Hready).
  - exact (Search.pre_nodup _ _ _ _ Hsearch).
  - intro v. rewrite (partition_complete p scope roots v Hready),
      (Search.pre_complete _ _ _ _ Hsearch v). reflexivity.
Qed.

Local Lemma nonempty_count {A} (cs : list (list A)) :
  (forall c, In c cs -> c <> []) -> (length cs <= length (concat cs))%nat.
Proof.
  induction cs as [|c rest IH]; intro Hnonempty; [reflexivity|].
  specialize (IH ltac:(intros block Hin; apply Hnonempty; now right)).
  assert (Hc : c <> []) by (apply Hnonempty; now left).
  destruct c as [|x tail]; [contradiction|].
  cbn [concat length]. rewrite length_app. cbn [length]. lia.
Qed.

(** Component counters and member counts are bounded by the actual scoped and global vertex counts. *)
Theorem component_count_bounds {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  (length (Scc.components (Tarjan.compute p scope roots)) <=
    length (concat (Scc.components (Tarjan.compute p scope roots))))%nat /\
  (length (concat (Scc.components (Tarjan.compute p scope roots))) <=
    ScopedSearchCost.node_count p scope)%nat /\
  (length (concat (Scc.components (Tarjan.compute p scope roots))) <=
    length (Graph.nodes (Prepared.graph p)))%nat.
Proof.
  intro Hready. split.
  - apply nonempty_count. exact (TarjanPartition.components_nonempty p scope roots Hready).
  - pose proof (Permutation_length (partition_preorder_permutation p scope roots Hready))
      as Hlength.
    rewrite SearchRun.run_result in Hlength.
    pose proof (ScopedSearchCost.preorder_length p scope roots Hready) as Hscoped.
    pose proof (SearchCost.preorder_length p scope roots Hready) as Hglobal.
    split; lia.
Qed.

End TarjanExact.
