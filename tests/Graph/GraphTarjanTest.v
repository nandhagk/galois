(** * Tarjan component observations

    Local prepared graphs exercise pending vertices, component order and rejected scope targets.
    For example, nested cycles form one maximal SCC while distinct cycles emit separately.
    Builds on: GraphTarjan and the public preparation laws. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchExact GraphSccSpec GraphTarjan GraphTarjanExact.
Import List.ListNotations.

Module TarjanFixtures.
Local Open Scope nat_scope.

Definition graph roots nodes (edges : list (nat * nat)) :=
  Graph.of_pure roots nodes (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition prepare roots nodes edges := Prepared.prepare nat_encoding (graph roots nodes edges).
Definition unrestricted := Scope.Make FinSet.empty None.

(** Local edge-list fixtures are ready when their nodes, entries and edge endpoints are valid. *)
Theorem fixture_ready roots nodes edges :
  NoDup nodes -> incl roots nodes -> NoDup edges ->
  (forall e, In e edges -> In (fst e) nodes /\ In (snd e) nodes) ->
  Prepared.ready (prepare roots nodes edges).
Proof.
  intros Hnodes Hroots Hedges Hendpoints.
  unfold prepare, graph.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - constructor.
    + exact Hnodes.
    + exact Hroots.
    + intros v e He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_source. now apply Nat.eqb_eq, (proj2 He).
    + intros v e _ He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_target. exact (proj2 (Hendpoints e (proj1 He))).
  - intro v. rewrite Graph.of_pure_out. now apply NoDup_filter.
Qed.

Definition line := prepare [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
Definition diamond := prepare [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
Definition self_loop := prepare [1] [1] [(1, 1)].
Definition nested :=
  prepare [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
Definition irreducible :=
  prepare [1] [1; 2; 3] [(1, 2); (1, 3); (2, 3); (3, 2)].
Definition empty := prepare [] [] [].
Definition distinct :=
  prepare [1] [1; 2; 3; 4] [(1, 2); (2, 1); (2, 3); (3, 4); (4, 3)].

(** Each local fixture obtains readiness from preparation rather than a GraphFixtures import. *)
Example fixtures_ready :
  Prepared.ready line /\ Prepared.ready diamond /\ Prepared.ready self_loop /\
  Prepared.ready nested /\ Prepared.ready irreducible /\ Prepared.ready empty /\
  Prepared.ready distinct.
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  all: apply fixture_ready;
    [ repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
    | intros x Hin; vm_compute in Hin |- *; intuition congruence
    | repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
    | intros [a b] Hin; vm_compute in Hin |- *; intuition congruence ].
Qed.

Definition components {V E} (p : Prepared.t V E) :=
  Scc.components (Tarjan.compute p unrestricted (Prepared.entry_ids p)).

Definition owner_list (r : Scc.result) vs := map (fun v => Map.get positive_encoding v
  (Scc.comp_of r)) vs.

Example line_components : components line = [[4]; [3]; [2]; [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_components : components diamond = [[4]; [2]; [3]; [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_component : components self_loop = [[1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_is_one_maximal_component : components nested = [[4; 3; 2; 1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_components : components irreducible = [[3; 2]; [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_components : components empty = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example distinct_reverse_topological : components distinct = [[4; 3]; [2; 1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example distinct_exact_owner_indices :
  owner_list (Tarjan.compute distinct unrestricted [1]%positive) [1; 2; 3; 4; 99]%positive =
    [Some 2; Some 2; Some 1; Some 1; None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Definition inner_scope :=
  Scope.Make FinSet.empty (Some (FinSet.of_list positive_encoding [2; 3]%positive)).
Definition block_two := Scope.Make (FinSet.of_list positive_encoding [2]%positive) None.

Example within_one_component :
  let r := Tarjan.compute nested inner_scope [99; 2; 2; 1]%positive in
  (Scc.components r, owner_list r [1; 2; 3; 4; 99]%positive) =
    ([[3; 2]], [None; Some 1; Some 1; None; None])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example blocked_node_absent :
  let r := Tarjan.compute diamond block_two [1; 2; 99]%positive in
  (Scc.components r, owner_list r [1; 2; 3; 4; 99]%positive) =
    ([[4]; [3]; [1]], [Some 3; None; Some 2; Some 1; None])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_unknown_rejected_roots :
  Tarjan.compute nested inner_scope [99; 2; 2; 1; 99]%positive =
    Tarjan.compute nested inner_scope [2]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Definition parallel_graph :=
  Graph.of_pure [1] [1; 2]
    (fun v => filter (fun e => Nat.eqb (if Nat.eqb e 12 then 2 else 1) v) [10; 11; 12])
    (fun e => if Nat.eqb e 12 then 2 else 1)
    (fun e => if Nat.eqb e 12 then 1 else 2).
Definition parallel := Prepared.prepare nat_encoding parallel_graph.

(** The parallel-label graph is prepared from a well-formed, duplicate-free labelled adjacency. *)
Example parallel_ready : Prepared.ready parallel.
Proof.
  unfold parallel, parallel_graph.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - constructor.
    + cbn. repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
    + intros v Hv. vm_compute in Hv |- *. intuition congruence.
    + intros v e He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_source. now apply Nat.eqb_eq, (proj2 He).
    + intros v e _ He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_target.
      destruct He as [He _]. cbn in He.
      destruct He as [<-|[<-|[<-|Hfalse]]]; [vm_compute; auto|vm_compute; auto|
        vm_compute; auto|contradiction].
  - intro v. rewrite Graph.of_pure_out. apply NoDup_filter.
    repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
Qed.

Example parallel_labels_same_component : components parallel = [[2; 1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example parallel_actual_labelled_trace :
  SearchRun.events parallel unrestricted [1]%positive =
    [Search.Enter 1 None; Search.Edge 10%nat 1 2 Search.Tree;
      Search.Enter 2 (Some (10%nat, 1)); Search.Edge 12%nat 2 1 Search.Back;
      Search.Exit 2 (Some 1); Search.Edge 11%nat 1 2 Search.Forward;
      Search.Exit 1 None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example finished_child_is_still_on_tarjan_stack :
  let s := SearchRun.apply_events Tarjan.visitor
    (firstn 5 (SearchRun.events parallel unrestricted [1]%positive)) Tarjan.initial in
  (Tarjan.stack s, FinSet.mem positive_encoding 2%positive (Tarjan.on_stack s),
    Map.get positive_encoding 2%positive (Tarjan.low s), Tarjan.emitted_rev s) =
    ([2; 1], true, Some 1, [])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Definition pending_cross :=
  prepare [1] [1; 2; 3] [(1, 2); (1, 3); (2, 1); (3, 2)].

(** A finished sibling remains on Tarjan's stack until its enclosing SCC is emitted. *)
Example pending_cross_ready : Prepared.ready pending_cross.
Proof.
  apply fixture_ready;
    [ repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
    | intros x Hin; vm_compute in Hin |- *; intuition congruence
    | repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
    | intros [a b] Hin; vm_compute in Hin |- *; intuition congruence ].
Qed.

Example cross_to_finished_pending_sibling : components pending_cross = [[3; 2; 1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_roots : Tarjan.compute distinct unrestricted [] = Scc.Result [] Map.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Definition unknown_within :=
  Scope.Make FinSet.empty (Some (FinSet.of_list positive_encoding [2; 3; 99]%positive)).

Example admitted_unknown_root_has_no_component :
  let r := Tarjan.compute nested unknown_within [99; 2; 2; 1; 99]%positive in
  (Scope.admits unknown_within 99%positive, Prepared.name_of nested 99%positive,
    Scc.components r, owner_list r [1; 2; 3; 4; 99]%positive) =
    (true, None, [[3; 2]], [None; Some 1; Some 1; None; None])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** Canonical owner storage is obtained for the actual arbitrary-scope visitor computation. *)
Example actual_scoped_owner_storage :
  Map.wf positive_encoding
    (Scc.comp_of (Tarjan.compute nested unknown_within [99; 2; 2; 1; 99]%positive)).
Proof.
  apply TarjanExact.compute_owners_wf.
Qed.

(** Scope rejection has a universal producer guarantee on the actual owner map. *)
Example actual_rejected_owner :
  Map.get positive_encoding 1%positive
    (Scc.comp_of (Tarjan.compute nested unknown_within [99; 2; 2; 1; 99]%positive)) = None.
Proof.
  apply TarjanExact.rejected_unowned.
  - exact (proj1 (proj2 (proj2 (proj2 fixtures_ready)))).
  - vm_compute. reflexivity.
Qed.

(** An admitted unknown ID is absent by the producer's valid-domain theorem. *)
Example actual_unknown_owner :
  Map.get positive_encoding 99%positive
    (Scc.comp_of (Tarjan.compute nested unknown_within [99; 2; 2; 1; 99]%positive)) = None.
Proof.
  pose proof (proj1 (proj2 (proj2 (proj2 fixtures_ready)))) as Hready.
  apply TarjanExact.unknown_unowned; [exact Hready|].
  intros [v [_ Hi]].
  pose proof (Prepared.name_of_id_of nested v 99%positive (proj2 (proj2 Hready)) Hi) as Hname.
  vm_compute in Hname. discriminate.
Qed.

(** The full empty-root SCC contract is available independently of preparation readiness. *)
Example empty_roots_exact : Scc.exact distinct unknown_within []
  (Tarjan.compute distinct unknown_within []).
Proof.
  apply TarjanExact.empty_roots_exact.
Qed.

(** Discovery ranks refer to the same visitor run that returns Tarjan's actual state. *)
Example actual_discovery_numbering :
  Map.get positive_encoding 3%positive (Tarjan.disc (snd (Cost.value
    (SearchRun.run_c nested Tarjan.visitor unknown_within [99; 2; 2; 1; 99]%positive
      Tarjan.initial)))) = Some 2%positive <->
  nth_error (Search.preorder (fst (Cost.value
    (SearchRun.run_c nested Tarjan.visitor unknown_within [99; 2; 2; 1; 99]%positive
      Tarjan.initial)))) (Nat.pred (Pos.to_nat 2%positive)) = Some 3%positive.
Proof.
  apply TarjanExact.discovery_index.
  exact (proj1 (proj2 (proj2 (proj2 fixtures_ready)))).
Qed.

Example separate_root_invocations_components :
  Scc.components (Tarjan.compute line unrestricted [3; 99; 1; 3]%positive) =
    [[4]; [3]; [2]; [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** Separate actual root invocations finish with no shared pending Tarjan vertices. *)
Example actual_multiple_root_stack_drained :
  Tarjan.stack (snd (Cost.value
    (SearchRun.run_c line Tarjan.visitor unrestricted [3; 99; 1; 3]%positive Tarjan.initial))) =
    [].
Proof.
  apply TarjanExact.stack_empty. exact (proj1 fixtures_ready).
Qed.

(** The actual restricted partition has complete scoped coverage for each queried ID. *)
Example actual_partition_coverage v :
  In v (concat (Scc.components (Tarjan.compute nested unknown_within
    [99; 2; 2; 1; 99]%positive))) <->
  Search.scoped_reachable nested unknown_within [99; 2; 2; 1; 99]%positive v.
Proof.
  apply TarjanExact.partition_complete. exact (proj1 (proj2 (proj2 (proj2 fixtures_ready)))).
Qed.

(** Each actual owner is the exact one-based position of its containing restricted component. *)
Example actual_one_based_owner v i :
  Map.get positive_encoding v (Scc.comp_of (Tarjan.compute nested unknown_within
    [99; 2; 2; 1; 99]%positive)) = Some i <->
  exists c, nth_error (Scc.components (Tarjan.compute nested unknown_within
    [99; 2; 2; 1; 99]%positive)) (Nat.pred (Pos.to_nat i)) = Some c /\ In v c.
Proof.
  apply TarjanExact.owners_exact. exact (proj1 (proj2 (proj2 (proj2 fixtures_ready)))).
Qed.

(** Every actual scoped reachable vertex has its proved component owner without a default index. *)
Example actual_reachable_vertex_has_owner v :
  Search.scoped_reachable nested unknown_within [99; 2; 2; 1; 99]%positive v ->
  exists i, Map.get positive_encoding v (Scc.comp_of (Tarjan.compute nested unknown_within
    [99; 2; 2; 1; 99]%positive)) = Some i.
Proof.
  apply TarjanExact.visited_has_component.
  exact (proj1 (proj2 (proj2 (proj2 fixtures_ready)))).
Qed.

(** The complete ready-only producer theorem proves the maximal nested-cycle partition. *)
Example nested_exact :
  Scc.exact nested unrestricted [1]%positive (Tarjan.compute nested unrestricted [1]%positive).
Proof.
  apply TarjanExact.compute_exact. exact (proj1 (proj2 (proj2 (proj2 fixtures_ready)))).
Qed.

(** The outer cycle and its nested cycle form one proved maximal mutual-reachability class. *)
Example nested_maximal_block : Scc.block nested unrestricted [1]%positive [4; 3; 2; 1]%positive.
Proof.
  apply TarjanExact.block_exact.
  - exact (proj1 (proj2 (proj2 (proj2 fixtures_ready)))).
  - vm_compute. now left.
Qed.

(** Exactness permits repeated roots and IDs that the scope admits but preparation does not name. *)
Example restricted_unknown_exact :
  Scc.exact nested unknown_within [99; 2; 2; 1; 99]%positive
    (Tarjan.compute nested unknown_within [99; 2; 2; 1; 99]%positive).
Proof.
  apply TarjanExact.compute_exact. exact (proj1 (proj2 (proj2 (proj2 fixtures_ready)))).
Qed.

(** Blocking a vertex keeps the complete scoped SCC contract rather than unrestricted coverage. *)
Example blocked_exact :
  Scc.exact diamond block_two [1; 2; 99]%positive
    (Tarjan.compute diamond block_two [1; 2; 99]%positive).
Proof.
  apply TarjanExact.compute_exact. exact (proj1 (proj2 fixtures_ready)).
Qed.

(** Independent actual root invocations satisfy every SCC specification field. *)
Example separate_roots_exact :
  Scc.exact line unrestricted [3; 99; 1; 3]%positive
    (Tarjan.compute line unrestricted [3; 99; 1; 3]%positive).
Proof.
  apply TarjanExact.compute_exact. exact (proj1 fixtures_ready).
Qed.

(** An empty graph with supplied unknown roots still satisfies every ready-only SCC field. *)
Example empty_graph_unknown_roots_exact :
  Scc.exact empty unrestricted [99; 99]%positive
    (Tarjan.compute empty unrestricted [99; 99]%positive).
Proof.
  apply TarjanExact.compute_exact.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 fixtures_ready)))))).
Qed.

(** Actual cross-component arcs decrease the observed owners of the two distinct cycles. *)
Example distinct_cross_owner_order i j :
  Map.get positive_encoding 2%positive
    (Scc.comp_of (Tarjan.compute distinct unrestricted [1]%positive)) = Some i ->
  Map.get positive_encoding 3%positive
    (Scc.comp_of (Tarjan.compute distinct unrestricted [1]%positive)) = Some j ->
    (j < i)%positive.
Proof.
  intros Hi Hj.
  apply (TarjanExact.reverse_topological distinct unrestricted [1]%positive
    2%positive (2, 3)%nat 3%positive i j).
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 fixtures_ready)))))).
  - exists 2%nat, 3%nat. vm_compute. intuition congruence.
  - exact Hi.
  - exact Hj.
  - vm_compute in Hi, Hj. inversion Hi; inversion Hj; subst. discriminate.
Qed.

Definition parallel_dag_graph :=
  Graph.of_pure [1] [1; 2]
    (fun v => filter (fun _ => Nat.eqb 1 v) [10; 11]) (fun _ => 1) (fun _ => 2).
Definition parallel_dag := Prepared.prepare nat_encoding parallel_dag_graph.

(** Parallel labels are distinct outgoing occurrences in a publicly prepared ready DAG. *)
Example parallel_dag_ready : Prepared.ready parallel_dag.
Proof.
  unfold parallel_dag, parallel_dag_graph.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - constructor.
    + repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
    + intros v Hv. vm_compute in Hv |- *. intuition congruence.
    + intros v e He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_source. now apply Nat.eqb_eq, (proj2 He).
    + intros v e _ _. rewrite Graph.of_pure_target. vm_compute. auto.
  - intro v. rewrite Graph.of_pure_out. apply NoDup_filter.
    repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
Qed.

Example parallel_dag_components : components parallel_dag = [[2]; [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example parallel_dag_actual_labels :
  SearchRun.events parallel_dag unrestricted [1]%positive =
    [Search.Enter 1 None; Search.Edge 10%nat 1 2 Search.Tree;
      Search.Enter 2 (Some (10%nat, 1)); Search.Exit 2 (Some 1);
      Search.Edge 11%nat 1 2 Search.Forward; Search.Exit 1 None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** Parallel-label exactness uses the same actual selected-label trace as the component producer. *)
Example parallel_dag_exact :
  Scc.exact parallel_dag unrestricted [1]%positive
    (Tarjan.compute parallel_dag unrestricted [1]%positive).
Proof.
  apply TarjanExact.compute_exact, parallel_dag_ready.
Qed.

End TarjanFixtures.
