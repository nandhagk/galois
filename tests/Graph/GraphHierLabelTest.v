(** * Parallel labels through hierarchy and reducibility

    Distinct labels on the same endpoints survive preparation and actual DFS events.
    For example, the second edge from 1 to 2 is Forward after the first selects the tree.
    Builds on: GraphSearchOrder, GraphHier, GraphWeakOrder, GraphLoopForest and GraphReducibility. *)

From Stdlib Require Import List Arith PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchOrder GraphHierSpec GraphHier GraphHierExact GraphWeakOrder GraphLoopForest
  GraphDomSpec GraphCheckDom GraphCheckWto GraphReducibility.
Import List.ListNotations.
Open Scope positive_scope.

Module ParallelLabels.

Inductive edge :=
  | First
  | Later
  | ReturnFirst
  | ReturnLater.

Definition source e :=
  match e with
  | First | Later => 1%nat
  | ReturnFirst | ReturnLater => 2%nat
  end.

Definition target e :=
  match e with
  | First | Later => 2%nat
  | ReturnFirst | ReturnLater => 1%nat
  end.

Definition outgoing v :=
  match v with
  | 1%nat => [First; Later]
  | 2%nat => [ReturnFirst; ReturnLater]
  | _ => []
  end.

Definition graph := Graph.of_pure [1%nat] [1%nat; 2%nat] outgoing source target.
Definition prepared := Prepared.prepare nat_encoding graph.
Definition scope := Scope.Make FinSet.empty None.
Definition parents := Map.of_list positive_encoding [(2, 1)].
Definition tree := DomCheck.of_parents prepared parents.

Example fixture_ready : Prepared.ready prepared.
Proof.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - unfold graph. constructor.
    + vm_compute. repeat (apply NoDup_cons; [cbn; intuition congruence|]).
      apply NoDup_nil.
    + intros v Hin. vm_compute in Hin |- *. tauto.
    + intros v e Hin. rewrite Graph.of_pure_out in Hin.
      rewrite Graph.of_pure_source.
      destruct v as [|[|[|v]]]; destruct e; cbn in Hin |- *; intuition congruence.
    + intros v e Hv Hin. rewrite Graph.of_pure_target.
      destruct e; vm_compute; auto.
  - intro v. unfold graph. rewrite Graph.of_pure_out.
    destruct v as [|[|[|v]]]; cbn;
      repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
Qed.

Example tree_exact : Dom.exact prepared tree.
Proof.
  apply DomCheck.check_sound; [exact fixture_ready|apply Map.wf_of_list|].
  vm_compute. reflexivity.
Qed.

Example distinct_labels_same_endpoints :
  First <> Later /\
  Graph.source graph First = Graph.source graph Later /\
  Graph.target graph First = Graph.target graph Later.
Proof.
  vm_compute. repeat split; discriminate.
Qed.

Example prepared_occurrences_retained :
  Prepared.succ_edges prepared 1 = [(First, 2); (Later, 2)] /\
  Prepared.pred_edges prepared 2 = [(First, 1); (Later, 1)] /\
  Prepared.succ_edges prepared 2 = [(ReturnFirst, 1); (ReturnLater, 1)].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example actual_labelled_trace :
  SearchRun.events prepared scope [1] =
    [Search.Enter 1 None;
     Search.Edge First 1 2 Search.Tree;
     Search.Enter 2 (Some (First, 1));
     Search.Edge ReturnFirst 2 1 Search.Back;
     Search.Edge ReturnLater 2 1 Search.Back;
     Search.Exit 2 (Some 1);
     Search.Edge Later 1 2 Search.Forward;
     Search.Exit 1 None].
Proof.
  vm_compute. reflexivity.
Qed.

Example selected_label_retained :
  Map.get positive_encoding 2 (Search.parent_edge (SearchRun.dfs prepared scope [1])) =
    Some (First, 1).
Proof.
  vm_compute. reflexivity.
Qed.

(** Endpoint classification alone cannot observe the later label's Forward event. *)
Example endpoint_classification_control :
  Search.classify (SearchRun.dfs prepared scope [1]) 1 2 = Some Search.Tree /\
  In (Search.Edge Later 1 2 Search.Forward) (SearchRun.events prepared scope [1]).
Proof.
  rewrite actual_labelled_trace. vm_compute. split; [reflexivity|tauto].
Qed.

Example later_label_contract_client :
  Prepared.arc prepared 1 Later 2 /\
  Scope.admits scope 1 = true /\ Scope.admits scope 2 = true /\
  SearchOrder.labelled_kind (SearchRun.dfs prepared scope [1]) Later 1 2 Search.Forward.
Proof.
  apply SearchOrder.classify_spec; [exact fixture_ready|].
  rewrite actual_labelled_trace. cbn. tauto.
Qed.

Example actual_hierarchy :
  HierRun.compute prepared scope [1] =
    Hier.Cons (Hier.Component 1 (Hier.Cons (Hier.Vertex 2) Hier.Nil)) Hier.Nil.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_weak_order :
  WeakOrder.compute prepared [1] = [Wto.WOpen 1; Wto.WVertex 2; Wto.WClose].
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_loop_ownership :
  let loops := LoopForest.compute prepared [1] in
  Loops.headers loops = [1] /\
  Map.get positive_encoding 1 (Loops.loop_parent loops) = None /\
  Map.get positive_encoding 1 (Loops.innermost loops) = Some 1 /\
  Map.get positive_encoding 2 (Loops.innermost loops) = Some 1.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example actual_weak_order_accepts :
  WtoCheck.check prepared [1] (WeakOrder.compute prepared [1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_hierarchy_exact :
  Hier.exact prepared scope [1] (HierRun.compute prepared scope [1]).
Proof.
  apply HierExact.compute_exact, fixture_ready.
Qed.

Example actual_weak_order_valid : Wto.valid prepared [1] (WeakOrder.compute prepared [1]).
Proof.
  apply WeakOrder.compute_valid, fixture_ready.
Qed.

Example actual_reducer_accepts : Reducibility.test prepared tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example missing_dominance_rejects :
  Reducibility.test prepared (Dom.Tree Map.empty Map.empty Map.empty) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** Both return labels participate in the real reducer's Back-event contract. *)
Example both_return_labels_checked :
  In (Search.Edge ReturnFirst 2 1 Search.Back) (SearchRun.events prepared scope [1]) /\
  In (Search.Edge ReturnLater 2 1 Search.Back) (SearchRun.events prepared scope [1]) /\
  Reducibility.dominates tree 1 2 = true.
Proof.
  split; [rewrite actual_labelled_trace; cbn; tauto|].
  split; [rewrite actual_labelled_trace; cbn; tauto|].
  apply (proj1 (Reducibility.test_events prepared tree) actual_reducer_accepts
    ReturnLater 2 1).
  change (In (Search.Edge ReturnLater 2 1 Search.Back) (SearchRun.events prepared scope [1])).
  rewrite actual_labelled_trace. cbn. tauto.
Qed.

Example actual_semantically_reducible : reducible (Prepared.graph prepared).
Proof.
  apply (Reducibility.reducible_b_sound prepared tree fixture_ready tree_exact).
  exact actual_reducer_accepts.
Qed.

End ParallelLabels.
Import ParallelLabels.
