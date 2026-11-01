(** * Virtual-root audit examples

    Exercise entry deduplication and the callbacks used by virtual search.
    For example, a repeated entry produces a membership hit on the persisted set.
    Builds on: the virtual audit adequacy claims and graph fixtures. *)

From Stdlib Require Import List PArith PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphSemiDominators
  GraphAuditBase GraphAuditDfs GraphAuditVirtual GraphAuditVirtualAdapter
  GraphAuditVirtualAdapterAdequacy
  GraphAuditVirtualAdequacy.
From Galois.Tests.Graph Require Import GraphGRA1a.
Import List.ListNotations.

(** * Entry and callback observations *)

Example virtual_entries_empty_boundary :
  @audit_virtual_entries_counted nat nat nat_encoding FinSet.empty [] =
    ([], [AuditVirtualCase 0]).
Proof.
  reflexivity.
Qed.

Example virtual_entries_duplicate_observation :
  @audit_virtual_entries_counted nat nat nat_encoding FinSet.empty [1; 1] =
    ([1], [AuditVirtualCase 1; AuditVirtualMem 1 FinSet.empty false; AuditVirtualCase 3;
      AuditVirtualAdd 1 FinSet.empty; AuditVirtualCase 1;
      AuditVirtualMem 1 (FinSet.add nat_encoding 1 FinSet.empty) true;
      AuditVirtualCase 2; AuditVirtualCase 0]).
Proof.
  reflexivity.
Qed.

(** The callback body identifies the exact vertex or edge passed by virtual search. *)
Definition virtual_example_callbacks : audit_virtual_base_callbacks nat nat nat :=
  AuditVirtualBaseCallbacks nat nat nat
    (fun v => (Graph.out example_graph v, [100 + v]))
    (fun e => (Graph.target example_graph e, [200 + e]))
    (fun v => (encode nat_encoding v, [300 + v])).

Example virtual_full_callback_observations :
  audit_virtual_full_target virtual_example_callbacks (inl 10) =
    (inl 2, [VirtualFullCase 2; VirtualFullTarget 10 2 [210]]) /\
  audit_virtual_full_encode virtual_example_callbacks (inl 2) =
    (xO (encode nat_encoding 2), [VirtualFullCase 4;
      VirtualFullEncode 2 (encode nat_encoding 2) [302]]) /\
  audit_virtual_full_source (fun e : nat => (Graph.source example_graph e, [400 + e])) (inl 10) =
    (inl 0, [VirtualFullCase 6; VirtualFullSource 10 0 [410]]).
Proof.
  repeat split; reflexivity.
Qed.

Example virtual_entries_full_budget_accepts :
  let '(result, events) := audit_virtual_entries_full_counted
    (fun v : nat => (encode nat_encoding v, [300 + v])) FinSet.empty [1; 1; 2] in
  result = [1; 2] /\
  Nat.leb (audit_virtual_entries_full_internal_work events)
    (audit_virtual_entries_full_budget nat_encoding [1; 1; 2]) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Recognize a target callback inside the actual preparation source trace. *)
Definition virtual_target_receipt
    (event : audit_prepare_source_event (nat + unit) (nat + nat)
      (audit_virtual_full_call nat nat nat)) : bool :=
  match event with
  | PrepareSourceTarget (inl 10) (inl 2)
      [VirtualFullCase 2; VirtualFullTarget 10 2 [210]] => true
  | _ => false
  end.

Example virtual_source_target_receipt :
  let '(_, (_, (events, _))) :=
    audit_virtual_source_search nat_encoding example_graph virtual_example_callbacks in
  existsb virtual_target_receipt events = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example virtual_source_search_nontrivial_result :
  let '(prepared, (result, _)) :=
    audit_virtual_source_search nat_encoding example_graph virtual_example_callbacks in
  prepared = virtual_prepared (prepare nat_encoding example_graph) /\
  result = virtual_dfs (prepare nat_encoding example_graph).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example virtual_model_entry_budget_accepts :
  let '(_, events) := @audit_virtual_entries_counted nat nat nat_encoding FinSet.empty [1; 1; 2] in
  Nat.leb (audit_virtual_entries_work nat_encoding events)
    (audit_virtual_entries_budget nat_encoding [1; 1; 2]) = true /\
  Nat.leb (audit_virtual_entries_work nat_encoding events) 0 = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The fixture callbacks return the graph and encoding results alongside their actual bodies. *)
Lemma virtual_example_callbacks_erase :
  audit_virtual_base_callbacks_erase nat_encoding example_graph virtual_example_callbacks.
Proof.
  repeat split; intros; reflexivity.
Qed.

Example virtual_source_budget_accepts_nontrivial :
  let '(_, (_, (prepare_events, dfs_events))) :=
    audit_virtual_source_search nat_encoding example_graph virtual_example_callbacks in
  let weight := fun item => audit_virtual_full_internal_event_work item +
    audit_virtual_full_body_event_work (fun _ => 1) item in
  Nat.leb (audit_prepare_source_work weight prepare_events +
    audit_dfs_source_work weight dfs_events)
    (audit_virtual_source_search_budget nat_encoding example_graph +
      audit_prepare_source_body_work (audit_virtual_full_body_event_work (fun _ => 1))
        prepare_events +
      audit_dfs_source_body_work (audit_virtual_full_body_event_work (fun _ => 1))
        dfs_events) = true.
Proof.
  pose proof (audit_virtual_source_search_holds nat nat nat nat_encoding example_graph
    (prepare nat_encoding example_graph) virtual_example_callbacks (fun _ => 1)
    virtual_example_callbacks_erase) as Hrun.
  destruct (audit_virtual_source_search nat_encoding example_graph virtual_example_callbacks)
    as [vp [result [prepare_events dfs_events]]] eqn:Hsearch.
  cbv beta iota zeta in Hrun |- *.
  apply Nat.leb_le; exact (proj2 (proj2 Hrun)).
Qed.

Example virtual_model_search_budget_accepts_nontrivial :
  Nat.leb (audit_virtual_search_work nat_encoding example_graph)
    (audit_virtual_search_budget nat_encoding example_graph) = true.
Proof.
  apply Nat.leb_le; exact (audit_virtual_search_bound nat nat nat_encoding example_graph).
Qed.

Example virtual_callback_budget_operands :
  @audit_virtual_adapter_call_budget nat nat nat (fun v => 10 + v) (fun v => 20 + v)
    (fun e => 30 + e) (VirtualFullOut 2 [10] [102]) = 22 /\
  @audit_virtual_adapter_call_budget nat nat nat (fun v => 10 + v) (fun v => 20 + v)
    (fun e => 30 + e) (VirtualFullTarget 10 2 [210]) = 40 /\
  @audit_virtual_adapter_call_budget nat nat nat (fun v => 10 + v) (fun v => 20 + v)
    (fun e => 30 + e)
    (VirtualFullEntry (VirtualEntriesSet (AuditSetMem 2 3%positive FinSet.empty false [302] []))) =
      12.
Proof.
  repeat split; reflexivity.
Qed.

(** Every fixture callback records exactly one unit-cost body event. *)
Lemma virtual_example_adapters :
  audit_graph_external_callback_adapter (audit_virtual_base_encode virtual_example_callbacks)
    (fun _ => 1) (fun _ _ _ _ => True) (fun _ => 1) /\
  audit_graph_external_callback_adapter (audit_virtual_base_out virtual_example_callbacks)
    (fun _ => 1) (fun _ _ _ _ => True) (fun _ => 1) /\
  audit_graph_external_callback_adapter (audit_virtual_base_target virtual_example_callbacks)
    (fun _ => 1) (fun _ _ _ _ => True) (fun _ => 1).
Proof.
  split; [|split]; constructor; intros arg result body Hcall;
    cbn [virtual_example_callbacks audit_virtual_base_encode audit_virtual_base_out
      audit_virtual_base_target] in Hcall; inversion Hcall; subst body; cbn; auto.
Qed.

Example virtual_adapted_budget_accepts_nontrivial :
  let '(_, (_, (prepare_events, dfs_events))) :=
    audit_virtual_source_search nat_encoding example_graph virtual_example_callbacks in
  let weight := fun item => audit_virtual_full_internal_event_work item +
    audit_virtual_full_body_event_work (fun _ => 1) item in
  let budget := audit_virtual_adapter_call_budget (fun _ => 1) (fun _ => 1) (fun _ => 1) in
  Nat.leb (audit_prepare_source_work weight prepare_events +
    audit_dfs_source_work weight dfs_events)
    (audit_virtual_source_search_budget nat_encoding example_graph +
      audit_prepare_source_body_work budget prepare_events +
      audit_dfs_source_body_work budget dfs_events) = true.
Proof.
  destruct virtual_example_adapters as [Hencode [Hout Htarget]].
  pose proof (audit_virtual_source_search_adapted_holds nat nat nat nat_encoding example_graph
    (prepare nat_encoding example_graph) virtual_example_callbacks (fun _ => 1)
    (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) virtual_example_callbacks_erase Hencode Hout Htarget)
    as Hrun.
  destruct (audit_virtual_source_search nat_encoding example_graph virtual_example_callbacks)
    as [vp [result [prepare_events dfs_events]]] eqn:Hsearch.
  cbv beta iota zeta in Hrun |- *.
  apply Nat.leb_le; exact (proj2 (proj2 Hrun)).
Qed.

(** A real parent and a synthetic parent exercise both erasure branches. *)
Definition virtual_parent_fixture : Map.t (nat + unit) (nat + unit) :=
  Map.set (virtual_encoding nat_encoding) (inr tt) (inl 2)
    (Map.set (virtual_encoding nat_encoding) (inl 1) (inl 2) Map.empty).

Example virtual_parent_erasure_budgets_accept :
  let '(result, events) := audit_erase_virtual_counted nat_encoding virtual_parent_fixture in
  let '(nested, nested_events) := audit_erase_virtual_nested
    (fun v : nat => (encode nat_encoding v, [v])) virtual_parent_fixture in
  Map.get nat_encoding 1 result = Some 2 /\
  Map.get nat_encoding 1 nested = Some 2 /\
  Nat.leb (audit_erase_virtual_work nat_encoding events)
    (audit_erase_virtual_budget nat_encoding virtual_parent_fixture) = true /\
  Nat.leb (audit_erase_nested_work (fun _ => 1) nested_events)
    (audit_erase_nested_budget nat_encoding virtual_parent_fixture +
      audit_erase_nested_body_work (fun _ => 1) nested_events) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
