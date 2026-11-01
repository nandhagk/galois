(** * Strongly connected component audit examples

    Exercise Tarjan audit traces and captured graph callbacks on small inputs.
    For example, a target receipt retains the edge and vertex returned by the callback.
    Builds on: GraphAuditSccAdequacy and GraphGRA1a. *)

From Stdlib Require Import List Bool PArith ZArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphAuditDfs GraphAuditScc
  GraphAuditSccAdequacy.
From Galois.Tests.Graph Require Import GraphGRA1a.
Import List.ListNotations.

(** * Boundary and callback receipts *)

(** Callbacks include their operands in one-item bodies. *)
Definition scc_example_callbacks : audit_dfs_callback_model nat nat nat :=
  AuditDfsCallbackModel nat nat nat
    (fun edge => (Graph.target example_graph edge, [200 + edge]))
    (fun vertex => (encode nat_encoding vertex, [300 + vertex])).

(** Empty region setup returns an empty SCC result and its terminal events. *)
Example scc_empty_region_boundary :
    snd (audit_scc_within_counted (prepare nat_encoding empty_graph) []) =
      [AuditTarjanCase 14; AuditTarjanCase 12; AuditTarjanOutput 0 0] /\
    fst (audit_scc_within_counted (prepare nat_encoding empty_graph) []) =
      scc_within (prepare nat_encoding empty_graph) [].
Proof.
  split; reflexivity.
Qed.

(** Recognize the actual edge, returned vertex, and callback body in a target receipt. *)
Definition scc_target_receipt (edge vertex : nat)
    (event : audit_tarjan_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match event with
  | (AuditTarjanTarget actual_edge actual_vertex,
      [AuditGraphTargetCapture _ _ _ captured_edge captured_vertex [body]]) =>
    Nat.eqb edge actual_edge && Nat.eqb vertex actual_vertex &&
    Nat.eqb edge captured_edge && Nat.eqb vertex captured_vertex && Nat.eqb body (200 + edge)
  | _ => false
  end.

(** A real edge receipt retains its actual target and rejects a different target. *)
Example scc_target_callback_receipt :
    existsb (scc_target_receipt 10 2)
      (snd (audit_scc_source_counted (prepare nat_encoding example_graph)
        scc_example_callbacks [0; 1; 2; 3])) = true /\
    existsb (scc_target_receipt 10 3)
      (snd (audit_scc_source_counted (prepare nat_encoding example_graph)
        scc_example_callbacks [0; 1; 2; 3])) = false.
Proof.
  split; reflexivity.
Qed.

(** Recognize a region insertion and the encoder result and body used for that insertion. *)
Definition scc_encoder_receipt (vertex : nat)
    (event : audit_tarjan_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match event with
  | (AuditTarjanSet actual _, [AuditGraphEncodeCapture _ _ _ captured code [body]]) =>
    Nat.eqb vertex actual && Nat.eqb vertex captured &&
    Pos.eqb code (encode nat_encoding vertex) && Nat.eqb body (300 + vertex)
  | _ => false
  end.

(** A real region insertion retains its encoder operand and excludes an absent vertex. *)
Example scc_encoder_callback_receipt :
    existsb (scc_encoder_receipt 2)
      (snd (audit_scc_source_counted (prepare nat_encoding example_graph)
        scc_example_callbacks [0; 1; 2; 3])) = true /\
    existsb (scc_encoder_receipt 4)
      (snd (audit_scc_source_counted (prepare nat_encoding example_graph)
        scc_example_callbacks [0; 1; 2; 3])) = false.
Proof.
  split; reflexivity.
Qed.

(** One fuel step keeps the example's work small enough to compute its source bounds. *)
Definition scc_tiny_index : prepared nat_encoding empty_graph :=
  Prepared Map.empty Map.empty 1%positive.

(** The tiny graph's callbacks retain their actual returned operands. *)
Definition scc_tiny_callbacks : audit_dfs_callback_model nat nat nat :=
  AuditDfsCallbackModel nat nat nat
    (fun edge => (edge, [200 + edge]))
    (fun vertex => (encode nat_encoding vertex, [300 + vertex])).

(** A nonempty traversal fits its event budget and exceeds zero events. *)
Example scc_tiny_event_budget_accepts :
    Nat.leb (length (snd (audit_scc_within_counted scc_tiny_index [0])))
      (audit_tarjan_input_event_bound scc_tiny_index [0]) = true /\
    Nat.leb (length (snd (audit_scc_within_counted scc_tiny_index [0]))) 0 = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A nonempty captured traversal fits the source budget with its actual callback work. *)
Example scc_tiny_source_budget_accepts :
    let events := snd (audit_scc_source_counted scc_tiny_index scc_tiny_callbacks [0]) in
    Nat.leb (audit_scc_source_work (fun _ => 1) events)
      (audit_scc_source_budget nat_encoding empty_graph scc_tiny_index [0] +
        audit_scc_source_body_work (fun _ => 1) events) = true.
Proof.
  apply Nat.leb_le; eapply Nat.le_trans with (m := 100 * 1000).
  - apply Nat2Z.inj_le; vm_compute; easy.
  - set (count := audit_tarjan_input_event_bound scc_tiny_index [0]).
    assert (Hcount : 30 <= count).
    { unfold count, audit_tarjan_input_event_bound, scc_tiny_index; cbn; lia. }
    change (100 * 1000 <= 1024 * S count * S count + count *
      (512 + 64 * Nat.max (audit_dfs_input_width nat_encoding empty_graph scc_tiny_index [0])
        (Pos.size_nat (Pos.of_succ_nat (2 + length [0] * S (Pos.to_nat (fuel scc_tiny_index)))))) +
      audit_scc_source_body_work (fun _ => 1)
        (snd (audit_scc_source_counted scc_tiny_index scc_tiny_callbacks [0]))).
    nia.
Qed.

(** A nonempty counted traversal fits the original-input model budget. *)
Example scc_tiny_model_budget_accepts :
    let events := snd (audit_scc_within_counted scc_tiny_index [0]) in
    Nat.leb (audit_tarjan_model_work nat_encoding events)
      (audit_tarjan_input_budget nat_encoding empty_graph scc_tiny_index [0]) = true.
Proof.
  apply Nat.leb_le; eapply Nat.le_trans with (m := 100 * 1000).
  - apply Nat2Z.inj_le; vm_compute; easy.
  - set (count := audit_tarjan_input_event_bound scc_tiny_index [0]).
    assert (Hcount : 30 <= count).
    { unfold count, audit_tarjan_input_event_bound, scc_tiny_index; cbn; lia. }
    change (100 * 1000 <= 128 * S count * S count + count *
      (140 + 12 * Nat.max (audit_dfs_input_width nat_encoding empty_graph scc_tiny_index [0])
        (CollectionsAuditCost.audit_key_bits_weight
          (Pos.of_succ_nat (2 + length [0] * S (Pos.to_nat (fuel scc_tiny_index))))))).
    nia.
Qed.

(** A nonempty captured traversal fits the supplied callback budgets. *)
Example scc_tiny_external_budget_accepts :
    let events := snd (audit_scc_source_counted scc_tiny_index scc_tiny_callbacks [0]) in
    Nat.leb (audit_scc_source_work (fun _ => 1) events)
      (audit_scc_source_budget nat_encoding empty_graph scc_tiny_index [0] +
        audit_scc_source_external_budget (fun _ => 1) (fun _ => 1) events) = true.
Proof.
  apply Nat.leb_le; eapply Nat.le_trans with (m := 100 * 1000).
  - apply Nat2Z.inj_le; vm_compute; easy.
  - set (count := audit_tarjan_input_event_bound scc_tiny_index [0]).
    assert (Hcount : 30 <= count).
    { unfold count, audit_tarjan_input_event_bound, scc_tiny_index; cbn; lia. }
    change (100 * 1000 <= 1024 * S count * S count + count *
      (512 + 64 * Nat.max (audit_dfs_input_width nat_encoding empty_graph scc_tiny_index [0])
        (Pos.size_nat (Pos.of_succ_nat (2 + length [0] * S (Pos.to_nat (fuel scc_tiny_index)))))) +
      audit_scc_source_external_budget (fun _ => 1) (fun _ => 1)
        (snd (audit_scc_source_counted scc_tiny_index scc_tiny_callbacks [0]))).
    nia.
Qed.

(** An importing client can use every contracted SCC adequacy theorem. *)
Example scc_all_contract_witnesses :
    audit_tarjan_helpers_erasure_statement /\ audit_tarjan_helpers_event_bound_statement /\
    audit_scc_within_counted_statement /\ audit_scc_within_nested_statement /\
    audit_scc_within_nested_total_statement /\ audit_scc_reverse_run_statement /\
    audit_scc_source_statement /\ audit_scc_min_source_model_statement /\
    audit_scc_source_primitive_correspondence_statement /\ audit_scc_source_library_obligations /\
    audit_scc_source_adapted_statement /\ audit_scc_source_contract_statement.
Proof.
  split; [exact audit_tarjan_helpers_erasure|].
  split; [exact audit_tarjan_helpers_event_bound|].
  split; [exact audit_scc_within_counted_correct|].
  split; [exact audit_scc_within_nested_holds|].
  split; [exact audit_scc_within_nested_total_holds|].
  split; [exact audit_scc_reverse_run_holds|].
  split; [exact audit_scc_source_correct|].
  split; [exact audit_scc_min_source_model_holds|].
  split; [exact audit_scc_source_primitive_correspondence_holds|].
  split; [exact audit_scc_source_primitives_correct|].
  split; [exact audit_scc_source_adapted_correct|exact audit_scc_source_contract_correct].
Qed.

(** A two-vertex cycle causes a pop to compare different keys before reaching its root. *)
Definition scc_cycle_graph : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1];
     Graph.out := fun v => if Nat.eqb v 0 then [1] else if Nat.eqb v 1 then [0] else [];
     Graph.source := fun edge => if Nat.eqb edge 1 then 0 else 1;
     Graph.target := fun edge => edge |}.

(** Cycle callbacks retain the returned key and the actual one-item bodies. *)
Definition scc_cycle_callbacks : audit_dfs_callback_model nat nat nat :=
  AuditDfsCallbackModel nat nat nat
    (fun edge => (Graph.target scc_cycle_graph edge, [200 + edge]))
    (fun vertex => (encode nat_encoding vertex, [300 + vertex])).

(** Recognize a comparison event with both encoder receipts and the actual result. *)
Definition scc_compare_receipt (left right : nat) (result : bool)
    (event : audit_tarjan_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match event with
  | (AuditTarjanHelper (THCompare actual_left actual_right actual_result),
      [AuditGraphEncodeCapture _ _ _ captured_left left_code [left_body];
       AuditGraphEncodeCapture _ _ _ captured_right right_code [right_body]]) =>
    Nat.eqb left actual_left && Nat.eqb right actual_right && Bool.eqb result actual_result &&
    Nat.eqb left captured_left && Nat.eqb right captured_right &&
    Pos.eqb left_code (encode nat_encoding left) &&
    Pos.eqb right_code (encode nat_encoding right) &&
    Nat.eqb left_body (300 + left) && Nat.eqb right_body (300 + right)
  | _ => false
  end.

(** A cycle records the unequal and equal pop comparisons with the actual callback bodies. *)
Example scc_cycle_comparison_receipts :
    let events := snd (audit_scc_source_counted (prepare nat_encoding scc_cycle_graph)
      scc_cycle_callbacks [0; 1]) in
    existsb (scc_compare_receipt 1 0 false) events = true /\
    existsb (scc_compare_receipt 0 0 true) events = true /\
    existsb (scc_compare_receipt 1 0 true) events = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The same cycle returns one component and a persistent owner entry for each member. *)
Example scc_cycle_returned_owner_map :
    let result := fst (audit_scc_source_counted (prepare nat_encoding scc_cycle_graph)
      scc_cycle_callbacks [0; 1]) in
    components result = [[1; 0]] /\
    Map.get nat_encoding 0 (comp_of result) = Some 1%positive /\
    Map.get nat_encoding 1 (comp_of result) = Some 1%positive /\
    Map.get nat_encoding 2 (comp_of result) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The nested tiny traversal fits its internal budget plus its actual callback-body work. *)
Example scc_tiny_nested_total_budget_accepts :
    let events := snd (audit_scc_within_nested_counted scc_tiny_index scc_tiny_callbacks [0]) in
    Nat.leb (audit_tarjan_nested_total_work nat_encoding (fun _ => 1) events)
      (audit_tarjan_input_budget nat_encoding empty_graph scc_tiny_index [0] +
        audit_tarjan_nested_body_work (fun _ => 1) events) = true.
Proof.
  apply Nat.leb_le; eapply Nat.le_trans with (m := 100 * 1000).
  - apply Nat2Z.inj_le; vm_compute; easy.
  - set (count := audit_tarjan_input_event_bound scc_tiny_index [0]).
    assert (Hcount : 30 <= count).
    { unfold count, audit_tarjan_input_event_bound, scc_tiny_index; cbn; lia. }
    change (100 * 1000 <= 128 * S count * S count + count *
      (140 + 12 * Nat.max (audit_dfs_input_width nat_encoding empty_graph scc_tiny_index [0])
        (CollectionsAuditCost.audit_key_bits_weight
          (Pos.of_succ_nat (2 + length [0] * S (Pos.to_nat (fuel scc_tiny_index)))))) +
      audit_tarjan_nested_body_work (fun _ => 1)
        (snd (audit_scc_within_nested_counted scc_tiny_index scc_tiny_callbacks [0]))).
    nia.
Qed.

(** Popping an empty pending stack leaves both persistent maps unchanged. *)
Example scc_empty_pop_boundary :
    @audit_tarjan_pop_counted nat nat nat_encoding 0 1%positive [] Map.empty Map.empty =
      (([], [], Map.empty, Map.empty), [THCase 2]).
Proof.
  reflexivity.
Qed.

(** Popping through a root retains the suffix and records each popped member in the owner map. *)
Example scc_pop_returned_maps :
    let links := Map.set nat_encoding 0 2%positive
      (Map.set nat_encoding 1 3%positive Map.empty) in
    let '(answer, _) := @audit_tarjan_pop_counted nat nat nat_encoding 0 4%positive
      [1; 0; 2] links Map.empty in
    let '(members, tail, remaining, owners) := answer in
    members = [1; 0] /\ tail = [2] /\
    Map.get nat_encoding 0 remaining = None /\ Map.get nat_encoding 1 remaining = None /\
    Map.get nat_encoding 0 owners = Some 4%positive /\
    Map.get nat_encoding 1 owners = Some 4%positive /\ Map.get nat_encoding 2 owners = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Positive minimum inspects both operand bits and returns the smaller operand. *)
Example scc_positive_minimum_capture :
    fst (audit_scc_min_source_model 3%positive 2%positive) = 2%positive /\
    length (snd (audit_scc_min_source_model 3%positive 2%positive)) = 2.
Proof.
  split; reflexivity.
Qed.
