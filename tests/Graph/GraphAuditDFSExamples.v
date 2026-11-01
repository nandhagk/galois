(** * Depth-first search audit examples

    Exercise counted traversal boundaries and captured callback operands.
    For example, a target receipt retains the edge, returned vertex and callback body.
    Builds on: GraphAuditDfsAdequacy and the graph fixtures. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditDfs
  GraphAuditDfsAdequacy.
From Galois.Tests.Graph Require Import GraphGRA1a.
Import List.ListNotations.

(** The fixture records operands in each target and encoder callback body. *)
Definition dfs_example_callbacks : audit_dfs_callback_model nat nat nat :=
  AuditDfsCallbackModel nat nat nat
    (fun edge => (Graph.target example_graph edge, [200 + edge]))
    (fun vertex => (encode nat_encoding vertex, [300 + vertex])).

Example dfs_empty_roots_boundary :
    snd (audit_dfs_counted (prepare nat_encoding empty_graph) FinSet.empty []) =
      [AuditDfsCase 10] /\
    fst (audit_dfs_counted (prepare nat_encoding empty_graph) FinSet.empty []) =
      dfs (prepare nat_encoding empty_graph) FinSet.empty [].
Proof.
  split; reflexivity.
Qed.

Example dfs_blocked_root_boundary :
    snd (audit_dfs_root_counted (prepare nat_encoding example_graph)
      (FinSet.add nat_encoding 2 FinSet.empty) dfs_initial 2) =
      [AuditDfsMember 2 (FinSet.add nat_encoding 2 FinSet.empty) true;
       AuditDfsMember 2 FinSet.empty false; AuditDfsCase 8].
Proof.
  reflexivity.
Qed.

(** Recognize a target event with matching operand, result, and callback body. *)
Definition dfs_target_receipt (edge vertex : nat)
    (event : audit_dfs_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match event with
  | (AuditDfsFullTarget actual_edge actual_vertex,
      [AuditGraphTargetCapture _ _ _ captured_edge captured_vertex [body]]) =>
    Nat.eqb edge actual_edge && Nat.eqb vertex actual_vertex &&
    Nat.eqb edge captured_edge && Nat.eqb vertex captured_vertex && Nat.eqb body (200 + edge)
  | _ => false
  end.

Example dfs_nontrivial_capture_operands :
    existsb (dfs_target_receipt 10 2)
      (snd (audit_dfs_source_counted (prepare nat_encoding example_graph)
        dfs_example_callbacks FinSet.empty [0])) = true /\
    existsb (dfs_target_receipt 10 3)
      (snd (audit_dfs_source_counted (prepare nat_encoding example_graph)
        dfs_example_callbacks FinSet.empty [0])) = false.
Proof.
  split; reflexivity.
Qed.

(** Recognize a membership event with matching encoder operand, code, and body. *)
Definition dfs_encoder_receipt (vertex : nat)
    (event : audit_dfs_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match event with
  | (AuditDfsFullMember actual _ _,
      [AuditGraphEncodeCapture _ _ _ captured code [body]]) =>
    Nat.eqb vertex actual && Nat.eqb vertex captured &&
    Pos.eqb code (encode nat_encoding vertex) && Nat.eqb body (300 + vertex)
  | _ => false
  end.

Example dfs_encoder_capture_operand :
    existsb (dfs_encoder_receipt 0)
      (snd (audit_dfs_source_counted (prepare nat_encoding example_graph)
        dfs_example_callbacks FinSet.empty [0])) = true /\
    existsb (dfs_encoder_receipt 4)
      (snd (audit_dfs_source_counted (prepare nat_encoding example_graph)
        dfs_example_callbacks FinSet.empty [0])) = false.
Proof.
  split; reflexivity.
Qed.

Example dfs_full_and_nested_nontrivial_match :
    fst (audit_dfs_full_counted (prepare nat_encoding example_graph) FinSet.empty [0]) =
      dfs (prepare nat_encoding example_graph) FinSet.empty [0] /\
    map fst (snd (audit_dfs_nested_counted (prepare nat_encoding example_graph)
      dfs_example_callbacks FinSet.empty [0])) =
      snd (audit_dfs_full_counted (prepare nat_encoding example_graph) FinSet.empty [0]).
Proof.
  split; reflexivity.
Qed.

(** * Bounded source and public theorem witnesses *)

(** A one-step index exercises bounded source traversal. *)
Definition dfs_tiny_index : prepared nat_encoding empty_graph :=
  Prepared Map.empty Map.empty 1%positive.

(** Each tiny callback records a one-item body. *)
Definition dfs_tiny_callbacks : audit_dfs_callback_model nat nat nat :=
  AuditDfsCallbackModel nat nat nat
    (fun edge => (edge, [200 + edge]))
    (fun vertex => (encode nat_encoding vertex, [300 + vertex])).

Example dfs_tiny_source_budget_accepts :
    let events := snd (audit_dfs_source_counted dfs_tiny_index dfs_tiny_callbacks FinSet.empty
      [0]) in
    Nat.leb (audit_dfs_source_work (fun _ => 1) events)
      (audit_dfs_source_budget nat_encoding empty_graph dfs_tiny_index [0] +
        audit_dfs_source_body_work (fun _ => 1) events) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dfs_tiny_model_budgets_accept :
    let counted := snd (audit_dfs_counted dfs_tiny_index FinSet.empty [0]) in
    let full := snd (audit_dfs_full_counted dfs_tiny_index FinSet.empty [0]) in
    Nat.leb (audit_dfs_model_work nat_encoding counted)
      (audit_dfs_input_budget nat_encoding empty_graph dfs_tiny_index [0]) = true /\
    Nat.leb (audit_dfs_full_model_work nat_encoding full)
      (audit_dfs_full_input_budget nat_encoding empty_graph dfs_tiny_index [0]) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example dfs_all_contract_witnesses :
    audit_dfs_counted_statement /\ audit_dfs_helpers_statement /\ audit_dfs_full_counted_statement
      /\
    audit_dfs_nested_statement /\ audit_graph_capture_callbacks_erases_statement /\
    audit_dfs_source_statement /\ audit_dfs_source_successor_correspondence_statement /\
    audit_dfs_source_adapted_statement /\ audit_dfs_source_contract_statement.
Proof.
  split; [exact audit_dfs_counted_correct|].
  split; [exact audit_dfs_helpers_correct|].
  split; [exact audit_dfs_full_counted_correct|].
  split; [exact audit_dfs_nested_correct|].
  split; [exact audit_graph_capture_callbacks_erases_holds|].
  split; [exact audit_dfs_source_correct|].
  split; [exact audit_dfs_source_successor_correspondence_holds|].
  split; [exact audit_dfs_source_adapted_holds|exact audit_dfs_source_contract_holds].
Qed.

Example dfs_tiny_external_budget_accepts :
    let events := snd (audit_dfs_source_counted dfs_tiny_index dfs_tiny_callbacks FinSet.empty
      [0]) in
    Nat.leb (audit_dfs_source_work (fun _ => 1) events)
      (audit_dfs_source_budget nat_encoding empty_graph dfs_tiny_index [0] +
        audit_dfs_source_external_budget (fun _ => 1) (fun _ => 1) events) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dfs_tiny_zero_budget_rejects :
    Nat.leb (audit_dfs_source_work (fun _ => 1)
      (snd (audit_dfs_source_counted dfs_tiny_index dfs_tiny_callbacks FinSet.empty [0]))) 0 =
      false.
Proof.
  vm_compute; reflexivity.
Qed.
