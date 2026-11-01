(** * Graph audit adequacy examples

    Computations exercise graph preparation and the generic counted traversals.
    For example, a predecessor lookup retains the target encoder's body receipt.
    Builds on: GraphAuditBaseAdequacy and the graph preparation fixtures. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditMap.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase GraphAuditBaseAdequacy.
From Galois.Tests.Graph Require Import GraphGRA1a.
Import List.ListNotations.

Definition audit_example_callbacks : audit_prepare_callback_model nat nat nat :=
  AuditPrepareCallbackModel nat nat nat
    (fun v => (Graph.out example_graph v, [100 + v]))
    (fun e => (Graph.target example_graph e, [200 + e]))
    (fun v => (encode nat_encoding v, [300 + v])).

Example audit_prepare_empty_boundary :
  fst (audit_graph_prepare_counted nat_encoding empty_graph) = prepare nat_encoding empty_graph /\
  snd (audit_graph_prepare_counted nat_encoding empty_graph) = [] /\
  length (snd (audit_graph_prepare_full_counted nat_encoding empty_graph)) = 5.
Proof.
  repeat split; reflexivity.
Qed.

Example audit_prepare_nontrivial_models :
  fst (audit_graph_prepare_full_counted nat_encoding example_graph) =
    prepare nat_encoding example_graph /\
  length (snd (audit_graph_prepare_full_counted nat_encoding example_graph)) = 50 /\
  fst (audit_graph_prepare_nested_counted nat_encoding example_graph audit_example_callbacks) =
    prepare nat_encoding example_graph /\
  map fst (snd (audit_graph_prepare_nested_counted nat_encoding example_graph
    audit_example_callbacks)) = snd (audit_graph_prepare_full_counted nat_encoding example_graph).
Proof.
  repeat split; reflexivity.
Qed.

Example audit_prepare_nested_callback_operand :
  In (AuditGraphFullCall (AuditPrepareTargetCall 10 2), [210])
    (snd (audit_graph_prepare_nested_counted nat_encoding example_graph audit_example_callbacks)).
Proof.
  vm_compute; tauto.
Qed.

Definition audit_example_source_events : list (audit_prepare_source_event nat nat nat) :=
  snd (audit_prepare_source_counted nat_encoding example_graph audit_example_callbacks).

Definition audit_example_read_receipt (event : audit_prepare_source_event nat nat nat) : bool :=
  match event with
  | PrepareSourceMap (AuditMapGet key code _ _ body _) =>
      Nat.eqb key 2 && Pos.eqb code 3%positive &&
        match body with
        | [302] => true
        | _ => false
        end
  | _ => false
  end.

Definition audit_example_target_receipt (event : audit_prepare_source_event nat nat nat) : bool :=
  match event with
  | PrepareSourceTarget edge target body =>
      Nat.eqb edge 10 && Nat.eqb target 2 &&
        match body with
        | [210] => true
        | _ => false
        end
  | _ => false
  end.

Example audit_prepare_source_receipts :
  fst (audit_prepare_source_counted nat_encoding example_graph audit_example_callbacks) =
    prepare nat_encoding example_graph /\
  length audit_example_source_events = 50 /\
  existsb audit_example_read_receipt audit_example_source_events = true /\
  existsb audit_example_target_receipt audit_example_source_events = true.
Proof.
  repeat split; reflexivity.
Qed.

Example audit_iteration_boundaries :
  audit_n_iter 0%N (fun x : nat => (S x, [x])) 4 = (4, [AuditCombCase 3]) /\
  fst (audit_pos_iter (fun x : nat => (S x, [x])) 4 3%positive) = 7 /\
  audit_comb_call_count (snd (audit_pos_iter (fun x : nat => (S x, [x])) 4 3%positive)) = 3.
Proof.
  repeat split; reflexivity.
Qed.

Example audit_folds_and_filters :
  fst (audit_fold_left (fun acc x : nat => (acc + x, [x])) [1; 2; 3] 0) = 6 /\
  fst (audit_fold_right (fun (x : nat) (acc : list nat) => (x :: acc, [x])) [1; 2] []) = [1; 2] /\
  fst (audit_map (fun x : nat => (S x, [x])) [0; 2]) = [1; 3] /\
  fst (audit_filter (fun x : nat => (Nat.even x, [x])) [0; 1; 2]) = [0; 2] /\
  fst (audit_existsb_strict (fun x : nat => (Nat.eqb x 3, [x])) [0; 1; 2]) = false.
Proof.
  repeat split; reflexivity.
Qed.

Example audit_reverse_with_accumulator :
  audit_graph_reverse_fast_counted [1; 2; 3] [9] = ([3; 2; 1; 9], 7) /\
  audit_graph_reverse_fast_counted ([] : list nat) [9] = ([9], 1).
Proof.
  split; reflexivity.
Qed.

Example audit_strict_exists_visits_after_success :
  audit_existsb_strict (fun x : nat => (Nat.eqb x 1, [x])) [1; 2] =
    (true, [AuditCombCase 16; AuditCombBody 1; AuditCombCase 16; AuditCombBody 2;
      AuditCombCase 15]).
Proof.
  reflexivity.
Qed.

Example audit_prepare_work_budgets_accept :
  Nat.leb
    (audit_graph_prepare_full_work
      (snd (audit_graph_prepare_full_counted nat_encoding example_graph)))
    (audit_graph_prepare_full_budget nat_encoding example_graph) = true /\
  Nat.leb (audit_prepare_source_work (fun x => x) audit_example_source_events)
    (audit_prepare_source_budget nat_encoding example_graph +
      audit_prepare_source_body_work (fun x => x) audit_example_source_events) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.
