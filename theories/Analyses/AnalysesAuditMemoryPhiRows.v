(** * Counted phi input rows

    This mirror preserves predecessor occurrences, first-occurrence keys and operand callbacks.
    For example, duplicate predecessor keys are probed twice but retained at their first position.
    Builds on: G4 phi inputs and shared collection and encoding observers. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominance.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryPhiState.
From Galois.Collections Require Import CollectionsAuditEncoding CollectionsAuditMap
  CollectionsAuditFinSet.
Import List.ListNotations.

Inductive audit_phi_distinct_event (K CE : Type) : Type :=
  | AuditPhiDistinctCase (remaining : list K) (seen : FinSet.t K)
  | AuditPhiDistinctProbe (key : K) (found : bool) (calls : list (audit_set_event K CE))
  | AuditPhiDistinctAdd (key : K) (calls : list (audit_set_event K CE))
  | AuditPhiDistinctKeep (key : K).

Arguments AuditPhiDistinctCase {K CE} _ _.
Arguments AuditPhiDistinctProbe {K CE} _ _ _.
Arguments AuditPhiDistinctAdd {K CE} _ _.
Arguments AuditPhiDistinctKeep {K CE} _.

(** This is the exact first-occurrence traversal used by [memory_distinct]. *)
Fixpoint audit_phi_distinct_from {K CE} (enc : K -> positive * list CE)
    (seen : FinSet.t K) (input : list K) : list K * list (audit_phi_distinct_event K CE) :=
  match input with
  | [] => ([], [AuditPhiDistinctCase input seen])
  | key :: rest =>
      let '(found, probes) := audit_finset_mem enc key seen in
      if found then
        let '(out, events) := audit_phi_distinct_from enc seen rest in
        (out, [AuditPhiDistinctCase input seen; AuditPhiDistinctProbe key found probes] ++ events)
      else
        let '(next, adds) := audit_finset_add enc key seen in
        let '(out, events) := audit_phi_distinct_from enc next rest in
        (key :: out, [AuditPhiDistinctCase input seen; AuditPhiDistinctProbe key found probes;
                      AuditPhiDistinctAdd key adds; AuditPhiDistinctKeep key] ++ events)
  end.

Inductive audit_phi_row_event (N E CN CE PE OE : Type) : Type :=
  | AuditPhiPred (node : N) (edges : list E) (events : list PE)
  | AuditPhiDistinctKeys (events : list (audit_phi_distinct_event (option E) (audit_option_event E
    CE)))
  | AuditPhiRowOperand (node : N) (key : option E) (result : option (memory_version N E))
      (events : list OE)
  | AuditPhiRowStore (events : list (audit_map_event N (list (option E * memory_version N E)) CN)).

Arguments AuditPhiPred {N E CN CE PE OE} _ _ _.
Arguments AuditPhiDistinctKeys {N E CN CE PE OE} _.
Arguments AuditPhiRowOperand {N E CN CE PE OE} _ _ _ _.
Arguments AuditPhiRowStore {N E CN CE PE OE} _.

(** Each distinct key retains the actual optional operand result and its child trace. *)
Fixpoint audit_phi_row_operands {N E CN CE PE OE}
    (operand : N -> option E -> option (memory_version N E) * list OE) (n : N)
    (keys : list (option E))
    : list (option E * memory_version N E) * list (audit_phi_row_event N E CN CE PE OE) :=
  match keys with
  | [] => ([], [])
  | key :: rest =>
      let '(result, calls) := operand n key in
      let '(tail, events) := @audit_phi_row_operands N E CN CE PE OE operand n rest in
      (
        match result with
        | Some v => (key, v) :: tail
        | None => tail
        end,
        AuditPhiRowOperand n key result calls :: events)
  end.

Definition audit_phi_input_row {N E CN CE PE OE}
    (edge_enc : E -> positive * list CE) (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE) (n : N)
    : list (option E * memory_version N E) * list (audit_phi_row_event N E CN CE PE OE) :=
  let '(edges, pe) := pred n in
  let '(keys, de) := audit_phi_distinct_from (audit_option_encode edge_enc) FinSet.empty
    (None :: map Some edges) in
  let '(row, oe) := @audit_phi_row_operands N E CN CE PE OE operand n keys in
  (row, [AuditPhiPred n edges pe; AuditPhiDistinctKeys de] ++ oe).

(** The result index uses the same tail-first order as [memory_result_index]. *)
Fixpoint audit_phi_input_rows {N E CN CE PE OE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE) (nodes : list N)
    : Map.t N (list (option E * memory_version N E)) * list (audit_phi_row_event N E CN CE PE OE) :=
  match nodes with
  | [] => (Map.empty, [])
  | n :: rest =>
      let '(tail, te) := audit_phi_input_rows node_enc edge_enc pred operand rest in
      let '(row, re) := @audit_phi_input_row N E CN CE PE OE edge_enc pred operand n in
      let '(out, se) := audit_map_set node_enc n row tail in
      (out, te ++ re ++ [AuditPhiRowStore se])
  end.

(** * Future exact-result and occurrence bounds *)

(** Matching key codes preserve first occurrences relative to the initial seen set. *)
Definition audit_phi_distinct_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (EK : encoding K) seen input,
    (forall key, In key input -> fst (enc key) = encode EK key) ->
    fst (audit_phi_distinct_from enc seen input) = virtual_entries_from EK seen input.

(** Matching node and edge encoders, predecessor and operand callbacks recover the original phi
    input rows. *)
Definition audit_phi_input_rows_erases_statement : Prop :=
  forall N E T CN CE PE OE (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (pred : N -> list E * list PE)
      (operand : N -> option E -> option (memory_version N E) * list OE),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (pred n) = pred_edges (prepare EN g) n) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    fst (audit_phi_input_rows node_enc edge_enc pred operand (memory_phis mg)) =
      phi_input_rows EN EE g effects mg.

Fixpoint audit_phi_rows_budget {N E PE} (pred : N -> list E * list PE) (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | n :: rest => 4 + length (fst (pred n)) + audit_phi_rows_budget pred rest
  end.

(** The phi input-row trace length is bounded by the row budget. *)
Definition audit_phi_input_rows_count_statement : Prop :=
  forall N E CN CE PE OE (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (pred : N -> list E * list PE)
      (operand : N -> option E -> option (memory_version N E) * list OE) nodes,
    length (snd (audit_phi_input_rows node_enc edge_enc pred operand nodes)) <=
      audit_phi_rows_budget pred nodes.

(** * Nested collection and callback source charges *)

Fixpoint audit_phi_distinct_work {K CE} (enc_work : list CE -> nat)
    (events : list (audit_phi_distinct_event K CE)) : nat :=
  match events with
  | [] => 0
  | AuditPhiDistinctCase _ _ :: rest => 1 + audit_phi_distinct_work enc_work rest
  | AuditPhiDistinctProbe _ _ calls :: rest => audit_finset_source_work enc_work calls +
      audit_phi_distinct_work enc_work rest
  | AuditPhiDistinctAdd _ calls :: rest => audit_finset_source_work enc_work calls +
      audit_phi_distinct_work enc_work rest
  | AuditPhiDistinctKeep _ :: rest => 1 + audit_phi_distinct_work enc_work rest
  end.

Fixpoint audit_phi_rows_primitive_work {N E CN CE PE OE} (node_work : list CN -> nat)
    (edge_work : list CE -> nat) (pred_work : list PE -> nat) (operand_work : list OE -> nat)
    (events : list (audit_phi_row_event N E CN CE PE OE)) : nat :=
  match events with
  | [] => 0
  | AuditPhiPred _ edges calls :: rest => length edges + pred_work calls +
      audit_phi_rows_primitive_work node_work edge_work pred_work operand_work rest
  | AuditPhiDistinctKeys calls :: rest =>
      audit_phi_distinct_work (audit_option_events_work edge_work) calls +
      audit_phi_rows_primitive_work node_work edge_work pred_work operand_work rest
  | AuditPhiRowOperand _ _ _ calls :: rest => operand_work calls +
      audit_phi_rows_primitive_work node_work edge_work pred_work operand_work rest
  | AuditPhiRowStore calls :: rest => audit_map_source_work node_work calls +
      audit_phi_rows_primitive_work node_work edge_work pred_work operand_work rest
  end.

Definition audit_phi_rows_source_work {N E CN CE PE OE} (node_work : list CN -> nat)
    (edge_work : list CE -> nat) (pred_work : list PE -> nat) (operand_work : list OE -> nat)
    (events : list (audit_phi_row_event N E CN CE PE OE)) : nat :=
  1 + 2 * length events + audit_phi_rows_primitive_work node_work edge_work pred_work operand_work
    events.

(** Phi row work is bounded by outer row frames plus the captured primitive calls. *)
Definition audit_phi_input_rows_source_bound_statement : Prop :=
  forall N E CN CE PE OE (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (pred : N -> list E * list PE)
      (operand : N -> option E -> option (memory_version N E) * list OE) nodes
      node_work edge_work pred_work operand_work,
    let events := snd (audit_phi_input_rows node_enc edge_enc pred operand nodes) in
    audit_phi_rows_source_work node_work edge_work pred_work operand_work events <=
      1 + 2 * audit_phi_rows_budget pred nodes +
      audit_phi_rows_primitive_work node_work edge_work pred_work operand_work events.
