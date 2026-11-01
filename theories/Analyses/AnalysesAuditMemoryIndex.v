(** * Counted memory result indexing

    This mirror retains every tail-first index update and actual value callback.
    For example, duplicate keys generate two updates and the earlier occurrence is retained.
    Builds on: AnalysesMemoryFrontier and the shared audit map model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Analyses Require Import AnalysesMemoryFrontier.
From Galois.Collections Require Import CollectionsAuditMap.
Import List.ListNotations.

Inductive audit_memory_index_event (K A CE VE : Type) : Type :=
  | AuditMemoryIndexNil
  | AuditMemoryIndexPut (key : K) (value : A) (before after : Map.t K A)
      (value_events : list VE) (set_events : list (audit_map_event K A CE)).

Arguments AuditMemoryIndexNil {K A CE VE}.
Arguments AuditMemoryIndexPut {K A CE VE} _ _ _ _ _ _.

(** The accumulator and value-call traces belong to the same actual recursive execution. *)
Fixpoint audit_memory_result_index {K A CE VE} (enc : K -> positive * list CE)
    (value : K -> A * list VE) (keys : list K)
    : Map.t K A * list (audit_memory_index_event K A CE VE) :=
  match keys with
  | [] => (Map.empty, [AuditMemoryIndexNil])
  | key :: rest =>
      let '(before, tail_events) := audit_memory_result_index enc value rest in
      let '(v, value_events) := value key in
      let '(after, set_events) := audit_map_set enc key v before in
      (after, tail_events ++ [AuditMemoryIndexPut key v before after value_events set_events])
  end.

(** Matching key codes and values preserve the original index even with duplicate keys. *)
Definition audit_memory_result_index_erases_statement : Prop :=
  forall K A CE VE (enc : K -> positive * list CE) (original_enc : encoding K)
      (value : K -> A * list VE) (original_value : K -> A) keys,
    (forall k, In k keys -> fst (enc k) = encode original_enc k) ->
    (forall k, In k keys -> fst (value k) = original_value k) ->
    fst (audit_memory_result_index enc value keys) = memory_result_index original_enc
      original_value keys.

(** Result indexing records one event per key and one final event. *)
Definition audit_memory_result_index_count_statement : Prop :=
  forall K A CE VE (enc : K -> positive * list CE) (value : K -> A * list VE) keys,
    length (snd (audit_memory_result_index enc value keys)) = S (length keys).

(** Actual child traces are charged at the same occurrence and intermediate map. *)
Fixpoint audit_memory_index_work {K A CE VE} (encoder_work : list CE -> nat)
    (value_work : list VE -> nat) (events : list (audit_memory_index_event K A CE VE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoryIndexNil :: rest => 1 + audit_memory_index_work encoder_work value_work rest
  | AuditMemoryIndexPut _ _ _ _ ve se :: rest =>
      1 + value_work ve + audit_map_source_work encoder_work se +
        audit_memory_index_work encoder_work value_work rest
  end.

(** The budget derives from actual keys, component outputs and the original input length. *)
Fixpoint audit_memory_index_budget {K A CE VE} (enc : K -> positive * list CE)
    (value : K -> A * list VE) (encoder_work : list CE -> nat) (value_work : list VE -> nat)
    (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      3 + encoder_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)) +
      value_work (snd (value key)) + audit_memory_index_budget enc value encoder_work value_work
        rest
  end.

(** Indexing work is bounded by the budget for each key encoding, value call and insertion. *)
Definition audit_memory_result_index_work_bound_statement : Prop :=
  forall K A CE VE (enc : K -> positive * list CE) (value : K -> A * list VE)
      encoder_work value_work keys,
    audit_memory_index_work encoder_work value_work (snd (audit_memory_result_index enc value
      keys)) <=
      audit_memory_index_budget enc value encoder_work value_work keys.
