(** * Counted first-occurrence memory indexing

    This mirror preserves the original order and nested set operations used by memory distinctness.
    For example, repeated edges are probed twice but retained only at their first occurrence.
    Builds on: GraphDominance, AnalysesMemoryFrontier and the audit finite-set observer. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Graph Require Import GraphDominance.
From Galois.Analyses Require Import AnalysesMemoryFrontier.
From Galois.Collections Require Import CollectionsAuditFinSet.
Import List.ListNotations.

Inductive audit_memory_distinct_event (A CE : Type) : Type :=
  | AuditMemoryDistinctCase (remaining : list A) (seen : FinSet.t A)
  | AuditMemoryDistinctProbe (key : A) (result : bool) (calls : list (audit_set_event A CE))
  | AuditMemoryDistinctAdd (key : A) (calls : list (audit_set_event A CE))
  | AuditMemoryDistinctKeep (key : A).

Arguments AuditMemoryDistinctCase {A CE} _ _.
Arguments AuditMemoryDistinctProbe {A CE} _ _ _.
Arguments AuditMemoryDistinctAdd {A CE} _ _.
Arguments AuditMemoryDistinctKeep {A CE} _.

(** Each input occurrence performs its actual membership call before the conditional insertion. *)
Fixpoint audit_memory_distinct_from {A CE} (enc : A -> positive * list CE)
    (seen : FinSet.t A) (input : list A) : list A * list (audit_memory_distinct_event A CE) :=
  match input with
  | [] => ([], [AuditMemoryDistinctCase input seen])
  | key :: rest =>
      let '(found, probes) := audit_finset_mem enc key seen in
      if found then
        let '(out, events) := audit_memory_distinct_from enc seen rest in
        (out, [AuditMemoryDistinctCase input seen; AuditMemoryDistinctProbe key found probes] ++
          events)
      else
        let '(next, adds) := audit_finset_add enc key seen in
        let '(out, events) := audit_memory_distinct_from enc next rest in
        (key :: out, [AuditMemoryDistinctCase input seen; AuditMemoryDistinctProbe key found probes;
                      AuditMemoryDistinctAdd key adds; AuditMemoryDistinctKeep key] ++ events)
  end.

Definition audit_memory_distinct {A CE} (enc : A -> positive * list CE) (input : list A)
    : list A * list (audit_memory_distinct_event A CE) :=
  audit_memory_distinct_from enc FinSet.empty input.

(** Matching input codes preserve first-occurrence order relative to the supplied seen set. *)
Definition audit_memory_distinct_from_erases_statement : Prop :=
  forall A CE (enc : A -> positive * list CE) (EA : encoding A) seen input,
    (forall x, In x input -> fst (enc x) = encode EA x) ->
    fst (audit_memory_distinct_from enc seen input) = virtual_entries_from EA seen input.

(** Matching codes on the input preserve the original first-occurrence ordering. *)
Definition audit_memory_distinct_erases_statement : Prop :=
  forall A CE (enc : A -> positive * list CE) (EA : encoding A) input,
    (forall x, In x input -> fst (enc x) = encode EA x) ->
    fst (audit_memory_distinct enc input) = memory_distinct EA input.

(** Fixed source charges retain the actual nested probe and conditional add executions. *)
Fixpoint audit_memory_distinct_work {A CE} (enc_work : list CE -> nat)
    (events : list (audit_memory_distinct_event A CE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoryDistinctCase _ _ :: rest => 1 + audit_memory_distinct_work enc_work rest
  | AuditMemoryDistinctProbe _ _ calls :: rest => audit_finset_source_work enc_work calls +
      audit_memory_distinct_work enc_work rest
  | AuditMemoryDistinctAdd _ calls :: rest => audit_finset_source_work enc_work calls +
      audit_memory_distinct_work enc_work rest
  | AuditMemoryDistinctKeep _ :: rest => 1 + audit_memory_distinct_work enc_work rest
  end.

Fixpoint audit_memory_distinct_budget {A CE} (enc : A -> positive * list CE)
    (enc_work : list CE -> nat) (input : list A) : nat :=
  match input with
  | [] => 1
  | key :: rest => 10 + 2 * enc_work (snd (enc key)) + 21 * Pos.size_nat (fst (enc key)) +
      audit_memory_distinct_budget enc enc_work rest
  end.

(** Distinctness work is bounded by a budget charging every probe and possible insertion. *)
Definition audit_memory_distinct_source_bound_statement : Prop :=
  forall A CE (enc : A -> positive * list CE) enc_work seen input,
    audit_memory_distinct_work enc_work (snd (audit_memory_distinct_from enc seen input)) <=
      audit_memory_distinct_budget enc enc_work input.
