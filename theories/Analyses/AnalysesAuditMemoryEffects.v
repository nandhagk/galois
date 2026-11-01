(** * Counted memory effect rows

    This candidate mirrors the existing tail-first effect-table row builder.
    For example, two effects insert the later index first, preserving both unary conversions.
    Builds on: AnalysesMemoryWalk and the shared map and natural-encoding models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditEncoding
  CollectionsAuditMap.
Import List.ListNotations.

Inductive audit_memory_effect_event (T : Type) : Type :=
  | AuditEffectRow (start : nat) (input : list (memory_effect T))
  | AuditEffectSet (events : list (audit_map_event nat (memory_effect T) audit_nat_encoding_event)).

Arguments AuditEffectRow {T} _ _.
Arguments AuditEffectSet {T} _.

(** This function preserves actual indices, tail-built rows and all nested primitive events. *)
Fixpoint audit_memory_effects_from {T} (start : nat) (input : list (memory_effect T))
    : Map.t nat (memory_effect T) * list (audit_memory_effect_event T) :=
  match input with
  | [] => (Map.empty, [AuditEffectRow start input])
  | effect :: rest =>
      let '(tail, tail_events) := audit_memory_effects_from (S start) rest in
      let '(output, set_events) := audit_map_set audit_nat_encode start effect tail in
      (output, AuditEffectRow start input :: tail_events ++ [AuditEffectSet set_events])
  end.

(** The counted tail-first row builder returns the same index map as the plain builder. *)
Definition audit_memory_effects_from_erases_statement : Prop :=
  forall T start (input : list (memory_effect T)),
    fst (audit_memory_effects_from start input) = memory_walk_effects_from start input.

(** The effect-row trace has one final frame and two frames per input effect. *)
Definition audit_memory_effects_from_count_statement : Prop :=
  forall T start (input : list (memory_effect T)),
    length (snd (audit_memory_effects_from start input)) = 1 + 2 * length input.

(** * Input-derived selected-source budget *)

(** Charges use captured actual encoding and trie operands, not caller-provided prices. *)
Fixpoint audit_memory_effect_map_work {T}
    (events : list (audit_map_event nat (memory_effect T) audit_nat_encoding_event)) : nat :=
  match events with
  | [] => 0
  | AuditMapSet key value code before _ enc_events _ :: rest =>
      1 + 2 * length enc_events +
      audit_trie_update_source_work code (Some (key, value)) before +
      audit_memory_effect_map_work rest
  | _ :: rest => 1 + audit_memory_effect_map_work rest
  end.

Fixpoint audit_memory_effect_events_work {T} (events : list (audit_memory_effect_event T)) : nat :=
  match events with
  | [] => 0
  | AuditEffectRow _ _ :: rest => 1 + audit_memory_effect_events_work rest
  | AuditEffectSet calls :: rest => 1 + audit_memory_effect_map_work calls +
      audit_memory_effect_events_work rest
  end.

(** This bound is derived from the source input indices, including their unary sizes. *)
Fixpoint audit_memory_effects_budget {T} (start : nat) (input : list (memory_effect T)) : nat :=
  match input with
  | [] => 1
  | _ :: rest =>
      let bits := Pos.size_nat (encode nat_encoding start) in
      3 + 2 * S start * S bits + 16 * bits + audit_memory_effects_budget (S start) rest
  end.

(** Effect-row source work is bounded by the budget for its unary indices and trie updates. *)
Definition audit_memory_effects_work_bound_statement : Prop :=
  forall T start (input : list (memory_effect T)),
    audit_memory_effect_events_work (snd (audit_memory_effects_from start input)) <=
      audit_memory_effects_budget start input.

(** * Existing indexed effect lookup *)

Inductive audit_memory_effect_get_event (E T CE : Type) : Type :=
  | AuditEffectEdgeGet
      (events : list (audit_map_event E (Map.t nat (memory_effect T)) CE))
  | AuditEffectIndexGet
      (events : list (audit_map_event nat (memory_effect T) audit_nat_encoding_event)).

Arguments AuditEffectEdgeGet {E T CE} _.
Arguments AuditEffectIndexGet {E T CE} _.

(** A missing edge skips the numeric lookup; a present row uses the actual unary index. *)
Definition audit_memory_effect_get {E T CE} (edge_enc : E -> positive * list CE)
    (table : Map.t E (Map.t nat (memory_effect T))) (edge : E) (index : nat)
    : option (memory_effect T) * list (audit_memory_effect_get_event E T CE) :=
  let '(row, first) := audit_map_get edge_enc edge table in
  match row with
  | None => (None, [AuditEffectEdgeGet first])
  | Some actual =>
      let '(result, second) := audit_map_get audit_nat_encode index actual in
      (result, [AuditEffectEdgeGet first; AuditEffectIndexGet second])
  end.

(** With a matching edge code, the edge lookup and optional row lookup recover the plain result. *)
Definition audit_memory_effect_get_erases_statement : Prop :=
  forall E T CE (edge_enc : E -> positive * list CE) (EE : encoding E) table edge index,
    fst (edge_enc edge) = encode EE edge ->
    fst (@audit_memory_effect_get E T CE edge_enc table edge index) =
      memory_walk_effect_get EE table edge index.

(** An effect lookup emits at most two outer lookup events. *)
Definition audit_memory_effect_get_count_statement : Prop :=
  forall E T CE (edge_enc : E -> positive * list CE) table edge index,
    length (snd (@audit_memory_effect_get E T CE edge_enc table edge index)) <= 2.

(** Both row and index lookups charge their actual nested map and encoding traces. *)
Fixpoint audit_memory_effect_get_work {E T CE} (edge_work : list CE -> nat)
    (events : list (audit_memory_effect_get_event E T CE)) : nat :=
  match events with
  | [] => 0
  | AuditEffectEdgeGet calls :: rest => audit_map_source_work edge_work calls +
      audit_memory_effect_get_work edge_work rest
  | AuditEffectIndexGet calls :: rest => audit_map_source_work audit_nat_events_work calls +
      audit_memory_effect_get_work edge_work rest
  end.
