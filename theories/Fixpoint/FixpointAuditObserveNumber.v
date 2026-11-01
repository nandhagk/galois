(** * Numbered observation-system closures

    The numbered system retains a table of original constraint occurrences.
    For example, two equal constraints at different positions retain separate labels.
    Builds on: FixpointObserve and CollectionsAuditMap. *)

From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditEncoding
  CollectionsAuditEncoderBudget.
From Galois.Fixpoint Require Import FixpointObserve.
Import List.ListNotations.

(** Building the numbered table captures each recursive map write in source order. *)

Fixpoint fx_observe_number {C} (next : nat) (cs : list C) :
    Map.t nat C * list (audit_map_event nat C audit_nat_encoding_event) :=
  match cs with
  | [] => (Map.empty, [])
  | c :: rest =>
      let '(table, later) := fx_observe_number (S next) rest in
      let '(result, write) := audit_map_set audit_nat_encode next c table in
      (result, later ++ write)
  end.

(** A label closure captures the lookup and preserves fallback on a missing index. *)

Definition fx_observe_label {C} (fallback : C) (table : Map.t nat C) (i : nat) :
    C * list (audit_map_event nat C audit_nat_encoding_event) :=
  let '(found, events) := audit_map_get audit_nat_encode i table in
  (
    match found with
    | Some c => c
    | None => fallback
    end, events).

(** The table budget counts list traversal, encoded-key length and persistent map writes. *)

Fixpoint fx_observe_number_budget {C} (next : nat) (cs : list C) : nat :=
  match cs with
  | [] => 1
  | _ :: rest =>
      3 + audit_nat_input_budget next + 16 * Pos.size_nat (encode nat_encoding next) +
        fx_observe_number_budget (S next) rest
  end.

(** The label budget includes encoding and persistent-map lookup for this actual index. *)

Definition fx_observe_label_budget (i : nat) : nat :=
  6 + audit_nat_input_budget i + 5 * Pos.size_nat (encode nat_encoding i).

(** Numbering has the same table and an input-derived source-frame bound. *)

(** Counted numbering returns the original table and its map work fits the list-based budget. *)
Definition fx_observe_number_source_statement : Prop :=
  forall (C : Type) (next : nat) (cs : list C),
    let '(out, events) := fx_observe_number next cs in
    out = observation_number next cs /\
    audit_map_source_work (audit_nat_events_work) events <=
      fx_observe_number_budget next cs.

(** The lookup closure has the same label and an input-derived source-frame bound. *)

(** Counted label lookup returns the original label and its map work fits the index budget. *)
Definition fx_observe_label_source_statement : Prop :=
  forall (C : Type) (fallback : C) (table : Map.t nat C) (i : nat),
    let '(out, events) := fx_observe_label fallback table i in
    out = observation_label fallback table i /\
    audit_map_source_work (audit_nat_events_work) events <= fx_observe_label_budget i.
