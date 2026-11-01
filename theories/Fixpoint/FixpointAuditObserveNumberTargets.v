(** * Numbered observation target index

    The numbered system first constructs its occurrence table and then indexes its targets.
    For example, duplicate constraints have separate numbered target-index entries.
    Builds on: FixpointAuditObserveNumberCallbacks and the counted map model. *)

From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointNested FixpointObserve
  FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditNestedCallbacks
  FixpointAuditObserveExecute FixpointAuditObserveNumber FixpointAuditObserveNumberCallbacks
  FixpointAuditObserveExpiry.
Import List.ListNotations.

Inductive fx_observe_number_target_event (X C : Type) : Type :=
  | FxNumberTable (events : list (audit_map_event nat C audit_nat_encoding_event))
  | FxNumberTarget (i : nat) (label : C) (out : X)
      (events : list (audit_map_event nat C audit_nat_encoding_event))
  | FxNumberIndex (events : list (audit_map_event X (list nat) (fx_encoder_entry X)))
  | FxNumberSeq (size : nat)
  | FxNumberCase.

Arguments FxNumberTable {X C} _.

Arguments FxNumberTarget {X C} _ _ _ _.

Arguments FxNumberIndex {X C} _.

Arguments FxNumberSeq {X C} _.

Arguments FxNumberCase {X C}.

(** The target fold preserves occurrence order and captures every label lookup. *)

Fixpoint fx_number_targets_fold {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) (table : Map.t nat C) (indices : list nat) :
    Map.t X (list nat) * list (fx_observe_number_target_event X C) :=
  match indices with
  | [] => (Map.empty, [FxNumberCase])
  | i :: rest =>
      let '(before, later) := fx_number_targets_fold EX S fallback table rest in
      let '(target, label, label_events) := fx_observe_numbered_target S fallback table i in
      let '(found, read) := audit_map_get (fx_index_encoder EX) target before in
      let old :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(after, write) := audit_map_set (fx_index_encoder EX) target (i :: old) before in
      (after, FxNumberCase :: later ++
        [FxNumberTarget i label target label_events; FxNumberIndex read; FxNumberIndex write])
  end.

(** Building the numbered target map captures its table and the source seq construction. *)

Definition fx_observe_numbered_targets {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) : Map.t X (list nat) * list (fx_observe_number_target_event X C) :=
  let cs := System.constraints S in
  let '(table, table_events) := fx_observe_number 0 cs in
  let indices := seq 0 (length cs) in
  let '(targets, events) := fx_number_targets_fold EX S fallback table indices in
  (targets, FxNumberTable table_events :: FxNumberSeq (length cs) :: events).

(** Nat-key maps charge concrete unary encoder bodies, not a unit-cost callback. *)

Definition fx_number_target_event_work {X C} (event : fx_observe_number_target_event X C) : nat :=
  match event with
  | FxNumberTable events => audit_map_source_work audit_nat_events_work events
  | FxNumberTarget _ _ _ events => 1 + audit_map_source_work audit_nat_events_work events
  | FxNumberIndex events => audit_map_source_work (@length (fx_encoder_entry X)) events
  | FxNumberSeq n => 4 + 4 * n
  | FxNumberCase => 1
  end.

(** The fold sums actual table, label, index and sequence frames. *)

Definition fx_number_targets_work {X C} (events : list (fx_observe_number_target_event X C)) :
    nat :=
  fold_right (fun event n => fx_number_target_event_work event + n) 0 events.

(** Target-index frames use each actual label and encoded target key. *)

Fixpoint fx_number_targets_fold_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) (table : Map.t nat C) (indices : list nat) : nat :=
  match indices with
  | [] => 1
  | i :: rest =>
      let label := observation_label fallback table i in
      let target := System.target S label in
      12 + fx_observe_label_budget i + 21 * Pos.size_nat (encode EX target) +
        fx_number_targets_fold_budget EX S fallback table rest
  end.

(** The target-index bound depends on the input system and concrete numbered table. *)

Definition fx_observe_numbered_targets_budget {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) : nat :=
  let cs := System.constraints S in
  let table := observation_number 0 cs in
  fx_observe_number_budget 0 cs + 4 + 4 * length cs +
    fx_number_targets_fold_budget EX S fallback table (seq 0 (length cs)).

(** Target and index events relate their bodies to target or encoder sources; other
    numbered-target events require no bodies. *)

Definition fx_number_target_event_source {X C A B}
    (source : fx_declared_callback_source X C A B) (event : fx_observe_number_target_event X C)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxNumberTarget _ label out _ => exists body,
      bodies = [body] /\ fx_source_target source label out body
  | FxNumberIndex events =>
      Forall2 (fx_nested_entry_source source) (flat_map fx_observe_map_entries events) bodies
  | _ => bodies = []
  end.

(** Per-invocation target and encoder budgets are summed from the captured trace. *)

Definition fx_number_target_external_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (event : fx_observe_number_target_event X C) : nat :=
  match event with
  | FxNumberTarget _ label _ _ => fx_budget_target budget label
  | FxNumberIndex events => fx_nested_entries_budget budget (flat_map fx_observe_map_entries events)
  | _ => 0
  end.

(** The numbered-index statement relates the target map and event-body witnesses to their
    sources. *)

(** With expiry source laws and bounds, numbered target preparation has its original result,
    source receipts and a work bound. *)
Definition fx_observe_numbered_targets_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (fallback : C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_numbered_targets EX S fallback in
    exists bodies, Forall2 (fx_number_target_event_source source) events bodies /\
      out = nested_targets EX (observation_system S fallback) /\
      fx_number_targets_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_numbered_targets_budget EX S fallback +
        fold_right (fun e n => fx_number_target_external_budget budget e + n) 0 events.

(** The system and target map share one captured occurrence table and sequence construction. *)

Definition fx_observe_numbered_system_targets {X C A} (EX : encoding X) (S : System.t X C A)
    (fallback : C) : (Map.t nat C * System.t X nat A * Map.t X (list nat)) *
      list (fx_observe_number_target_event X C) :=
  let cs := System.constraints S in
  let '(table, table_events) := fx_observe_number 0 cs in
  let indices := seq 0 (length cs) in
  let numbered := System.Make indices
    (fun i => System.target S (observation_label fallback table i))
    (fun i => System.rhs S (observation_label fallback table i)) in
  let '(targets, events) := fx_number_targets_fold EX S fallback table indices in
  ((table, numbered, targets), FxNumberTable table_events :: FxNumberSeq (length cs) :: events).

(** The shared system/table statement relates event-body witnesses to sources and bounds combined
    work. *)

(** With expiry source laws and bounds, numbered system target preparation has its original
    result, source receipts and a work bound. *)
Definition fx_observe_numbered_system_targets_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (fallback : C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_numbered_system_targets EX S fallback in
    let numbered := observation_system S fallback in
    exists bodies, Forall2 (fx_number_target_event_source source) events bodies /\
      out = (observation_number 0 (System.constraints S), numbered, nested_targets EX numbered) /\
      fx_number_targets_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_numbered_targets_budget EX S fallback +
        fold_right (fun e n => fx_number_target_external_budget budget e + n) 0 events.
