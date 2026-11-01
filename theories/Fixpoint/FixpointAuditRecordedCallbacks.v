(** * FixpointAuditRecordedCallbacks model

    Recorded-reader source receipts, including duplicate reads and both map encodings.
    Individual callback laws remain external obligations; no whole-work assumption.
    For example, duplicate reads retain their separate callback receipts.
    Builds on: FixpointAuditRecorded and the counted collection models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistCallbacks
  FixpointAuditRecorded FixpointAuditRecordedBudget.
Import List.ListNotations.

Definition fx_recorded_set_entries {C} (events : list (audit_set_event C (fx_encoder_entry C))) :
  list (fx_encoder_entry C) :=
  flat_map (fun event =>
    match event with
    | AuditSetAdd _ _ _ _ body _
    | AuditSetMem _ _ _ _ body _
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

(** Base, read, reader, write and comparison events relate their bodies to their sources;
    recorded case events require no bodies. *)
Definition fx_recorded_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_recorded_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxRecordedBase events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FxRecordedRead x _ _ code _ _ _ _ add_events set_code _ _ =>
      exists lookup_body add_bodies set_body,
        bodies = [lookup_body] ++ add_bodies ++ [set_body] /\
        fx_source_encode_x source x code lookup_body /\
        Forall2 (fx_queue_encoder_source source) (fx_recorded_set_entries add_events) add_bodies /\
        fx_source_encode_x source x set_code set_body
  | FxRecordedReaders x _ code _ _ _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxRecordedWrite x code _ _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxRecordedCompare value old unchanged =>
      exists body, bodies = [body] /\ fx_source_leb source value old unchanged body
  | FxRecordedCase _ => bodies = []
  end.

(** Recorded events and their callback-body groups correspond in order. *)
Definition fx_recorded_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (events : list (fx_recorded_event X C A)) (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_recorded_event_source source) events bodies.

Definition fx_recorded_event_external_budget {X C A B} (budget : fx_declared_callback_budget X C A
  B)
    (event : fx_recorded_event X C A) : nat :=
  match event with
  | FxRecordedBase events => fx_declared_external_trace_budget budget events
  | FxRecordedRead x _ _ _ _ _ _ _ add_events _ _ _ =>
      2 * fx_budget_encode_x budget x +
      fold_right (fun e n => fx_queue_entry_budget budget e + n) 0 (fx_recorded_set_entries
        add_events)
  | FxRecordedReaders x _ _ _ _ _ _ _
  | FxRecordedWrite x _ _ _ _ _ => fx_budget_encode_x budget x
  | FxRecordedCompare value old _ => fx_budget_leb budget value old
  | FxRecordedCase _ => 0
  end.

Definition fx_recorded_external_trace_budget {X C A B} (budget : fx_declared_callback_budget X C A
  B)
    (events : list (fx_recorded_event X C A)) : nat :=
  fold_right (fun event n => fx_recorded_event_external_budget budget event + n) 0 events.

(** With declared callback source laws and bounds, the recorded worklist has its original result,
    source receipts and a work bound. *)
Definition fx_recorded_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) fuel
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    fx_declared_source_laws EX EC L sch S source -> fx_declared_callback_bounded source budget ->
    let '(out, events) := run_worklist_recorded_model EX EC L sch mode S fuel in
    exists bodies,
      fx_recorded_trace_source source events bodies /\
      out = run_worklist EX EC L sch mode S Recorded fuel /\
      fx_recorded_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_recorded_run_input_budget EX EC L sch mode S fuel + fx_recorded_external_trace_budget
          budget events.
