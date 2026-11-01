(** * Finite floor-tick observations

    These examples exercise the three source branches and zero-valued fields.
    For example, a completed tick retains its input and emits two frames.
    Builds on: AnalysesAuditScevFloorTick and CollectionsAuditCost. *)

From Stdlib Require Import List NArith.
From Galois.Analyses Require Import AnalysesAuditScevModCountPlain AnalysesAuditScevFloorTick.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.
Local Open Scope N_scope.

(** An already-completed tick returns unchanged with two source frames. *)
Example floor_tick_done_example :
  let st := AuditFloorState 1 2 1 0 0 true 0 in
  let '(out, events) := audit_floor_tick_counted st in out = st /\ audit_work events = 2%nat.
Proof.
  vm_compute; auto.
Qed.

(** An active finishing tick produces the reduced operands and twenty-five frames. *)
Example floor_tick_finish_example :
  let st := AuditFloorState 1 2 1 0 0 false 0 in
  let '(out, events) := audit_floor_tick_counted st in
  out = AuditFloorState 1 2 1 0 0 true 1 /\ audit_work events = 25%nat.
Proof.
  vm_compute; auto.
Qed.

(** At the equality boundary, the finish test is rejected and records quotient and remainder. *)
Example floor_tick_continue_example :
  let st := AuditFloorState 2 2 1 0 0 false 0 in
  let '(out, events) := audit_floor_tick_counted st in
  out = AuditFloorState 1 1 2 0 0 false 1 /\ audit_work events = 27%nat.
Proof.
  vm_compute; auto.
Qed.

(** A zero-length active input takes the finishing branch when its modulus is positive. *)
Example floor_tick_empty_example :
  let st := AuditFloorState 0 2 1 1 0 false 0 in
  let '(out, events) := audit_floor_tick_counted st in
  out = AuditFloorState 0 2 1 1 0 true 1 /\ audit_work events = 25%nat.
Proof.
  vm_compute; auto.
Qed.

(** A zero modulus retains the specified total division and remainder behavior. *)
Example floor_tick_zero_modulus_example :
  let st := AuditFloorState 0 0 0 0 0 false 0 in
  let '(out, events) := audit_floor_tick_counted st in
  out = AuditFloorState 0 0 0 0 0 false 1 /\ audit_work events = 27%nat.
Proof.
  vm_compute; auto.
Qed.

(** Instrumentation charges distinguish the three branch shapes. *)
Example floor_tick_instrumentation_examples :
  floor_instrumentation_work (AuditFloorState 1 2 1 0 0 true 0) = 7%nat /\
  floor_instrumentation_work (AuditFloorState 1 2 1 0 0 false 0) = 141%nat /\
  floor_instrumentation_work (AuditFloorState 2 2 1 0 0 false 0) = 149%nat.
Proof.
  vm_compute; auto.
Qed.

(** The literal continuing trace records the same output and number of frames. *)
Example floor_tick_literal_continue_example :
  let '(out, events) := floor_tick_counted (AuditFloorState 2 2 1 0 0 false 0) in
  out = AuditFloorState 1 1 2 0 0 false 1 /\ length events = 27%nat.
Proof.
  vm_compute; auto.
Qed.

(** A zero divisor still records the actual nonzero remainder operands. *)
Example floor_tick_zero_divisor_operands_example :
  let st := AuditFloorState 2 0 3 4 5 false 0 in
  let '(out, events) := audit_floor_tick_counted st in
  out = AuditFloorState 0 3 0 10 5 false 1 /\ audit_work events = 27%nat /\
  In (AuditArithmetic 5 [3; 0]) events /\
  In (AuditArithmetic 5 [4; 0]) events /\
  In (AuditArithmetic 4 [10; 0]) events /\
  In (AuditArithmetic 5 [10; 0]) events.
Proof.
  vm_compute; tauto.
Qed.

(** Actual source-frame weights distinguish the three small executions. *)
Example floor_tick_source_weight_examples :
  floor_source_weight (snd (audit_floor_tick_counted (AuditFloorState 1 2 1 0 0 true 0))) =
    2%nat /\
  floor_source_weight (snd (audit_floor_tick_counted (AuditFloorState 1 2 1 0 0 false 0))) =
    87%nat /\
  floor_source_weight (snd (audit_floor_tick_counted (AuditFloorState 2 2 1 0 0 false 0))) =
    134%nat.
Proof.
  vm_compute; auto.
Qed.
