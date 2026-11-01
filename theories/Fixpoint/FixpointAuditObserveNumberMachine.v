(** * Numbered observation-machine callbacks

    Numbered target and RHS closures capture label lookups at their actual machine invocation.
    For example, a ready constraint reads its label once for RHS and once for target.
    Builds on: FixpointAuditObserveNumberCallbacks and FixpointAuditNestedMachine. *)

From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist FixpointNested
  FixpointObserve FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditWorklistCallbacks
  FixpointAuditNestedMachine FixpointAuditNestedCallbacks FixpointAuditObserveNumber
  FixpointAuditObserveNumberCallbacks.
Import List.ListNotations.

Inductive fx_number_machine_event (X C A : Type) : Type :=
  | FxNumberMachineNested (events : list (fx_nested_event X nat A))
  | FxNumberMachineRhs (i : nat) (label : C) (out : Query.t X A)
      (events : list (audit_map_event nat C audit_nat_encoding_event))
  | FxNumberMachineTarget (i : nat) (label : C) (out : X)
      (events : list (audit_map_event nat C audit_nat_encoding_event)).

Arguments FxNumberMachineNested {X C A} _.

Arguments FxNumberMachineRhs {X C A} _ _ _ _.

Arguments FxNumberMachineTarget {X C A} _ _ _ _.

(** The shared captured table determines the actual numbered system closures. *)

Definition fx_number_system {X C A} (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) : System.t X nat A :=
  System.Make (seq 0 (length (System.constraints S)))
    (fun i => System.target S (observation_label fallback table i))
    (fun i => System.rhs S (observation_label fallback table i)).

(** A ready step captures its two label calls while executing the original query and updates. *)

Definition fx_number_machine_step {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) (mode : strategy) (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) (state : NestedState.t X nat A) :
    option (NestedState.t X nat A) * list (fx_number_machine_event X C A) :=
  let numbered := fx_number_system S fallback table in
  match NestedState.ready state with
  | [] =>
      let '(out, events) := fx_nested_step EX L plan mode numbered state in
      (out, [FxNumberMachineNested events])
  | i :: rest =>
      let values := NestedState.current state in
      let '(rhs, rhs_label, rhs_events) := fx_observe_numbered_rhs S fallback table i in
      let '(answer, query_events) := @fx_model_query X nat A EX L rhs values in
      let '(value, _, sides) := answer in
      let '(target, target_label, target_events) := fx_observe_numbered_target S fallback table i in
      let next := NestedState.Make values rest (NestedState.frames state)
        (NestedState.dirty state) (NestedState.changed state) in
      let '(out, update_events) := fx_nested_updates EX L plan mode ((target, value) :: sides)
    next in
      (Some out, [FxNumberMachineNested [FxNestedCase 6];
        FxNumberMachineRhs i rhs_label rhs rhs_events;
        FxNumberMachineNested [FxNestedQuery query_events];
        FxNumberMachineTarget i target_label target target_events;
        FxNumberMachineNested update_events])
  end.

(** The step frame cost counts concrete label maps in addition to nested-machine frames. *)

Definition fx_number_machine_event_work {X C A} (event : fx_number_machine_event X C A) : nat :=
  match event with
  | FxNumberMachineNested events => fx_nested_work nat_encoding events
  | FxNumberMachineRhs _ _ _ events
  | FxNumberMachineTarget _ _ _ events =>
      1 + audit_map_source_work audit_nat_events_work events
  end.

(** Step work folds its captured nested and label events. *)

Definition fx_number_machine_work {X C A} (events : list (fx_number_machine_event X C A)) : nat :=
  fold_right (fun event n => fx_number_machine_event_work event + n) 0 events.

(** The independent step budget adds two label lookups exactly on ready states. *)

Definition fx_number_machine_step_budget {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) (mode : strategy) (S : System.t X C A) (fallback : C)
    (table : Map.t nat C) (state : NestedState.t X nat A) : nat :=
  fx_nested_step_input_budget EX L plan mode (fx_number_system S fallback table) state +
  match NestedState.ready state with
  | [] => 0
  | i :: _ => 2 * fx_observe_label_budget i
  end.

(** Non-numbered events use original encoder, continuation and lattice source relations. *)

Definition fx_number_passthrough_source {X C A B} (source : fx_declared_callback_source X C A B) :
    fx_declared_callback_source X nat A B :=
  FxDeclaredCallbackSource X nat A B (fx_source_encode_x source) (fun _ _ _ => False)
    (fun _ _ _ => False) (fx_source_priority source) (fx_source_widening_point source)
    (fun _ _ _ => False) (fx_source_continuation source) (fx_source_leb source)
    (fx_source_join source) (fx_source_widen source).

(** Unused numbered callback slots cost zero; real label calls are charged separately. *)

Definition fx_number_passthrough_budget {X C A B} (budget : fx_declared_callback_budget X C A B) :
    fx_declared_callback_budget X nat A B :=
  FxDeclaredCallbackBudget X nat A B (fx_body_weight budget) (fx_budget_encode_x budget)
    (fun _ => 0) (fun _ => 0) (fx_budget_priority budget) (fx_budget_widening_point budget)
    (fun _ => 0) (fx_budget_continuation budget) (fx_budget_leb budget)
    (fx_budget_join budget) (fx_budget_widen budget).

(** A nested event requires ordered machine-source groups, while an RHS or target event requires
    a body related to its captured label and result by the supplied source. *)

Definition fx_number_machine_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_number_machine_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxNumberMachineNested events => exists groups,
      Forall2 (fx_nested_machine_event_source (fx_number_passthrough_source source)) events
    groups /\
        bodies = concat groups
  | FxNumberMachineRhs _ label out _ => exists body,
      bodies = [body] /\ fx_source_rhs source label out body
  | FxNumberMachineTarget _ label out _ => exists body,
      bodies = [body] /\ fx_source_target source label out body
  end.

(** External budgets refer to the exact captured label or nested callback invocation. *)

Definition fx_number_machine_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_number_machine_event X C A) : nat :=
  match event with
  | FxNumberMachineNested events => fold_right
      (fun event n => fx_nested_machine_external_budget (fx_number_passthrough_budget budget)
    event + n)
      0 events
  | FxNumberMachineRhs _ label _ _ => fx_budget_rhs budget label
  | FxNumberMachineTarget _ label _ _ => fx_budget_target budget label
  end.

(** The numbered-step statement relates event-body groups to the supplied callback sources. *)

(** If the fallback belongs to the system constraints and nested-machine source laws hold, a
    numbered step agrees with the original result and admits source-related body groups within
    the stated work bound. *)
Definition fx_number_machine_step_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (L : lattice A) (plan : NestedPlan.t X nat)
    (mode : strategy) (S : System.t X C A) (fallback : C)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    (state : NestedState.t X nat A),
    In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
    let table := observation_number 0 (System.constraints S) in
    let '(out, events) := fx_number_machine_step EX L plan mode S fallback table state in
    exists bodies, Forall2 (fx_number_machine_event_source source) events bodies /\
      out = nested_step EX L plan mode (observation_system S fallback) state /\
      fx_number_machine_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_number_machine_step_budget EX L plan mode S fallback table state +
        fold_right (fun e n => fx_number_machine_external_budget budget e + n) 0 events.
