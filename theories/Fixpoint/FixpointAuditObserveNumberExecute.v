(** * Numbered observation execution

    This execution captures each numbered callback in the same machine tick that invokes it.
    For example, boundary output writes retain their own encoder calls before eviction.
    Builds on: FixpointAuditObserveNumberMachine and FixpointAuditObserveExecute. *)

From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointNested FixpointObserve
  FixpointAuditWorklistCallbacks FixpointAuditNestedMachine FixpointAuditNestedCallbacks
  FixpointAuditObserveExecute FixpointAuditObserveNumber FixpointAuditObserveNumberMachine.
Import List.ListNotations.

Inductive fx_number_execute_event (X C A : Type) : Type :=
  | FxNumberExecuteMachine (events : list (fx_number_machine_event X C A))
  | FxNumberExecuteBoundary (events : list (fx_observe_event X nat A))
  | FxNumberExecuteCase.

Arguments FxNumberExecuteMachine {X C A} _.

Arguments FxNumberExecuteBoundary {X C A} _.

Arguments FxNumberExecuteCase {X C A}.

(** A tick performs the counted nested step, then the actual boundary operations if finished. *)

Definition fx_number_execute_tick {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C) (evict : bool)
    (state : ObservationState.t X nat A + (assignment X A * assignment X A)) :
    (ObservationState.t X nat A + (assignment X A * assignment X A)) *
      list (fx_number_execute_event X C A) :=
  match state with
  | inr finished => (inr finished, [FxNumberExecuteCase])
  | inl current =>
      let component := ObservationState.active current in
      let '(next, machine) := fx_number_machine_step EX L (ObservationComponent.code component)
        mode S fallback table (ObservationState.local current) in
      match next with
      | Some local =>
          (inl (ObservationState.Make component (ObservationState.pending current) local
            (ObservationState.observed current)), [FxNumberExecuteCase; FxNumberExecuteMachine
    machine])
      | None =>
          let values := NestedState.current (ObservationState.local current) in
          let '(output, record_events) := @fx_observe_record X nat A EX L
            (ObservationComponent.outputs component) values (ObservationState.observed current) in
          let '(retained, evict_events) := if evict then
            @fx_observe_evict X nat A EX (ObservationComponent.expire component) values
            else (values, []) in
          let events := [FxNumberExecuteCase; FxNumberExecuteMachine machine;
            FxNumberExecuteBoundary (record_events ++ evict_events); FxNumberExecuteCase] in
          match ObservationState.pending current with
          | [] => (inr (retained, output), events)
          | next :: rest =>
              (inl (ObservationState.Make next rest (observation_start_local next retained)
    output), events)
          end
      end
  end.

(** Binary repetition retains every real tick, even after a finished state. *)

Fixpoint fx_number_execute_repeat {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C) (evict : bool)
    (fuel : positive) (state : ObservationState.t X nat A + (assignment X A * assignment X A)) :
    (ObservationState.t X nat A + (assignment X A * assignment X A)) *
      list (fx_number_execute_event X C A) :=
  match fuel with
  | xH => fx_number_execute_tick EX L mode S fallback table evict state
  | xO smaller =>
      let '(first, events) := fx_number_execute_repeat EX L mode S fallback table evict smaller
    state in
      let '(out, later) := fx_number_execute_repeat EX L mode S fallback table evict smaller
    first in
      (out, FxNumberExecuteCase :: events ++ later)
  | xI smaller =>
      let '(first, events) := fx_number_execute_repeat EX L mode S fallback table evict smaller
    state in
      let '(second, later) := fx_number_execute_repeat EX L mode S fallback table evict smaller
    first in
      let '(out, last) := fx_number_execute_tick EX L mode S fallback table evict second in
      (out, FxNumberExecuteCase :: events ++ later ++ last)
  end.

(** The machine starts from the actual first component and preserves both returned maps. *)

Definition fx_number_execute {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C)
    (schedule : list (ObservationComponent.t X nat)) (evict : bool) (fuel : positive) :
    option (assignment X A * assignment X A) * list (fx_number_execute_event X C A) :=
  match schedule with
  | [] => (Some (Map.empty, Map.empty), [FxNumberExecuteCase])
  | first :: rest =>
      let initial := ObservationState.Make first rest (observation_start_local first Map.empty)
    Map.empty in
      let '(out, events) := fx_number_execute_repeat EX L mode S fallback table evict fuel (inl
    initial) in
      (
        match out with
        | inl _ => None
        | inr result => Some result
        end, FxNumberExecuteCase :: events)
  end.

(** Each event charges its actual nested, label or boundary frames. *)

Definition fx_number_execute_event_work {X C A} (event : fx_number_execute_event X C A) : nat :=
  match event with
  | FxNumberExecuteMachine events => fx_number_machine_work events
  | FxNumberExecuteBoundary events => fx_observe_work nat_encoding events
  | FxNumberExecuteCase => 1
  end.

(** Execution work folds exactly the events captured by the run. *)

Definition fx_number_execute_work {X C A} (events : list (fx_number_execute_event X C A)) : nat :=
  fold_right (fun event n => fx_number_execute_event_work event + n) 0 events.

(** The tick bound adds the concrete label costs only when a constraint is ready. *)

Definition fx_number_execute_tick_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C) (evict : bool)
    (state : ObservationState.t X nat A + (assignment X A * assignment X A)) : nat :=
  fx_observe_tick_input_budget EX L mode (fx_number_system S fallback table) evict state +
  match state with
  | inr _ => 0
  | inl current =>
    match NestedState.ready (ObservationState.local current) with
    | [] => 0
    | i :: _ => 2 * fx_observe_label_budget i
    end
  end.

(** The binary bound follows the real intermediate states, including finished-state ticks. *)

Fixpoint fx_number_execute_repeat_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C) (evict : bool)
    (fuel : positive) (state : ObservationState.t X nat A + (assignment X A * assignment X A))
    : nat :=
  let tick := observation_tick EX L mode (fx_number_system S fallback table) evict in
  match fuel with
  | xH => fx_number_execute_tick_budget EX L mode S fallback table evict state
  | xO smaller =>
      let first := observation_repeat tick smaller state in
      1 + fx_number_execute_repeat_budget EX L mode S fallback table evict smaller state +
        fx_number_execute_repeat_budget EX L mode S fallback table evict smaller first
  | xI smaller =>
      let first := observation_repeat tick smaller state in
      let second := observation_repeat tick smaller first in
      1 + fx_number_execute_repeat_budget EX L mode S fallback table evict smaller state +
        fx_number_execute_repeat_budget EX L mode S fallback table evict smaller first +
        fx_number_execute_tick_budget EX L mode S fallback table evict second
  end.

(** The schedule budget starts from the real initial state and charges the empty branch. *)

Definition fx_number_execute_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (fallback : C) (table : Map.t nat C)
    (schedule : list (ObservationComponent.t X nat)) (evict : bool) (fuel : positive) : nat :=
  match schedule with
  | [] => 1
  | first :: rest =>
      let initial := ObservationState.Make first rest (observation_start_local first Map.empty)
    Map.empty in
      1 + fx_number_execute_repeat_budget EX L mode S fallback table evict fuel (inl initial)
  end.

(** Machine and boundary events relate their groups to the corresponding sources;
    numbered-execution case events require no bodies. *)

Definition fx_number_execute_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_number_execute_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxNumberExecuteMachine events => exists groups,
      Forall2 (fx_number_machine_event_source source) events groups /\ bodies = concat groups
  | FxNumberExecuteBoundary events => exists groups,
      Forall2 (fx_observe_event_source (fx_number_passthrough_source source)) events groups /\
        bodies = concat groups
  | FxNumberExecuteCase => bodies = []
  end.

(** External budgets follow the callback invocations actually retained in the run. *)

Definition fx_number_execute_external_budget {X C A B} (budget : fx_declared_callback_budget X
    C A B)
    (event : fx_number_execute_event X C A) : nat :=
  match event with
  | FxNumberExecuteMachine events =>
      fold_right (fun e n => fx_number_machine_external_budget budget e + n) 0 events
  | FxNumberExecuteBoundary events =>
      fold_right (fun e n => fx_observe_event_external_budget (fx_number_passthrough_budget
    budget) e + n)
        0 events
  | FxNumberExecuteCase => 0
  end.

(** One execution witness supplies both maps, captured source bodies and its intermediate-state
    bound. *)

(** If the fallback belongs to the system constraints and nested-machine source laws hold,
    numbered execution has its original result, source receipts and a work bound. *)
Definition fx_number_execute_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (fallback : C) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (schedule : list (ObservationComponent.t X nat))
    (evict : bool) (fuel : positive),
    In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
    let table := observation_number 0 (System.constraints S) in
    let '(out, events) := fx_number_execute EX L mode S fallback table schedule evict fuel in
    exists bodies, Forall2 (fx_number_execute_event_source source) events bodies /\
      out = observation_execute EX L mode (observation_system S fallback) schedule evict fuel /\
      fx_number_execute_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_number_execute_budget EX L mode S fallback table schedule evict fuel +
        fold_right (fun e n => fx_number_execute_external_budget budget e + n) 0 events.
