(** * Observation execution and boundary accounting

    The counted machine retains nested transitions, output writes and optional evictions.
    For example, completing one component records its roots before evicting expired values.
    Builds on: FixpointObserve and FixpointAuditNestedMachine. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointNested
  FixpointObserve FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditNestedMachine
  FixpointAuditWorklistCallbacks FixpointAuditNestedCallbacks.
Import List.ListNotations.

Inductive fx_observe_event (X C A : Type) : Type :=
  | FxObserveNested (events : list (fx_nested_event X C A))
  | FxObserveQuery (events : audit_trace (fx_declared_call X C A))
  | FxObserveMap (event : audit_map_event X A (fx_encoder_entry X))
  | FxObserveCase (site : nat).

Arguments FxObserveNested {X C A} _.

Arguments FxObserveQuery {X C A} _.

Arguments FxObserveMap {X C A} _.

Arguments FxObserveCase {X C A} _.

Section ObserveExecution.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (mode : strategy) (S : System.t X C A).

Fixpoint fx_observe_record (keys : list X) (values output : assignment X A) :
    assignment X A * list (fx_observe_event X C A) :=
  match keys with
  | [] => (output, [FxObserveCase 0])
  | x :: rest =>
      let '(value, reads) := @fx_model_lookup X C A EX L values x in
      let '(next, writes) := audit_map_set (fx_index_encoder EX) x value output in
      let '(result, later) := fx_observe_record rest values next in
      (result, FxObserveCase 0 :: FxObserveQuery reads :: map FxObserveMap writes ++ later)
  end.

Fixpoint fx_observe_evict (keys : list X) (values : assignment X A) :
    assignment X A * list (fx_observe_event X C A) :=
  match keys with
  | [] => (values, [FxObserveCase 1])
  | x :: rest =>
      let '(next, removed) := audit_map_remove (fx_index_encoder EX) x values in
      let '(result, later) := fx_observe_evict rest next in
      (result, FxObserveCase 1 :: map FxObserveMap removed ++ later)
  end.

Definition fx_observe_tick (evict : bool)
    (input : ObservationState.t X C A + (assignment X A * assignment X A)) :
    (ObservationState.t X C A + (assignment X A * assignment X A)) *
      list (fx_observe_event X C A) :=
  match input with
  | inr finished => (inr finished, [FxObserveCase 2])
  | inl state =>
      let component := ObservationState.active state in
      let '(next, nested_events) :=
        fx_nested_step EX L (ObservationComponent.code component) mode S
          (ObservationState.local state) in
      match next with
      | Some local =>
          (inl (ObservationState.Make component (ObservationState.pending state) local
            (ObservationState.observed state)), [FxObserveCase 2; FxObserveNested nested_events])
      | None =>
          let values := NestedState.current (ObservationState.local state) in
          let '(output, record_events) :=
            fx_observe_record (ObservationComponent.outputs component) values
              (ObservationState.observed state) in
          let '(retained, evict_events) :=
            if evict then fx_observe_evict (ObservationComponent.expire component) values
            else (values, []) in
          let events := FxObserveCase 2 :: FxObserveNested nested_events ::
            record_events ++ evict_events in
          match ObservationState.pending state with
          | [] => (inr (retained, output), events ++ [FxObserveCase 3])
          | next :: rest =>
              (inl (ObservationState.Make next rest (observation_start_local next retained) output),
               events ++ [FxObserveCase 3])
          end
      end
  end.

Fixpoint fx_observe_repeat (evict : bool) (fuel : positive)
    (input : ObservationState.t X C A + (assignment X A * assignment X A)) :
    (ObservationState.t X C A + (assignment X A * assignment X A)) *
      list (fx_observe_event X C A) :=
  match fuel with
  | xH => fx_observe_tick evict input
  | xO smaller =>
      let '(first, events) := fx_observe_repeat evict smaller input in
      let '(out, later) := fx_observe_repeat evict smaller first in
      (out, FxObserveCase 4 :: events ++ later)
  | xI smaller =>
      let '(first, events) := fx_observe_repeat evict smaller input in
      let '(second, later) := fx_observe_repeat evict smaller first in
      let '(out, last) := fx_observe_tick evict second in
      (out, FxObserveCase 4 :: events ++ later ++ last)
  end.

Definition fx_observe_execute (schedule : list (ObservationComponent.t X C))
    (evict : bool) (fuel : positive) :
    option (assignment X A * assignment X A) * list (fx_observe_event X C A) :=
  match schedule with
  | [] => (Some (Map.empty, Map.empty), [FxObserveCase 5])
  | first :: rest =>
      let initial := ObservationState.Make first rest (observation_start_local first Map.empty)
        Map.empty in
      let '(out, events) := fx_observe_repeat evict fuel (inl initial) in
      (
        match out with
        | inl _ => None
        | inr result => Some result
        end, FxObserveCase 5 :: events)
  end.

End ObserveExecution.

(** Every helper and the whole execution erase to the actual observation machine. *)

(** Discarding execution events recovers the original observation execution for the same schedule
    and fuel. *)
Definition fx_observe_execute_erasure_statement : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) mode (S : System.t X C A) schedule evict fuel,
    fst (fx_observe_execute EX L mode S schedule evict fuel) =
      observation_execute EX L mode S schedule evict fuel.

Definition fx_observe_event_work {X C A} (EC : encoding C) (event : fx_observe_event X C A) : nat :=
  match event with
  | FxObserveNested events => fx_nested_work EC events
  | FxObserveQuery events => fx_declared_model_work EC events
  | FxObserveMap e => audit_map_source_work (@length (fx_encoder_entry X)) [e]
  | FxObserveCase _ => 1
  end.

Definition fx_observe_work {X C A} (EC : encoding C)
    (events : list (fx_observe_event X C A)) : nat :=
  fold_right (fun e n => fx_observe_event_work EC e + n) 0 events.

(** * Input-derived execution budget *)

(** Each recorded key pays for the lookup and the output-map update. *)

Fixpoint fx_observe_record_input_budget {X} (EX : encoding X) (keys : list X) : nat :=
  match keys with
  | [] => 1
  | x :: rest =>
      1 + fx_fullcheck_lookup_input_budget EX x + 3 + 16 * Pos.size_nat (encode EX x) +
        fx_observe_record_input_budget EX rest
  end.

(** Each expired key pays for a removal from the current assignment. *)

Fixpoint fx_observe_evict_input_budget {X} (EX : encoding X) (keys : list X) : nat :=
  match keys with
  | [] => 1
  | x :: rest => 4 + 16 * Pos.size_nat (encode EX x) + fx_observe_evict_input_budget EX rest
  end.

(** The boundary charge is selected by the actual nested-step outcome. *)

Definition fx_observe_tick_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (evict : bool)
    (state : ObservationState.t X C A + (assignment X A * assignment X A)) : nat :=
  match state with
  | inr _ => 1
  | inl current =>
      let component := ObservationState.active current in
      3 + fx_nested_step_input_budget EX L (ObservationComponent.code component) mode S
        (ObservationState.local current) +
      match nested_step EX L (ObservationComponent.code component) mode S
          (ObservationState.local current) with
      | Some _ => 0
      | None => fx_observe_record_input_budget EX (ObservationComponent.outputs component) +
          (if evict then fx_observe_evict_input_budget EX (ObservationComponent.expire component)
           else 0) + 1
      end
  end.

(** Binary repetition charges every tick, including ticks after an already finished result. *)

Fixpoint fx_observe_repeat_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (evict : bool) (fuel : positive)
    (state : ObservationState.t X C A + (assignment X A * assignment X A)) : nat :=
  match fuel with
  | xH => fx_observe_tick_input_budget EX L mode S evict state
  | xO smaller =>
      let first := observation_repeat (observation_tick EX L mode S evict) smaller state in
      1 + fx_observe_repeat_input_budget EX L mode S evict smaller state +
        fx_observe_repeat_input_budget EX L mode S evict smaller first
  | xI smaller =>
      let first := observation_repeat (observation_tick EX L mode S evict) smaller state in
      let second := observation_repeat (observation_tick EX L mode S evict) smaller first in
      1 + fx_observe_repeat_input_budget EX L mode S evict smaller state +
        fx_observe_repeat_input_budget EX L mode S evict smaller first +
        fx_observe_tick_input_budget EX L mode S evict second
  end.

(** The schedule bound uses only its input and the actual intermediate machine states. *)

Definition fx_observe_execute_input_budget {X C A} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (schedule : list (ObservationComponent.t X C))
    (evict : bool) (fuel : positive) : nat :=
  match schedule with
  | [] => 1
  | first :: rest =>
      let initial := ObservationState.Make first rest (observation_start_local first Map.empty)
        Map.empty in
      1 + fx_observe_repeat_input_budget EX L mode S evict fuel (inl initial)
  end.

(** The same counted execution erases and is bounded by its input-derived source frames. *)

(** Counted observation execution returns the original result and its work fits the input budget. *)
Definition fx_observe_execute_input_bound_statement : Prop :=
  forall (X C A : Type) (EX : encoding X) (EC : encoding C) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (schedule : list (ObservationComponent.t X C))
    (evict : bool) (fuel : positive),
    let '(out, events) := fx_observe_execute EX L mode S schedule evict fuel in
    out = observation_execute EX L mode S schedule evict fuel /\
      fx_observe_work EC events <= fx_observe_execute_input_budget EX L mode S schedule evict fuel.

(** * Callback receipts for the captured execution *)

(** Each map event exposes its stored encoder-entry list. *)

Definition fx_observe_map_entries {X A}
    (event : audit_map_event X A (fx_encoder_entry X)) : list (fx_encoder_entry X) :=
  match event with
  | AuditMapGet _ _ _ _ entries _ => entries
  | AuditMapSet _ _ _ _ _ entries _ => entries
  | AuditMapRemove _ _ _ _ entries _ => entries
  end.

(** Nested-machine, query and map events relate their bodies to their sources; case events
    require no bodies. *)

Definition fx_observe_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_observe_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxObserveNested events => exists groups,
      Forall2 (fx_nested_machine_event_source source) events groups /\ bodies = concat groups
  | FxObserveQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FxObserveMap event =>
      Forall2 (fx_nested_entry_source source) (fx_observe_map_entries event) bodies
  | FxObserveCase _ => bodies = []
  end.

(** The receipt budget sums per-invocation callback budgets over the captured trace. *)

Definition fx_observe_event_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_observe_event X C A) : nat :=
  match event with
  | FxObserveNested events =>
      fold_right (fun e n => fx_nested_machine_external_budget budget e + n) 0 events
  | FxObserveQuery events => fx_declared_external_trace_budget budget events
  | FxObserveMap event => fx_nested_entries_budget budget (fx_observe_map_entries event)
  | FxObserveCase _ => 0
  end.

(** Every constraint in any scheduled component's target index belongs to the given constraint
    list. *)

Definition fx_observe_schedule_targets_within {X C} (EX : encoding X)
    (constraints : list C) (schedule : list (ObservationComponent.t X C)) : Prop :=
  forall component x c, In component schedule ->
    In c (index_get EX (NestedPlan.targets (ObservationComponent.code component)) x) ->
    In c constraints.

(** One captured execution carries all source bodies and its input-derived frame bound. *)

(** With nested-machine source laws and schedule targets drawn from the system constraints,
    execution preserves its original result with source receipts and a work bound. *)
Definition fx_observe_execute_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (EC : encoding C) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B)
    (schedule : list (ObservationComponent.t X C)) (evict : bool) (fuel : positive),
    fx_nested_machine_source_laws EX L S source budget ->
    fx_observe_schedule_targets_within EX (System.constraints S) schedule ->
    let '(out, events) := fx_observe_execute EX L mode S schedule evict fuel in
    exists bodies, Forall2 (fx_observe_event_source source) events bodies /\
      out = observation_execute EX L mode S schedule evict fuel /\
      fx_observe_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_execute_input_budget EX L mode S schedule evict fuel +
        fold_right (fun e n => fx_observe_event_external_budget budget e + n) 0 events.
