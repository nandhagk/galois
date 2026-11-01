(** * Observation plan checking

    The checker evaluates all four boolean operands, including after an earlier rejection.
    For example, an invalid root does not suppress component or expiration validation.
    Builds on: the observation preparation, component and expiration comparison models. *)

From Stdlib Require Import List Bool Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks
  FixpointAuditObservePrepare FixpointAuditObserveComponents FixpointAuditObserveExpiry
  FixpointAuditObserveExpireCheck.
Import List.ListNotations.

Inductive fx_observe_check_event (X C B : Type) : Type :=
  | FxCheckPrepare (events : list (fx_observe_prepare_event X C B))
  | FxCheckComponents (events : list (fx_observe_component_event X C B))
  | FxCheckExpiry (events : list (fx_observe_expiry_event X C))
  | FxCheckCompare (events : list (fx_expire_check_event X))
  | FxCheckCase.

Arguments FxCheckPrepare {X C B} _.

Arguments FxCheckComponents {X C B} _.

Arguments FxCheckExpiry {X C B} _.

Arguments FxCheckCompare {X C B} _.

Arguments FxCheckCase {X C B}.

(** Every boolean operand and the actual expiration reconstruction runs on every input. *)

Definition fx_observe_plan_check {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (cb : fx_index_external_model X C B)
    (roots : list X) (p : observation_plan X) : bool * list (fx_observe_check_event X C B) :=
  let '(side, side_events) := fx_observe_side_free cb (System.constraints S) in
  let '(root, root_events) := fx_observe_roots_check S cb roots in
  let order := observation_components p in
  let '(components, component_events) := fx_observe_components EX S SS cb order in
  let '(input, dep_events) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(unknown, unknown_events) := fxi_distinct_counted cb input in
  let '(expiration, expiry_events) := fx_observe_expiry_fold EX S ix order unknown in
  let '(expires, compare_events) := fx_expire_check EX (observation_expire p) expiration in
  (side && root && components && expires,
    [FxCheckPrepare side_events; FxCheckPrepare root_events; FxCheckComponents component_events;
     FxCheckPrepare [FxPrepareDependency dep_events; FxPrepareIndex unknown_events];
     FxCheckExpiry expiry_events; FxCheckCompare compare_events; FxCheckCase]).

(** The frame budget charges both strict checks and independently rebuilt expirations. *)

Definition fx_observe_plan_check_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (ib : fx_index_external_budget X C B)
    (roots : list X) (p : observation_plan X) : nat :=
  let order := observation_components p in
  let expiration := observation_expirations EX S SS ix order in
  1 + fx_observe_prepare_budget EX S SS ix ib roots + fx_observe_components_budget EX S SS ib
    order +
    fx_dep_build_budget EX S SS ib +
    fx_observe_expiry_fold_budget EX S ix order (unknowns EX S SS) +
    fx_expire_check_budget EX (observation_expire p) expiration.

(** Each event charges its own source frames and captured index callback bodies. *)

Definition fx_observe_check_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_check_event X C B) : nat :=
  match event with
  | FxCheckPrepare events => fx_observe_prepare_work ib events
  | FxCheckComponents events => fx_observe_components_work ib events
  | FxCheckExpiry events => fx_observe_expiry_work events
  | FxCheckCompare events => fx_expire_check_work events
  | FxCheckCase => 1
  end.

(** The work fold uses exactly the captured checker events. *)

Definition fx_observe_check_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_check_event X C B)) : nat :=
  fold_right (fun event n => fx_observe_check_event_work ib event + n) 0 events.

(** Preparation, component, expiry and comparison events relate their groups to their phase
    sources; case events require no bodies. *)

Definition fx_observe_check_event_source {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_observe_check_event X C B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxCheckPrepare events => exists groups,
      Forall2 (fx_observe_prepare_event_source index_source source) events groups /\
        bodies = concat groups
  | FxCheckComponents events => exists groups,
      Forall2 (fx_observe_component_event_source index_source source) events groups /\
        bodies = concat groups
  | FxCheckExpiry events => exists groups,
      Forall2 (fx_observe_expiry_event_source source) events groups /\ bodies = concat groups
  | FxCheckCompare events => exists groups,
      Forall2 (fx_expire_check_event_source source) events groups /\ bodies = concat groups
  | FxCheckCase => bodies = []
  end.

(** Each actual expiry and comparison callback contributes its own external budget. *)

Definition fx_observe_check_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_check_event X C B) : nat :=
  match event with
  | FxCheckPrepare events =>
      fold_right (fun e n => fx_observe_prepare_external_budget budget e + n) 0 events
  | FxCheckComponents events =>
      fold_right (fun e n => fx_observe_component_external_budget budget e + n) 0 events
  | FxCheckExpiry events =>
      fold_right (fun e n => fx_observe_expiry_external_budget budget e + n) 0 events
  | FxCheckCompare events =>
      fold_right (fun e n => fx_expire_check_external_budget budget e + n) 0 events
  | FxCheckCase => 0
  end.

(** A single checker witness provides source bodies, exact result and its input-derived bound. *)

(** With index erasure and bounds, dependency source laws and expiry source laws, plan checking
    has its original result, source receipts and a work bound. *)
Definition fx_observe_plan_check_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X) (p : observation_plan X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_plan_check EX S SS ix cb roots p in
    exists bodies, Forall2 (fx_observe_check_event_source index_source source) events bodies /\
      out = observation_plan_check EX S SS ix roots p /\
      fx_observe_check_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_plan_check_budget EX S SS ix ib roots p +
        fold_right (fun e n => fx_observe_check_external_budget budget e + n) 0 events.
