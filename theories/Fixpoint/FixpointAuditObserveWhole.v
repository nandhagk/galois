(** * Whole observation runners

    A single captured plan check feeds numbered compilation and the selected execution.
    For example, rejection and an empty system return before any numbered callback runs.
    Builds on: the observer checker, numbered compiler and numbered execution models. *)

From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks
  FixpointAuditNestedCallbacks FixpointAuditObserveExecute FixpointAuditObservePlanCheck
  FixpointAuditObserveNumberTargets FixpointAuditObserveNumberMachine
  FixpointAuditObserveNumberExecute FixpointAuditObserveCompile FixpointAuditObserveExpiry.
Import List.ListNotations.

Inductive fx_observe_whole_event (X C A B : Type) : Type :=
  | FxObserveWholeCheck (events : list (fx_observe_check_event X C B))
  | FxObserveWholeNumber (events : list (fx_observe_number_target_event X C))
  | FxObserveWholeCompile (events : list (fx_observe_compile_event X C nat B))
  | FxObserveWholeExecute (events : list (fx_number_execute_event X C A))
  | FxObserveWholeProject (events : list (fx_observe_event X nat A))
  | FxObserveWholeCase.

Arguments FxObserveWholeCheck {X C A B} _.

Arguments FxObserveWholeNumber {X C A B} _.

Arguments FxObserveWholeCompile {X C A B} _.

Arguments FxObserveWholeExecute {X C A B} _.

Arguments FxObserveWholeProject {X C A B} _.

Arguments FxObserveWholeCase {X C A B}.

(** The shared core preserves rejection, empty-system and both execution-map branches. *)

Definition fx_observe_whole_core {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (roots : list X) (p : observation_plan X)
    (fuel : positive) (evict : bool) : option (assignment X A) * list (fx_observe_whole_event X
    C A B) :=
  let '(accepted, check_events) := fx_observe_plan_check EX S SS ix cb roots p in
  if accepted then
    match System.constraints S with
    | [] => (Some Map.empty, [FxObserveWholeCheck check_events; FxObserveWholeCase])
    | fallback :: _ =>
        let '((table, _, targets), number_events) := fx_observe_numbered_system_targets EX S
    fallback in
        let '(schedule, compile_events) := fx_observe_compile_targets EX S SS cb targets roots p in
        let '(result, execute_events) := fx_number_execute EX L mode S fallback table schedule
    evict fuel in
        (option_map (if evict then @snd (assignment X A) (assignment X A)
                     else @fst (assignment X A) (assignment X A)) result,
          [FxObserveWholeCheck check_events; FxObserveWholeNumber number_events;
           FxObserveWholeCompile compile_events; FxObserveWholeExecute execute_events;
    FxObserveWholeCase])
    end
  else (None, [FxObserveWholeCheck check_events; FxObserveWholeCase]).

(** The full reference uses non-evicting execution and returns the full assignment. *)

Definition fx_observe_full_reference {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (roots : list X) (p : observation_plan X) (fuel :
    positive) :=
  fx_observe_whole_core EX L mode S SS ix cb roots p fuel false.

(** The optimized runner uses eviction and returns the separately retained output map. *)

Definition fx_observe_run {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (roots : list X) (p : observation_plan X) (fuel :
    positive) :=
  fx_observe_whole_core EX L mode S SS ix cb roots p fuel true.

(** Reference projection is a separate traversal only when the full reference succeeds. *)

Definition fx_observe_reference {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (roots : list X) (p : observation_plan X) (fuel :
    positive) :
    option (assignment X A) * list (fx_observe_whole_event X C A B) :=
  let '(full, events) := fx_observe_full_reference EX L mode S SS ix cb roots p fuel in
  match full with
  | None => (None, events ++ [FxObserveWholeCase])
  | Some values =>
      let '(out, project_events) := @fx_observe_record X nat A EX L roots values Map.empty in
      (Some out, events ++ [FxObserveWholeProject project_events; FxObserveWholeCase])
  end.

(** Work uses the actual captured checker, numbered closures, compiler and machine. *)

Definition fx_observe_whole_event_work {X C A B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_whole_event X C A B) : nat :=
  match event with
  | FxObserveWholeCheck events => fx_observe_check_work ib events
  | FxObserveWholeNumber events => fx_number_targets_work events
  | FxObserveWholeCompile events => fx_observe_compile_work ib events
  | FxObserveWholeExecute events => fx_number_execute_work events
  | FxObserveWholeProject events => fx_observe_work nat_encoding events
  | FxObserveWholeCase => 1
  end.

(** The full source-frame work is a fold over one captured runner execution. *)

Definition fx_observe_whole_work {X C A B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_whole_event X C A B)) : nat :=
  fold_right (fun event n => fx_observe_whole_event_work ib event + n) 0 events.

(** The input bound selects exactly the actual rejection, empty or execution branch. *)

Definition fx_observe_whole_core_budget {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (ib : fx_index_external_budget X C B) (roots : list X) (p : observation_plan X)
    (fuel : positive) (evict : bool) : nat :=
  fx_observe_plan_check_budget EX S SS ix ib roots p + 1 +
  if observation_plan_check EX S SS ix roots p then
    match System.constraints S with
    | [] => 0
    | fallback :: _ =>
        let table := observation_number 0 (System.constraints S) in
        let schedule := observation_compile EX S SS fallback roots p in
        fx_observe_numbered_targets_budget EX S fallback +
          fx_observe_compile_targets_budget EX S SS ib roots p +
          fx_number_execute_budget EX L mode S fallback table schedule evict fuel
    end
  else 0.

(** Reference projection is charged only for an actual successful full-reference result. *)

Definition fx_observe_reference_budget {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (ib : fx_index_external_budget X C B) (roots : list X) (p : observation_plan X)
    (fuel : positive) : nat :=
  1 + fx_observe_whole_core_budget EX L mode S SS ix ib roots p fuel false +
  match observation_full_reference EX L mode S SS ix roots p fuel with
  | None => 0
  | Some _ => fx_observe_record_input_budget EX roots
  end.

(** Check, number, compile, execute and projection events relate their groups to their phase
    sources; whole-run case events require no bodies. *)

Definition fx_observe_whole_event_source {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_observe_whole_event X C A B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxObserveWholeCheck events => exists groups,
      Forall2 (fx_observe_check_event_source index_source source) events groups /\ bodies =
    concat groups
  | FxObserveWholeNumber events => exists groups,
      Forall2 (fx_number_target_event_source source) events groups /\ bodies = concat groups
  | FxObserveWholeCompile events => exists groups,
      Forall2 (fx_observe_compile_event_source index_source (fx_number_passthrough_source source))
        events groups /\ bodies = concat groups
  | FxObserveWholeExecute events => exists groups,
      Forall2 (fx_number_execute_event_source source) events groups /\ bodies = concat groups
  | FxObserveWholeProject events => exists groups,
      Forall2 (fx_observe_event_source (fx_number_passthrough_source source)) events groups /\
    bodies = concat groups
  | FxObserveWholeCase => bodies = []
  end.

(** The external budget sums the per-call allowances selected by each phase event. *)

Definition fx_observe_whole_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_whole_event X C A B) : nat :=
  match event with
  | FxObserveWholeCheck events =>
      fold_right (fun e n => fx_observe_check_external_budget budget e + n) 0 events
  | FxObserveWholeNumber events =>
      fold_right (fun e n => fx_number_target_external_budget budget e + n) 0 events
  | FxObserveWholeCompile events => fold_right
      (fun e n => fx_observe_compile_external_budget (fx_number_passthrough_budget budget) e +
    n) 0 events
  | FxObserveWholeExecute events =>
      fold_right (fun e n => fx_number_execute_external_budget budget e + n) 0 events
  | FxObserveWholeProject events =>
      fold_right (fun e n => fx_observe_event_external_budget (fx_number_passthrough_budget
    budget) e + n) 0 events
  | FxObserveWholeCase => 0
  end.

(** The full-reference witness gives the exact option and the whole source-work allowance. *)

(** With index erasure and bounds and dependency and machine source laws, the full-memory
    reference has its original result, source receipts and a work bound. *)
Definition fx_observe_full_reference_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X) (p : observation_plan X)
    (fuel : positive),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_observe_full_reference EX L mode S SS ix cb roots p fuel in
    exists bodies, Forall2 (fx_observe_whole_event_source index_source source) events bodies /\
      out = observation_full_reference EX L mode S SS ix roots p fuel /\
      fx_observe_whole_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_whole_core_budget EX L mode S SS ix ib roots p fuel false +
        fold_right (fun e n => fx_observe_whole_external_budget budget e + n) 0 events.

(** The evicting-run witness gives its exact option and whole source-work allowance. *)

(** With index erasure and bounds and dependency and machine source laws, the observation run has
    its original result, source receipts and a work bound. *)
Definition fx_observe_run_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X) (p : observation_plan X)
    (fuel : positive),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_observe_run EX L mode S SS ix cb roots p fuel in
    exists bodies, Forall2 (fx_observe_whole_event_source index_source source) events bodies /\
      out = observation_run EX L mode S SS ix roots p fuel /\
      fx_observe_whole_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_whole_core_budget EX L mode S SS ix ib roots p fuel true +
        fold_right (fun e n => fx_observe_whole_external_budget budget e + n) 0 events.

(** The reference witness includes its separate root projection and exact failure branch. *)

(** With index erasure and bounds and dependency and machine source laws, reference execution has
    its original result, source receipts and a work bound. *)
Definition fx_observe_reference_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (roots : list X) (p : observation_plan X)
    (fuel : positive),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_observe_reference EX L mode S SS ix cb roots p fuel in
    exists bodies, Forall2 (fx_observe_whole_event_source index_source source) events bodies /\
      out = observation_reference EX L mode S SS ix roots p fuel /\
      fx_observe_whole_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_reference_budget EX L mode S SS ix ib roots p fuel +
        fold_right (fun e n => fx_observe_whole_external_budget budget e + n) 0 events.
