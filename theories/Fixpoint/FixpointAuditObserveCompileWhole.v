(** * Numbered observation compilation

    Numbering and target indexing feed the same captured table to component compilation.
    For example, repeated constraints remain distinct occurrences in each local target map.
    Builds on: FixpointAuditObserveNumberTargets and FixpointAuditObserveCompile. *)

From Stdlib Require Import List Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointObserve FixpointAuditIndex
  FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks FixpointAuditObserveExpiry
  FixpointAuditObserveNumberTargets FixpointAuditObserveNumberMachine FixpointAuditObserveCompile.
Import List.ListNotations.

Inductive fx_observe_compile_whole_event (X C A B : Type) : Type :=
  | FxWholeNumber (events : list (fx_observe_number_target_event X C))
  | FxWholeCompile (events : list (fx_observe_compile_event X C nat B)).

Arguments FxWholeNumber {X C A B} _.

Arguments FxWholeCompile {X C A B} _.

(** The actual numbered target index feeds one component-compilation execution. *)

Definition fx_observe_compile_whole {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (fallback : C)
    (roots : list X) (p : observation_plan X) :
    list (ObservationComponent.t X nat) * list (fx_observe_compile_whole_event X C A B) :=
  let '((_, _, targets), number_events) := fx_observe_numbered_system_targets EX S fallback in
  let '(out, compile_events) := fx_observe_compile_targets EX S SS cb targets roots p in
  (out, [FxWholeNumber number_events; FxWholeCompile compile_events]).

(** The full input budget composes numbered construction and local-component compilation. *)

Definition fx_observe_compile_whole_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (fallback : C)
    (roots : list X) (p : observation_plan X) : nat :=
  fx_observe_numbered_targets_budget EX S fallback +
    fx_observe_compile_targets_budget EX S SS ib roots p.

(** The captured phase work counts numbering, induced closures and local components. *)

Definition fx_observe_compile_whole_event_work {X C A B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_compile_whole_event X C A B) : nat :=
  match event with
  | FxWholeNumber events => fx_number_targets_work events
  | FxWholeCompile events => fx_observe_compile_work ib events
  end.

(** Numbering and compilation events require ordered body groups satisfying their respective
    phase source relations, with the supplied bodies equal to their concatenation. *)

Definition fx_observe_compile_whole_event_source {X C A B D}
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (event : fx_observe_compile_whole_event X C A B) (bodies : list (list D)) : Prop :=
  match event with
  | FxWholeNumber events => exists groups,
      Forall2 (fx_number_target_event_source source) events groups /\ bodies = concat groups
  | FxWholeCompile events => exists groups,
      Forall2 (fx_observe_compile_event_source index_source (fx_number_passthrough_source source))
        events groups /\ bodies = concat groups
  end.

(** External budgets are charged to actual captured numbering and local-plan callbacks. *)

Definition fx_observe_compile_whole_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_compile_whole_event X C
    A B) : nat :=
  match event with
  | FxWholeNumber events => fold_right (fun e n => fx_number_target_external_budget budget e +
    n) 0 events
  | FxWholeCompile events => fold_right
      (fun e n => fx_observe_compile_external_budget (fx_number_passthrough_budget budget) e + n)
      0 events
  end.

(** The same counted compilation has exact schedule output, source bodies and an input bound. *)

(** With index erasure and bounds, dependency source laws and expiry source laws, whole-plan
    compilation preserves its original result with source receipts and a work bound. *)
Definition fx_observe_compile_whole_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (fallback : C) (roots : list X)
    (p : observation_plan X),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_expiry_source_laws EX S source budget ->
    let '(out, events) := fx_observe_compile_whole EX S SS cb fallback roots p in
    exists bodies, Forall2 (fx_observe_compile_whole_event_source index_source source) events
    bodies /\
      out = observation_compile EX S SS fallback roots p /\
      fold_right (fun e n => fx_observe_compile_whole_event_work ib e + n) 0 events +
        fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_compile_whole_budget EX S SS ib fallback roots p +
        fold_right (fun e n => fx_observe_compile_whole_external_budget budget e + n) 0 events.
