(** * Fixed-fuel solver fallback and closure use

    Construction retains the actual solver run and the selected result or top branch.
    For example, evaluating a successful returned closure incurs its own lookup work.
    Builds on: FixpointAuditRecorded and FixpointAuditNested. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditCost.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointNested
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditRecorded
  FixpointAuditRecordedBudget FixpointAuditNested.
Import List.ListNotations.

Inductive fx_fallback_event (X C A B : Type) : Type :=
  | FxFallbackRecorded (body : list (fx_recorded_event X C A))
  | FxFallbackNested (body : list (fx_nested_whole_event X C A B))
  | FxFallbackCase (is_result : bool).

Arguments FxFallbackRecorded {X C A B} _.

Arguments FxFallbackNested {X C A B} _.

Arguments FxFallbackCase {X C A B} _.

Definition fx_fallback_result {X A} (EX : encoding X) (L : lattice A) (T : top L)
    (result : option (assignment X A)) : X -> A :=
  match result with
  | Some values => lookup EX L values
  | None => fun _ => top_value T
  end.

Definition fx_recorded_fallback_counted {X C A B} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (fuel : positive) : option (assignment X A) * list (fx_fallback_event X C A B) :=
  let '(out, events) := run_worklist_recorded_model EX EC L sch mode S fuel in
  (out, [FxFallbackRecorded events; FxFallbackCase (
    match out with
    | Some _ => true
    | None => false
    end)]).

Definition fx_nested_fallback_counted {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (fuel : positive) :
    option (assignment X A) * list (fx_fallback_event X C A B) :=
  let '(out, events) := fx_nested_run_counted EX L mode S SS cb fuel in
  (out, [FxFallbackNested events; FxFallbackCase (
    match out with
    | Some _ => true
    | None => false
    end)]).

(** Construction preserves both original proof-erased fallback functions pointwise. *)

(** With lattice laws, recorded fallback agrees pointwise with its solver closure, and nested
    fallback also agrees when its index callbacks erase correctly. *)
Definition fx_fallback_erasure_statement : Prop :=
  (forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (T : top L) (sch : scheduler X) mode (S : System.t X C A) fuel x,
    fx_fallback_result EX L T (fst (@fx_recorded_fallback_counted X C A B EX EC L sch mode S
  fuel)) x =
      proj1_sig (solve_fuel EX EC L HL T sch mode S fuel) x) /\
  (forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
    (T : top L) mode (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) fuel x,
    fx_index_external_erases EX S SS cb ->
    fx_fallback_result EX L T (fst (fx_nested_fallback_counted EX L mode S SS cb fuel)) x =
      proj1_sig (nested_solve_fuel EX EC L HL T mode S SS fuel) x).

Definition fx_fallback_event_work {X C A B} (EC : encoding C)
    (ib : fx_index_external_budget X C B) (event : fx_fallback_event X C A B) : nat :=
  match event with
  | FxFallbackRecorded events => fx_recorded_work EC events
  | FxFallbackNested events => fx_nested_whole_work EC ib events
  | FxFallbackCase _ => 1
  end.

Definition fx_fallback_work {X C A B} (EC : encoding C) (ib : fx_index_external_budget X C B)
    (events : list (fx_fallback_event X C A B)) : nat :=
  fold_right (fun event n => fx_fallback_event_work EC ib event + n) 0 events.

(** Construction budgets exclude later applications of the returned function. *)

(** Recorded fallback returns the original worklist result within its input budget plus one case
    step. *)
Definition fx_recorded_fallback_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    mode (S : System.t X C A) (ib : fx_index_external_budget X C B) fuel,
    let '(out, events) := @fx_recorded_fallback_counted X C A B EX EC L sch mode S fuel in
    out = run_worklist EX EC L sch mode S Recorded fuel /\
    fx_fallback_work EC ib events <= fx_recorded_run_input_budget EX EC L sch mode S fuel + 1.

(** Nested construction uses its graph, WTO, plan and machine allowance. *)

(** With index callback erasure and bounds, nested fallback returns the original run within its
    input budget plus one. *)
Definition fx_nested_fallback_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) fuel,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let '(out, events) := fx_nested_fallback_counted EX L mode S SS cb fuel in
    out = nested_run EX EC L mode S SS fuel /\
    fx_fallback_work EC ib events <= fx_nested_run_input_budget EX L mode S SS ib fuel + 1.

(** Applying a returned closure performs the actual lookup or top branch once. *)

Definition fx_fallback_apply_counted {X C A} (EX : encoding X) (L : lattice A) (T : top L)
    (result : option (assignment X A)) (x : X) : A * audit_trace (fx_declared_call X C A) :=
  match result with
  | Some values => fx_model_lookup EX L values x
  | None => (top_value T, [AuditCase 0 []])
  end.

(** The application boundary is separate from solver construction. *)

(** Applying a fallback returns the chosen lookup or top value within the stated lookup budget. *)
Definition fx_fallback_apply_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (T : top L) result x,
    let '(out, events) := @fx_fallback_apply_counted X C A EX L T result x in
    out = fx_fallback_result EX L T result x /\
    fx_declared_model_work EC events <= 1 + fx_fullcheck_lookup_input_budget EX x.
