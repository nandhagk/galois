(** * Nested solver preparation and execution

    One captured dependency index feeds graph preparation, WTO and the solver machine.
    For example, each graph outgoing call retains the body for its actual vertex.
    Builds on: FixpointAuditScheduleWrapper, GraphAuditWto and the nested phase models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphCore GraphPrepare GraphWto GraphAuditBase GraphAuditDfs
  GraphAuditWto.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointNested FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditNestedPlan
  FixpointAuditNestedMachine.
Import List.ListNotations.

Inductive fx_nested_whole_event (X C A B : Type) : Type :=
  | FnWholeDependency (events : list (fx_dep_event X C B))
  | FnWholePrepare (events : list (audit_prepare_source_event X (X * X) (fx_dep_event X C B)))
  | FnWholeWto (events : list (audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B))))
  | FnWholePlan (events : list (fx_nested_plan_event X C))
  | FnWholeMachine (events : list (fx_nested_event X C A))
  | FnWholeCase (site : nat).

Arguments FnWholeDependency {X C A B} _.

Arguments FnWholePrepare {X C A B} _.

Arguments FnWholeWto {X C A B} _.

Arguments FnWholePlan {X C A B} _.

Arguments FnWholeMachine {X C A B} _.

Arguments FnWholeCase {X C A B} _.

Definition fx_nested_run_counted {X C A B} (EX : encoding X) (L : lattice A) (mode : strategy)
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (fuel : positive) : option (assignment X A) * list (fx_nested_whole_event X C A B) :=
  let '(graph, ix, graph_events) := fx_dep_graph_build EX S SS cb in
  let '(prepared, prepare_events) := audit_prepare_source_counted EX graph (fx_dep_prepare_cb cb
  ix) in
  let '(tokens, wto_events) := audit_wto_source_counted prepared (fx_dep_dfs_cb cb) in
  let '(plan, plan_events) := fx_nested_plan_from_tokens EX S tokens in
  let '(result, machine_events) := fx_nested_loop EX L plan mode S fuel (nested_start plan) in
  (
    match result with
    | inl _ => None
    | inr values => Some values
    end,
   [FnWholeDependency graph_events; FnWholePrepare prepare_events; FnWholeWto wto_events;
    FnWholePlan plan_events; FnWholeMachine machine_events; FnWholeCase 0]).

(** The counted phases erase to the same nested solve when index callbacks erase. *)

(** With index callback erasure, discarding whole-run events recovers the original nested solver
    result. *)
Definition fx_nested_run_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B) fuel,
    fx_index_external_erases EX S SS cb ->
    fst (fx_nested_run_counted EX L mode S SS cb fuel) = nested_run EX EC L mode S SS fuel.

Definition fx_nested_whole_event_work {X C A B} (EC : encoding C)
    (ib : fx_index_external_budget X C B) (event : fx_nested_whole_event X C A B) : nat :=
  match event with
  | FnWholeDependency events => fx_dep_events_work ib events
  | FnWholePrepare events => audit_prepare_source_work (fx_dep_event_work ib) events
  | FnWholeWto events => audit_wto_source_work (fx_dep_event_work ib) events
  | FnWholePlan events => fx_nested_plan_work events
  | FnWholeMachine events => fx_nested_work EC events
  | FnWholeCase _ => 1
  end.

Definition fx_nested_whole_work {X C A B} (EC : encoding C)
    (ib : fx_index_external_budget X C B) (events : list (fx_nested_whole_event X C A B)) : nat :=
  fold_right (fun e n => fx_nested_whole_event_work EC ib e + n) 0 events.

Definition fx_nested_run_input_budget {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S)
    (ib : fx_index_external_budget X C B) (fuel : positive) : nat :=
  let graph := dependency_graph EX S SS in
  let prepared := prepare EX graph in
  let tokens := wto_total prepared in
  let plan := nested_prepare EX S SS in
  let count := audit_graph_prepare_full_event_bound graph + audit_wto_input_event_bound prepared in
  fx_dep_build_budget EX S SS ib + audit_prepare_source_budget EX graph +
    audit_wto_source_budget EX graph prepared +
    64 * (1 + count) * fx_rpo_callback_max EX S SS ib +
    fx_nested_plan_input_budget EX S tokens +
    fx_nested_loop_input_budget EX L plan mode S fuel (nested_start plan) + 1.

(** The phase allowance depends on inputs and native intermediate structures. *)

(** With index callback erasure and bounds, the nested run returns the original result within its
    input budget. *)
Definition fx_nested_run_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) fuel,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let '(result, events) := fx_nested_run_counted EX L mode S SS cb fuel in
    result = nested_run EX EC L mode S SS fuel /\
    fx_nested_whole_work EC ib events <= fx_nested_run_input_budget EX L mode S SS ib fuel.

(** The nested-run derivation connects actual graph, preparation, WTO, plan and machine results
    and events in order. *)

Inductive fx_nested_run_model_relation {X C A B} (EX : encoding X) (L : lattice A)
    (mode : strategy) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (fuel : positive) :
    option (assignment X A) -> list (fx_nested_whole_event X C A B) -> Prop :=
  | FxNestedRunModel : forall graph ix graph_events prepared prepare_events tokens wto_events
      plan plan_events result machine_events,
      fx_dep_graph_build EX S SS cb = (graph, ix, graph_events) ->
      audit_prepare_source_counted EX graph (fx_dep_prepare_cb cb ix) =
        (prepared, prepare_events) ->
      audit_wto_source_counted prepared (fx_dep_dfs_cb cb) = (tokens, wto_events) ->
      fx_nested_plan_from_tokens EX S tokens = (plan, plan_events) ->
      fx_nested_loop EX L plan mode S fuel (nested_start plan) = (result, machine_events) ->
      fx_nested_run_model_relation EX L mode S SS cb fuel
        (
          match result with
          | inl _ => None
          | inr values => Some values
          end)
        [FnWholeDependency graph_events; FnWholePrepare prepare_events; FnWholeWto wto_events;
         FnWholePlan plan_events; FnWholeMachine machine_events; FnWholeCase 0].

(** Every counted nested run has the corresponding phase derivation. *)

(** The counted nested execution yields a witness of the whole-run relation. *)
Definition fx_nested_run_model_total_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) mode (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) fuel,
    let '(out, events) := fx_nested_run_counted EX L mode S SS cb fuel in
    fx_nested_run_model_relation EX L mode S SS cb fuel out events.

(** Each such derivation preserves the native result and the independent phase allowance. *)

(** With index callback erasure and bounds, a whole-run witness returns the original result
    within the input budget. *)
Definition fx_nested_run_model_correct_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) fuel out events,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_nested_run_model_relation EX L mode S SS cb fuel out events ->
    out = nested_run EX EC L mode S SS fuel /\
    fx_nested_whole_work EC ib events <= fx_nested_run_input_budget EX L mode S SS ib fuel.
