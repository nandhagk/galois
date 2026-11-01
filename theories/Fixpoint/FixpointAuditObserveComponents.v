(** * Observation component validation

    Component validation compares SCC classes, universe coverage and forward boundaries.
    For example, an earlier failed component match does not stop a strict existsb tail.
    Builds on: FixpointAuditObserveOrder, FixpointAuditObserveForward and comparison models. *)

From Stdlib Require Import List Bool Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks
  FixpointAuditObserveOrder FixpointAuditObserveForward FixpointAuditObserveCompare.
Import List.ListNotations.

Inductive fx_observe_component_event (X C B : Type) : Type :=
  | FxComponentOrder (events : list (fx_observe_order_event X C B))
  | FxComponentDependency (events : list (fx_dep_event X C B))
  | FxComponentIndex (events : list (fx_index_nested_event X C B))
  | FxComponentForward (events : list (fx_observe_forward_event X C B))
  | FxComponentCompare (events : list (fx_observe_compare_event X))
  | FxComponentList (size : nat)
  | FxComponentCase.

Arguments FxComponentOrder {X C B} _.

Arguments FxComponentDependency {X C B} _.

Arguments FxComponentIndex {X C B} _.

Arguments FxComponentForward {X C B} _.

Arguments FxComponentCompare {X C B} _.

Arguments FxComponentList {X C B} _.

Arguments FxComponentCase {X C B}.

(** Every candidate class is examined, including after a successful class match. *)

Fixpoint fx_component_in_classes {X C B} (EX : encoding X) (component : list X)
    (classes : list (list X)) : bool * list (fx_observe_component_event X C B) :=
  match classes with
  | [] => (false, [FxComponentCase])
  | class :: rest =>
      let '(same, events) := fx_observe_seteq EX component class in
      let '(later, tail) := @fx_component_in_classes X C B EX component rest in
      (same || later, FxComponentCase :: FxComponentCompare events :: tail)
  end.

(** Every component receives a full class scan. *)

Fixpoint fx_components_in_classes {X C B} (EX : encoding X) (order classes : list (list X)) :
    bool * list (fx_observe_component_event X C B) :=
  match order with
  | [] => (true, [FxComponentCase])
  | component :: rest =>
      let '(found, events) := @fx_component_in_classes X C B EX component classes in
      let '(later, tail) := @fx_components_in_classes X C B EX rest classes in
      (found && later, FxComponentCase :: events ++ tail)
  end.

(** Nonempty validation evaluates all list tails. *)

Fixpoint fx_components_nonempty {X C B} (order : list (list X)) :
    bool * list (fx_observe_component_event X C B) :=
  match order with
  | [] => (true, [FxComponentCase])
  | component :: rest =>
      let '(later, tail) := @fx_components_nonempty X C B rest in
      ((
        match component with
        | [] => false
        | _ => true
        end) && later, FxComponentCase :: tail)
  end.

(** All strict component checks consume the same computed classes and actual input order. *)

Definition fx_observe_components {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (order : list (list X)) :
    bool * list (fx_observe_component_event X C B) :=
  let '(classes, class_events) := fx_observe_order EX S SS cb in
  let '(nodup, nd_events) := fx_observe_nodup EX (concat order) in
  let '(input, dep_events) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(unknown, unknown_events) := fxi_distinct_counted cb input in
  let '(cover, cover_events) := fx_observe_seteq EX (concat order) unknown in
  let '(nonempty, nonempty_events) := @fx_components_nonempty X C B order in
  let '(belongs, belongs_events) := @fx_components_in_classes X C B EX order classes in
  let '(forward, forward_events) := fx_observe_forward_run cb (System.constraints S) order in
  (nodup && cover && nonempty && belongs && forward,
    [FxComponentOrder class_events; FxComponentList (length order + length (concat order));
     FxComponentCompare nd_events; FxComponentDependency dep_events; FxComponentIndex
    unknown_events;
     FxComponentList (length order + length (concat order)); FxComponentCompare cover_events] ++
     nonempty_events ++ belongs_events ++ [FxComponentForward forward_events]).

(** Class scans use input lists and encoded-key widths. *)

Fixpoint fx_component_in_classes_budget {X} (EX : encoding X) (component : list X)
    (classes : list (list X)) : nat :=
  match classes with
  | [] => 1
  | class :: rest => 1 + fx_observe_seteq_budget EX component class +
      fx_component_in_classes_budget EX component rest
  end.

(** The full class-membership budget traverses every component and class. *)

Fixpoint fx_components_in_classes_budget {X} (EX : encoding X) (order classes : list (list X))
    : nat :=
  match order with
  | [] => 1
  | component :: rest => 1 + fx_component_in_classes_budget EX component classes +
      fx_components_in_classes_budget EX rest classes
  end.

(** The component bound includes both concat calls and all five strict checks. *)

Definition fx_observe_components_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) (order : list (list X)) : nat :=
  let classes := observation_order EX S SS in
  let unknown := unknowns EX S SS in
  fx_observe_order_budget EX S SS ib + fx_dep_build_budget EX S SS ib +
    8 * (1 + length order + length (concat order)) + fx_observe_nodup_budget EX (concat order) +
    fx_observe_seteq_budget EX (concat order) unknown +
    fx_components_in_classes_budget EX order classes +
    fx_observe_forward_budget EX S SS ib order.

(** Every event is charged for its own actual phase or list traversal. *)

Definition fx_observe_component_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_component_event X C B) : nat :=
  match event with
  | FxComponentOrder events => fx_observe_order_work ib events
  | FxComponentDependency events => fx_dep_events_work ib events
  | FxComponentIndex events => fx_index_adapter_work ib events
  | FxComponentForward events => fx_observe_forward_work ib events
  | FxComponentCompare events => fx_observe_compare_work events
  | FxComponentList n => 2 + n
  | FxComponentCase => 1
  end.

(** Work folds the captured component-check events. *)

Definition fx_observe_components_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_component_event X C B)) : nat :=
  fold_right (fun event n => fx_observe_component_event_work ib event + n) 0 events.

(** Order, dependency, index and forward events use embedded index sources and empty body groups,
    comparison events use their source groups, and other component events require none. *)

Definition fx_observe_component_event_source {X C A B D}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_observe_component_event X C B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FxComponentOrder events => Forall (fx_observe_order_event_source index_source) events /\
    bodies = []
  | FxComponentDependency events => fx_dep_body_source index_source events /\ bodies = []
  | FxComponentIndex events => fx_index_external_trace_adequacy index_source events /\ bodies = []
  | FxComponentForward events =>
      Forall (fx_observe_forward_event_source index_source) events /\ bodies = []
  | FxComponentCompare events => exists groups,
      Forall2 (fx_observe_compare_source source) events groups /\ bodies = concat groups
  | _ => bodies = []
  end.

(** Only actual comparisons contribute encoder-body budgets. *)

Definition fx_observe_component_external_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (event : fx_observe_component_event X C B) :
    nat :=
  match event with
  | FxComponentCompare events =>
      fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events
  | _ => 0
  end.

(** One component-check witness provides its result, callbacks and independent frame bound. *)

(** With index erasure and bounds, dependency source laws and comparison source laws, component
    checking preserves its result with source receipts and a work bound. *)
Definition fx_observe_components_source_statement : Prop :=
  forall (X C A B D : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (order : list (list X)),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_observe_components EX S SS cb order in
    exists bodies, Forall2 (fx_observe_component_event_source index_source source) events bodies /\
      out = observation_components_check EX S SS order /\
      fx_observe_components_work ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_observe_components_budget EX S SS ib order +
        fold_right (fun e n => fx_observe_component_external_budget budget e + n) 0 events.
