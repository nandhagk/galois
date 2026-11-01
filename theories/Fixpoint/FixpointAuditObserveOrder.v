(** * Observation SCC order

    This model retains dependency construction, graph preparation and the actual SCC traversal.
    For example, the outer List.rev keeps its legacy quadratic source cost.
    Builds on: FixpointAuditScheduleWrapper and GraphAuditScc. *)

From Stdlib Require Import List Arith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphAuditBase GraphAuditDfs
  GraphAuditScc.
From Galois.Fixpoint Require Import FixpointSystem FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper.
Import List.ListNotations.

Inductive fx_observe_order_event (X C B : Type) : Type :=
  | FxObserveOrderGraph (events : list (fx_dep_event X C B))
  | FxObserveOrderPrepare (events : list (audit_prepare_source_event X (X * X)
      (fx_dep_event X C B)))
  | FxObserveOrderScc (events : list (audit_tarjan_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B))))
  | FxObserveOrderReverse (length : nat).

Arguments FxObserveOrderGraph {X C B} _.

Arguments FxObserveOrderPrepare {X C B} _.

Arguments FxObserveOrderScc {X C B} _.

Arguments FxObserveOrderReverse {X C B} _.

(** The SCC phase assumes AUD-GR-SCC has replaced the two internal reversals. *)

Definition fx_observe_order {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
    list (list X) * list (fx_observe_order_event X C B) :=
  let '(graph, ix, graph_events) := fx_dep_graph_build EX S SS cb in
  let '(prepared, prep_events) := audit_prepare_source_counted EX graph (fx_dep_prepare_cb cb ix) in
  let '(result, scc_events) :=
    audit_scc_source_counted prepared (fx_dep_dfs_cb cb) (Graph.nodes graph) in
  let classes := components result in
  (rev classes, [FxObserveOrderGraph graph_events; FxObserveOrderPrepare prep_events;
    FxObserveOrderScc scc_events; FxObserveOrderReverse (length classes)]).

(** The post-SCC refinement and outer legacy reverse contribute their source work. *)

Definition fx_observe_order_event_work {X C B} (ib : fx_index_external_budget X C B)
    (event : fx_observe_order_event X C B) : nat :=
  match event with
  | FxObserveOrderGraph events => fx_dep_events_work ib events
  | FxObserveOrderPrepare events => audit_prepare_source_work (fx_dep_event_work ib) events
  | FxObserveOrderScc events =>
      audit_scc_source_work (fx_dep_event_work ib) events
  | FxObserveOrderReverse n => audit_graph_reverse_work n
  end.

(** The order work folds exactly the events from one captured execution. *)

Definition fx_observe_order_work {X C B} (ib : fx_index_external_budget X C B)
    (events : list (fx_observe_order_event X C B)) : nat :=
  fold_right (fun event n => fx_observe_order_event_work ib event + n) 0 events.

(** The order budget uses the actual input graph and native SCC intermediate. *)

Definition fx_observe_order_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) : nat :=
  let graph := dependency_graph EX S SS in
  let prepared := prepare EX graph in
  let classes := components (scc prepared) in
  let count := audit_graph_prepare_full_event_bound graph +
    audit_tarjan_input_event_bound prepared (Graph.nodes graph) in
  fx_dep_build_budget EX S SS ib + audit_prepare_source_budget EX graph +
    audit_scc_source_budget EX graph prepared (Graph.nodes graph) +
    64 * (1 + count) * fx_rpo_callback_max EX S SS ib +
    audit_graph_reverse_work (length classes).

(** The order phase has the source result and a native-input budget. *)

(** With index callback erasure and bounds, counted component ordering agrees with the original
    and fits its input budget. *)
Definition fx_observe_order_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    let '(out, events) := fx_observe_order EX S SS cb in
    out = observation_order EX S SS /\
      fx_observe_order_work ib events <= fx_observe_order_budget EX S SS ib.

(** A graph target or encoder capture satisfies the source relation for its dependency-event
    body. *)

Definition fx_observe_order_capture_source {X C B} (source : fx_index_external_source X C B)
    (capture : audit_graph_callback_capture X (X * X) (fx_dep_event X C B)) : Prop :=
  match capture with
  | AuditGraphTargetCapture _ _ _ _ _ body => fx_dep_body_source source body
  | AuditGraphEncodeCapture _ _ _ _ _ body => fx_dep_body_source source body
  end.

(** Graph, preparation and SCC events require their respective source relations; reverse events
    impose no source condition. *)

Definition fx_observe_order_event_source {X C B} (source : fx_index_external_source X C B)
    (event : fx_observe_order_event X C B) : Prop :=
  match event with
  | FxObserveOrderGraph events => fx_dep_body_source source events
  | FxObserveOrderPrepare events => Forall (fx_dep_prepare_source source) events
  | FxObserveOrderScc events =>
      Forall (fun event => Forall (fx_observe_order_capture_source source) (snd event)) events
  | FxObserveOrderReverse _ => True
  end.

(** The same captured order execution supplies callbacks, result and input-derived work bound. *)

(** With index erasure and bounds and dependency source laws, ordering has its original result,
    source evidence and a work bound. *)
Definition fx_observe_order_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B)
    (source : fx_index_external_source X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb source ->
    let '(out, events) := fx_observe_order EX S SS cb in
    Forall (fx_observe_order_event_source source) events /\ out = observation_order EX S SS /\
      fx_observe_order_work ib events <= fx_observe_order_budget EX S SS ib.
