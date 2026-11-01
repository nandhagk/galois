(** * SSA graph-index reuse and batch queries

    Value refresh reuses the captured graph DFS, and batch queries retain each query trace.
    For example, two queries share one prepared graph while keeping two encoder receipts.
    Builds on: SSA query base and SSA query source models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditElements.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase.
From Galois.Views Require Import ViewsSsaPoints.
From Galois.Analyses Require Import AnalysesLiveness AnalysesSsaLiveQuery
  AnalysesAuditSsaQueryBase AnalysesAuditSsaQuerySource.
Import List.ListNotations.

(** * SSA graph-index reuse and batch queries *)

(** Refresh consumes the DFS already held by the graph index. *)
Definition audit_sq_reuse_values_counted {N E V B} (idx : ssa_query_graph N E)
    (cb : audit_sq_values_callbacks N E V B)
    : ssa_query_values N V * list (audit_sq_values_source_event N E V B) :=
  let '(uses, use_events) := audit_sq_values_source_uses cb (preorder (query_dfs idx)) in
  let '(rows, elements) := audit_map_elements uses in
  let '(defs, def_events) := audit_sq_values_source_defs cb rows in
  (SsaQueryValues defs uses, use_events ++ map SqValuesElements elements ++ def_events).

(** With matching graph and DFS and callback laws, refresh agrees with preparation within its
    bound. *)
Definition audit_sq_reuse_values_adapted_statement : Prop :=
  forall B0 BE N E V B (EN : encoding N) (EV : encoding V) (s : ssa_points B0 BE N E V)
    (idx : ssa_query_graph N E) (cb : audit_sq_values_callbacks N E V B) (weight : B -> nat)
    node_source value_source out_source exit_source edge_source home_source
    node_budget value_budget out_budget exit_budget edge_budget home_budget,
    audit_sq_values_callbacks_erase EN EV s cb ->
    query_cfg idx = live_graph (point_model s) ->
    query_dfs idx = dfs (prepare EN (live_graph (point_model s))) FinSet.empty
      (Graph.entries (live_graph (point_model s))) ->
    audit_graph_external_callback_adapter (sq_values_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (sq_values_value_encode cb) weight value_source
      value_budget ->
    audit_graph_external_callback_adapter (sq_values_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (sq_values_exit cb) weight exit_source exit_budget ->
    audit_graph_external_callback_adapter (sq_values_edge cb) weight edge_source edge_budget ->
    audit_graph_external_callback_adapter (sq_values_home cb) weight home_source home_budget ->
    let '(result, events) := audit_sq_reuse_values_counted idx cb in
    result = audit_live_values_from_graph EN EV s idx /\ result = prepare_ssa_query_values EN EV
      s /\
      audit_sq_values_source_work weight events <= audit_sq_values_source_input_budget EN EV s +
      fold_right (fun event total => audit_sq_values_source_event_budget node_budget out_budget
        exit_budget value_budget home_budget (fun _ => 0) edge_budget event + total) 0 events.

(** Batch evaluation keeps each query's event list without recomputing a callback. *)
Fixpoint audit_sq_batch_counted {N E V B} (encn : N -> positive * list B)
    (encv : V -> positive * list B) (idx : ssa_query_graph N E) (values : ssa_query_values N V)
    (queries : list (N * V))
    : list bool * list (list (audit_sq_query_source_event N E V B)) :=
  match queries with
  | [] => ([], [])
  | (n, x) :: rest =>
    let '(result, events) := audit_sq_query_source_counted encn encv idx values n x in
    let '(results, traces) := audit_sq_batch_counted encn encv idx values rest in
    (result :: results, events :: traces)
  end.

(** The batch budget is the sum of independent per-query input bounds. *)
Definition audit_sq_batch_input_budget {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (queries : list (N * V)) : nat :=
  S (length queries) + fold_right (fun item total =>
    audit_sq_query_source_input_budget EN EV idx values (fst item) (snd item) + total) 0 queries.

(** Batch agreement and cost use exactly the prepared indexes and captured per-query calls. *)
Definition audit_sq_batch_adapted_statement : Prop :=
  forall N E V B (EN : encoding N) (EV : encoding V) (idx : ssa_query_graph N E)
    (values : ssa_query_values N V) queries (encn : N -> positive * list B)
    (encv : V -> positive * list B) (weight : B -> nat)
    node_source value_source node_budget value_budget,
    (forall n, fst (encn n) = encode EN n) -> (forall x, fst (encv x) = encode EV x) ->
    audit_graph_external_callback_adapter encn weight node_source node_budget ->
    audit_graph_external_callback_adapter encv weight value_source value_budget ->
    let '(results, traces) := audit_sq_batch_counted encn encv idx values queries in
    results = map (fun q => ssa_live_query EN EV idx values (fst q) (snd q)) queries /\
      length traces = length queries /\
      S (length queries) + fold_right (fun events total =>
        audit_sq_query_source_work weight events + total) 0 traces <=
        audit_sq_batch_input_budget EN EV idx values queries +
        fold_right (fun events total => fold_right (fun event subtotal =>
          audit_sq_query_source_event_budget node_budget value_budget event + subtotal) 0 events +
          total) 0 traces.

(** The reuse contract combines value refresh and shared-index batch source obligations. *)
Definition audit_sq_reuse_contract_statement : Prop :=
  audit_sq_reuse_values_adapted_statement /\ audit_sq_batch_adapted_statement.
