(** * SSA prepared-index composition

    Graph preparation and value refresh retain one shared depth-first search receipt.
    For example, a batch uses the same graph and value indexes for every query.
    Builds on: graph source composition and SSA value reuse. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators GraphSemiDominators
  GraphAuditBase GraphAuditDfs GraphAuditVirtual GraphAuditSemiDominators GraphAuditLengauerTarjan
  GraphAuditDominators.
From Galois.Views Require Import ViewsSsaPoints.
From Galois.Analyses Require Import AnalysesLiveness AnalysesSsaLiveQuery AnalysesAuditSsaQueryBase
  AnalysesAuditSsaQuerySource AnalysesAuditSsaQueryGraph AnalysesAuditSsaReuse.
Import List.ListNotations.

(** * SSA prepared-index composition *)

(** The graph producer and value producer share the same original callbacks. *)
Definition audit_sq_prepare_graph_callbacks {N E V B} (cb : audit_sq_values_callbacks N E V B)
    : audit_virtual_base_callbacks N E B :=
  AuditVirtualBaseCallbacks N E B (sq_values_out cb) (sq_values_target cb)
    (sq_values_node_encode cb).

(** Under callback laws, shared graph and value preparation returns the source pair within its
    bound. *)
Definition audit_sq_prepared_source_statement : Prop :=
  forall B0 BE N E V B (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (s : ssa_points B0 BE N E V) (cb : audit_sq_values_callbacks N E V B)
    (source : E -> N * list B) (weight : B -> nat)
    node_source value_source out_source target_source source_source exit_source edge_source
    home_source
    node_budget value_budget out_budget target_budget source_budget exit_budget edge_budget
    home_budget,
    audit_sq_values_callbacks_erase EN EV s cb ->
    (forall e, fst (source e) = Graph.source (live_graph (point_model s)) e) ->
    audit_graph_external_callback_adapter (sq_values_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (sq_values_value_encode cb) weight value_source
      value_budget ->
    audit_graph_external_callback_adapter (sq_values_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (sq_values_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    audit_graph_external_callback_adapter (sq_values_exit cb) weight exit_source exit_budget ->
    audit_graph_external_callback_adapter (sq_values_edge cb) weight edge_source edge_budget ->
    audit_graph_external_callback_adapter (sq_values_home cb) weight home_source home_budget ->
    let g := live_graph (point_model s) in
    let graph_cb := audit_sq_prepare_graph_callbacks cb in
    let '(p, prep_events) := audit_prepare_source_counted EN g
      (audit_sq_graph_prepare_callbacks graph_cb) in
    let '(search, dfs_events) := audit_dfs_source_counted p (audit_sq_graph_dfs_callbacks graph_cb)
      FinSet.empty (Graph.entries g) in
    let '(rm, reduced_events) := audit_sq_reduced_source_rows p (sq_values_node_encode cb)
      (sq_values_target cb) source search (rev_append (postorder search) []) in
    let '(tg, (rows, t_events)) := audit_sq_t_source_counted p (sq_values_node_encode cb)
      (sq_values_target cb) source search rm (preorder search) in
    let '(tp, tp_events) := audit_prepare_source_counted EN tg
      (audit_sq_t_internal_prepare_callbacks (sq_values_node_encode cb) rows) in
    exists vp virtual_search virtual_prep_events virtual_dfs_events semi_state semi_events
      virtual_parents lt_events parents erase_events dom_receipt tree,
      audit_virtual_source_search EN g graph_cb = (vp, (virtual_search, (virtual_prep_events,
        virtual_dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode graph_cb)
        (audit_virtual_full_source source) vp virtual_search semi_state semi_events /\
      audit_lt_nested_run (audit_virtual_full_encode graph_cb) (audit_virtual_full_source source)
        virtual_search (SemiState.result semi_state) virtual_parents lt_events /\
      audit_erase_virtual_nested (sq_values_node_encode cb) virtual_parents = (parents,
        erase_events) /\
      dom_receipt = audit_dom_search_source_counted p parents
        (audit_sq_graph_dfs_callbacks graph_cb) /\
      tree = DomTree parents (pre_num (audit_dom_source_result dom_receipt))
        (post_num (audit_dom_source_result dom_receipt)) /\
      let '(closure, closure_events) := audit_sq_closure_source_rows tp (sq_values_node_encode cb)
        (preorder search) in
      let idx := SsaQueryGraph g search tree rm closure in
      let '(values, value_events) := audit_sq_reuse_values_counted idx cb in
      AuditLiveIndexes N E V idx values = audit_live_prepare EN EE EV s /\
      let graph_work := 64 + audit_graph_reverse_fast_work (length (postorder search)) +
        audit_prepare_source_work weight prep_events + audit_dfs_source_work weight dfs_events +
        audit_sq_reduced_source_work weight reduced_events + audit_sq_t_source_work weight
          t_events +
        audit_prepare_source_work (audit_sq_t_internal_work weight) tp_events +
        audit_prepare_source_work
          (fun e => audit_virtual_full_internal_event_work e + audit_virtual_full_body_event_work
            weight e)
          virtual_prep_events +
        audit_dfs_source_work
          (fun e => audit_virtual_full_internal_event_work e + audit_virtual_full_body_event_work
            weight e)
          virtual_dfs_events + audit_virtual_semi_stage_work weight semi_events +
        audit_virtual_lt_stage_work weight lt_events + audit_erase_nested_work weight erase_events +
        audit_dom_source_work weight (audit_dom_source_events dom_receipt) +
        audit_sq_closure_source_work weight closure_events in
      let virtual_budget := audit_sq_graph_virtual_call_budget node_budget out_budget target_budget
        source_budget in
      let graph_external :=
        fold_right (fun e n => audit_prepare_source_event_budget node_budget out_budget
          target_budget e + n) 0 prep_events +
        fold_right (fun item n => fold_right (fun call k => match call with
          | AuditGraphEncodeCapture _ _ _ v _ _ => node_budget v + k
          | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e + k
          end) 0 (snd item) + n) 0
          dfs_events +
        fold_right (fun e n => audit_sq_reduced_source_event_budget node_budget target_budget
          source_budget e + n) 0 reduced_events +
        fold_right (fun e n => audit_sq_t_source_event_budget node_budget target_budget
          source_budget e + n) 0 t_events +
        audit_prepare_source_body_work (audit_sq_t_internal_budget node_budget) tp_events +
        audit_prepare_source_body_work virtual_budget virtual_prep_events +
        audit_dfs_source_body_work virtual_budget virtual_dfs_events +
        audit_semi_producer_nested_body_work virtual_budget semi_events +
        audit_lt_nested_body_work virtual_budget lt_events +
        fold_right (fun e n => audit_sq_graph_erase_budget node_budget e + n) 0 erase_events +
        fold_right (fun e n => audit_sq_graph_dom_budget node_budget target_budget e + n) 0
          (audit_dom_source_events dom_receipt) +
        fold_right (fun e n => audit_sq_closure_source_event_budget node_budget e + n) 0
          closure_events in
      graph_work + audit_sq_values_source_work weight value_events <=
        audit_sq_graph_input_budget EN g + audit_sq_values_source_input_budget EN EV s +
        graph_external +
        fold_right (fun event total => audit_sq_values_source_event_budget node_budget out_budget
          exit_budget value_budget home_budget target_budget edge_budget event + total) 0
            value_events.

(** The prepared contract exposes graph, value reuse and batch source obligations. *)
Definition audit_sq_prepared_contract_statement : Prop :=
  audit_sq_graph_full_source_contract_statement /\ audit_sq_reuse_contract_statement /\
  audit_sq_prepared_source_statement.
