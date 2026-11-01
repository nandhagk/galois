(** * Liveness portfolio source contracts

    Every choice selects its actual producer and query source contract.
    For example, sparse liveness materializes once before probing the stored row.
    Builds on: one-shot, prepared, sparse and reference rules source models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphAuditBase.
From Galois.Views Require Import ViewsSsaPoints.
From Galois.Analyses Require Import AnalysesLiveness AnalysesSsaLiveSets AnalysesAuditSsaQueryBase
  AnalysesAuditSsaQuerySource AnalysesAuditSsaPrepared AnalysesAuditSsaOneShot
  AnalysesAuditSsaSparse AnalysesAuditSsaGeneral.
Import List.ListNotations.

(** * Liveness portfolio source contracts *)

(** Under callback laws, a shared sparse materialization and probe return the source answer within
    the stated work bound. *)
Definition audit_live_sparse_query_adapted_statement : Prop :=
  forall N E V B (EN : encoding N) (EE : encoding E) (EV : encoding V) (p : point_uses N E V)
    (cb : audit_live_sparse_callbacks N E V B) n x (weight : B -> nat)
    node_source edge_source value_source out_source target_source source_source def_source
    exit_source use_source
    node_budget edge_budget value_budget out_budget target_budget source_budget def_budget
    exit_budget use_budget,
    audit_live_sparse_callbacks_erase EN EE EV p cb ->
    audit_graph_external_callback_adapter (sl_node_encode cb) weight node_source node_budget ->
    audit_graph_external_callback_adapter (sl_edge_encode cb) weight edge_source edge_budget ->
    audit_graph_external_callback_adapter (sl_value_encode cb) weight value_source value_budget ->
    audit_graph_external_callback_adapter (sl_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (sl_target cb) weight target_source target_budget ->
    audit_graph_external_callback_adapter (sl_source cb) weight source_source source_budget ->
    audit_graph_external_callback_adapter (sl_def cb) weight def_source def_budget ->
    audit_graph_external_callback_adapter (sl_exit cb) weight exit_source exit_budget ->
    audit_graph_external_callback_adapter (sl_use cb) weight use_source use_budget ->
    let '(rows, (prep_events, events)) := audit_live_sparse_counted EN p cb in
    let '(answer, probe_events) := audit_live_sparse_probe cb rows n x in
    let external := fold_right (fun event total => audit_live_sparse_event_budget node_budget
      out_budget exit_budget edge_budget source_budget def_budget use_budget value_budget event +
        total)
      0 (events ++ probe_events) in
    answer = sparse_live_at EN EV (sparse_live_materialize EN EE EV p) n x /\
    audit_prepare_source_work weight prep_events + audit_live_sparse_work weight events +
      audit_live_sparse_work weight probe_events <=
      audit_live_sparse_input_budget EN EE EV p +
      4096 * Nat.pow (S (Pos.size_nat (encode EN n) + Pos.size_nat (encode EV x))) 4 +
      fold_right (fun event total => audit_prepare_source_event_budget node_budget out_budget
        target_budget event + total) 0 prep_events + external.

(** Each explicit portfolio branch retains its own actual source producer. *)
Definition audit_live_portfolio_choice_source (choice : audit_live_choice) : Prop :=
  match choice with
  | AuditLiveGeneral => audit_live_general_contract_statement
  | AuditLiveOneShot => audit_live_one_source_adapted_statement
  | AuditLivePrepared => audit_sq_prepared_contract_statement /\
    audit_sq_query_source_contract_statement
  | AuditLiveSparse => audit_live_sparse_source_adapted_statement /\
    audit_live_sparse_probe_statement /\
    audit_live_sparse_query_adapted_statement
  end.

(** The portfolio fixes every source branch and retains its established semantic boundaries. *)
Definition audit_live_portfolio_contract_statement : Prop :=
  (forall choice, audit_live_portfolio_choice_source choice) /\
  audit_live_values_reuse_statement /\ audit_live_values_refresh_statement /\
  audit_live_refresh_query_exact_statement /\ audit_live_prepared_agrees_statement /\
  audit_live_prepared_batch_statement /\ audit_live_select_exact_statement /\
  audit_live_all_points_agrees_statement /\ audit_live_all_points_three_statement /\
  audit_live_one_shot_exact_statement.
