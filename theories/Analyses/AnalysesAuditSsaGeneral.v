(** * General liveness portfolio source

    The general fallback composes fact extraction, the actual naive rules run and tabulation.
    For example, a rejected rules program returns false without constructing answer rows.
    Builds on: liveness fact and tabulation sources and the naive rules materializer. *)
From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Views Require Import ViewsGraph.
From Galois.Rules Require Import RulesSyntax RulesSolve RulesAuditMaterializeDeltaTotal
  RulesAuditMaterializeReceipts RulesAuditMaterializeNaiveDimensions
  RulesAuditMaterializeNaiveTotal.
From Galois.Analyses Require Import AnalysesLiveness AnalysesRules AnalysesSsaLiveQuery
  AnalysesAuditSsaSparse AnalysesAuditSsaFacts AnalysesAuditSsaTabulate.
Import List.ListNotations.

(** * General liveness portfolio source *)

(** Predicate encoding is the actual fixed liveness-program constructor match. *)
Definition audit_live_predicate_code (p : pred) : positive :=
  match p with
  | PUse => 1%positive
  | PDef => 2%positive
  | PSucc => 3%positive
  | PNec => 4%positive
  | PDep => 5%positive
  | PExitUse => 6%positive
  | PLive => 7%positive
  | PNeeded => 8%positive
  | PReaches => 9%positive
  end.

(** Predicate arity is the actual fixed liveness-program constructor match. *)
Definition audit_live_predicate_arity (p : pred) : nat :=
  match p with
  | PUse | PDef | PNec | PExitUse | PLive | PNeeded => 2
  | PSucc | PDep | PReaches => 3
  end.

(** Internal predicate calls retain their constructor and the executed match frame. *)
Definition audit_live_predicate_source : mat_predicate_callback_source liveness_program
    (bool * pred) :=
  @MatPredicateCallbackSource pred liveness_program (bool * pred)
    (fun p code body => code = audit_live_predicate_code p /\ body = [(false, p)])
    (fun p value body => value = audit_live_predicate_arity p /\ body = [(true, p)])
    (fun _ => 1).

(** Fixed predicate matches satisfy the materializer's source and constant-frame laws. *)
Definition audit_live_predicate_source_statement : Prop :=
  mat_predicate_callback_receipts_statement liveness_program (bool * pred)
    audit_live_predicate_source /\
  mat_predicate_callback_input_bounds_statement liveness_program (bool * pred)
    audit_live_predicate_source
    (fun _ => 2) (fun _ => 2).

(** Under callback laws, one fact list and naive run give the general answer and branch work
    bound. *)
Definition audit_live_general_source_adapted_statement : Prop :=
  forall S O N E V C B (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (vv : var_view S O N E V C) (cb : audit_live_sparse_callbacks N E V B)
    n x (weight : B -> nat)
    node_source edge_source value_source out_source target_source use_source def_source exit_source
    node_budget edge_budget value_budget out_budget target_budget use_budget def_budget exit_budget,
    audit_live_sparse_callbacks_erase EN EE EV (var_point_uses vv) cb ->
    audit_graph_external_callback_adapter (sl_node_encode cb) weight node_source node_budget ->
    audit_graph_external_callback_adapter (sl_edge_encode cb) weight edge_source edge_budget ->
    audit_graph_external_callback_adapter (sl_value_encode cb) weight value_source value_budget ->
    audit_graph_external_callback_adapter (sl_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (sl_target cb) weight target_source target_budget ->
    audit_graph_external_callback_adapter (sl_use cb) weight use_source use_budget ->
    audit_graph_external_callback_adapter (sl_def cb) weight def_source def_budget ->
    audit_graph_external_callback_adapter (sl_exit cb) weight exit_source exit_budget ->
    let g := cfg (gview vv) in
    let '(facts, fact_events) := audit_live_facts_counted g cb in
    let fact_external := fold_right (fun event total => audit_live_fact_event_budget node_budget
      out_budget exit_budget edge_budget target_budget use_budget def_budget value_budget event +
        total) 0
      fact_events in
    exists output events receipts,
      mat_naive_program_run liveness_program facts output events /\
      mat_external_trace_receipts liveness_program (bool * pred) audit_live_predicate_source
        (fun _ => 2) (fun _ => 2) (mat_naive_callback_frames events) receipts /\
      let solver_work := mat_naive_work events +
        mat_external_body_work liveness_program (bool * pred) audit_live_predicate_source
          receipts in
      let solver_budget := mat_naive_whole_budget liveness_program facts (mat_naive_operand_max
        events) +
        mat_external_trace_allowance (bool * pred) receipts in
      match output with
      | None => general_live_query EN EE EV vv n x = false /\
        audit_live_facts_work weight fact_events + solver_work <=
          (N.to_nat 65536%N) *
            Nat.pow (audit_live_sparse_input_scale EN EE EV (var_point_uses vv)) 16 +
          fact_external + solver_budget
      | Some db =>
        let '(rows, build_events) := audit_live_tab_nodes g cb db (Graph.nodes g) in
        let '(answer, query_events) := audit_live_tab_probe cb rows n x in
        let tab_external := fold_right (fun event total => audit_live_tab_event_budget node_budget
          out_budget exit_budget (fun _ => 0) (fun _ => 0) def_budget use_budget value_budget event
            + total)
          0 (build_events ++ query_events) in
        answer = general_live_query EN EE EV vv n x /\
        audit_live_facts_work weight fact_events + solver_work + audit_live_tab_work weight
          build_events +
          audit_live_tab_work weight query_events <=
          (N.to_nat 65536%N) *
            Nat.pow (audit_live_sparse_input_scale EN EE EV (var_point_uses vv)) 16 +
          fact_external + solver_budget + audit_live_tab_input_budget EN EE EV vv db n x +
          tab_external
      end.

(** The general path combines predicate, fact, tabulation and naive-solver source contracts. *)
Definition audit_live_general_contract_statement : Prop :=
  audit_live_predicate_source_statement /\ audit_live_facts_adapted_statement /\
  audit_live_tab_adapted_statement /\ rules_naive_materialization_full_source_statement /\
  audit_live_general_source_adapted_statement.
