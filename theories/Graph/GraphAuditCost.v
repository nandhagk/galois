(** * Graph source-cost facade

    The facade exposes the complete leaf source contracts without adding bridge dependencies.
    For example, the default dominator contract does not wait for the Semi-NCA selector proof.
    Builds on: graph audit leaf models and their source adapters. *)

From Galois.Graph Require Export GraphAuditBase GraphAuditDfs GraphAuditVirtual
  GraphAuditVirtualAdapter
  GraphAuditScc GraphAuditWto GraphAuditLoops GraphAuditSemiDominators GraphAuditLengauerTarjan
  GraphAuditSemiNca GraphAuditDominators GraphAuditDominatorsAdapter GraphAuditDominatorSelect
  GraphAuditFrontier GraphAuditFrontierAdapter GraphAuditIdf.

(** The family contract names the actual source and adapted boundary for every graph producer. *)

Definition graph_audit_source_contract_statement : Prop :=
  audit_prepare_source_contract_statement /\ audit_dfs_source_contract_statement /\
  audit_virtual_full_source_statement /\ audit_virtual_full_callbacks_statement /\
  audit_virtual_entries_full_statement /\ audit_erase_nested_statement /\
  audit_virtual_source_search_adapted_statement /\ audit_scc_source_contract_statement /\
  audit_wto_source_contract_statement /\ audit_loop_full_source_contract_statement /\
  audit_semi_producer_nested_erasure_statement /\ audit_semi_producer_nested_unique_statement /\
  audit_semi_producer_nested_bound_statement /\ audit_lt_nested_erasure_statement /\
  audit_lt_nested_unique_statement /\ audit_lt_nested_bound_statement /\
  audit_default_dom_single_adapted_statement /\ audit_virtual_nca_source_full_contract_statement /\
  audit_flat_source_full_contract_statement /\ audit_check_idom_source_full_contract_statement /\
  audit_dom_select_source_full_contract_statement /\ audit_frontier_source_adapted_statement /\
  audit_idf_full_source_contract_statement.
