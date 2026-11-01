(** * Rules join cost contract

    This proposition combines the fixed phase contracts without asserting their proofs.
    For example, its firing component retains each strategy's own intermediate bindings.
    Builds on: the Rules audit index, selection, callback and firing modules. *)

From Galois.Rules Require Import RulesAuditIndex RulesAuditIndexCounts RulesAuditJoinSyntax
  RulesAuditRelations RulesAuditRelationCallbacks RulesAuditNestedPrepare RulesAuditMultiwayPrepare
  RulesAuditPrepareCallbacks RulesAuditNestedProbe RulesAuditMultiwayProbe RulesAuditTerminal
  RulesAuditTerminalCallbacks RulesAuditUniverse RulesAuditNestedSelection
  RulesAuditMultiwaySelection
  RulesAuditFiring RulesAuditFiringCallbacks RulesAuditJoin.

(** Both indexed strategies use actual source phases, callback receipts and quantitative bounds. *)
Definition rules_index_cost : Prop :=
  mat_index_full_erases_statement /\
  mat_index_full_input_bound_statement /\
  mat_variable_full_input_bound_statement /\
  mat_index_full_source_statement /\
  mat_index_row_counts_statement /\
  mat_index_fold_counts_statement /\
  mat_index_add_run_total_statement /\
  mat_join_syntax_erasure_statement /\
  rules_join_relations_erasure_statement /\
  rules_join_relations_row_count_statement /\
  rules_join_relations_selected_cost_statement /\
  rules_join_relations_input_bound_statement /\
  rules_relations_external_source_statement /\
  rules_prepare_nested_full_erases_statement /\
  rules_prepare_nested_full_input_bound_statement /\
  rules_prepare_multiway_full_erases_statement /\
  rules_nested_prepare_source_statement /\
  rules_multiway_prepare_source_statement /\
  rules_nested_probe_erasure_statement /\
  rules_run_nested_selected_cost_statement /\
  rules_multiway_probe_erasure_statement /\
  rules_run_multiway_selected_cost_statement /\
  rules_terminal_erasure_statement /\
  rules_terminal_selected_cost_statement /\
  rules_positive_filter_erasure_statement /\
  rules_universe_erasure_statement /\
  rules_universe_selected_cost_statement /\
  rules_nested_selection_input_bound_statement /\
  rules_nested_selection_source_statement /\
  rules_multiway_selection_count_statement /\
  rules_multiway_selection_input_bound_statement /\
  rules_multiway_selection_source_statement /\
  rules_firing_tail_input_bound_statement /\
  rules_firing_tail_source_statement /\
  rules_join_firing_input_bound_statement /\
  rules_join_firing_source_statement.
