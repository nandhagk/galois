(** * Collection family closure adequacy

    This file composes the installed collection erasure, source-work and input-budget proofs into
    the ten source-family contracts. For example, the public closure retains both callback and
    internal encoder-budget obligations from its component theorems.
    Builds on: the collection adequacy leaves and contract assemblies. *)

From Galois.Collections Require Import CollectionsAuditFamilyClosure
  CollectionsAuditTrieAdequacy CollectionsAuditPrimitiveAdequacy
  CollectionsAuditEncodingAdequacy CollectionsAuditElementsAdequacy
  CollectionsAuditMapAdequacy CollectionsAuditFinSetAdequacy
  CollectionsAuditUnionAdequacy CollectionsAuditInterAdequacy
  CollectionsAuditMapTraverseAdequacy CollectionsAuditMapFoldAdequacy
  CollectionsAuditPreparedAdequacy CollectionsAuditDenseAdequacy
  CollectionsAuditDenseSlotsAdequacy CollectionsAuditUnionFindAdequacy
  CollectionsAuditUnionFindAdaptersAdequacy CollectionsAuditEncoderBudgetAdequacy
  CollectionsAuditUnionFindWholeAdequacy CollectionsAuditContractsDENSEAdequacy
  CollectionsAuditContractsUFAdequacy CollectionsAuditCallbackAdequacy
  CollectionsAuditAdaptedENCAdequacy CollectionsAuditAdaptedUFAdequacy
  CollectionsAuditTraversalBudgetAdequacy CollectionsAuditDenseInputAdequacy.

(** * Family theorem composition *)

(** Selects an installed leaf without replacing any of its source or budget premises. *)
Local Ltac audit_cl_leaf :=
  first [ exact audit_trie_get_erases
        | exact audit_trie_set_erases
        | exact audit_trie_remove_erases
        | exact audit_map_code_get_erases
        | exact audit_trie_left_source_adequate
        | exact audit_trie_right_source_adequate
        | exact audit_trie_value_source_adequate
        | exact audit_trie_node_source_adequate
        | exact audit_positive_eqb_erases
        | exact audit_positive_succ_erases
        | exact audit_nat_encode_erases
        | exact audit_N_encode_erases
        | exact audit_positive_encode_erases
        | exact audit_bool_encode_erases
        | exact audit_unit_encode_erases
        | exact audit_z_encode_erases
        | exact audit_emit_code_erases
        | exact audit_stream_positive_erases
        | exact audit_pair_encode_erases
        | exact audit_emit_list_erases
        | exact audit_list_encode_erases
        | exact audit_sum_encode_erases
        | exact audit_option_encode_erases
        | exact audit_trie_elements_erases
        | exact audit_map_elements_erases
        | exact audit_finset_elements_erases
        | exact audit_map_get_erases
        | exact audit_map_set_erases
        | exact audit_map_remove_erases
        | exact audit_finset_of_list_erases
        | exact audit_finset_add_erases
        | exact audit_finset_mem_erases
        | exact audit_finset_remove_erases
        | exact audit_finset_union_erases
        | exact audit_finset_inter_erases
        | exact audit_map_transform_erases
        | exact audit_map_union_erases
        | exact audit_map_fold_erases
        | exact audit_prepare_key_erases
        | exact audit_prepared_lookup_erases
        | exact audit_prepared_update_erases
        | exact audit_prepared_remove_erases
        | exact audit_dense_prepare_erases
        | exact audit_slot_lookup_erases
        | exact audit_prepare_slot_erases
        | exact audit_slot_read_erases
        | exact audit_prepare_slots_erases
        | exact audit_read_slots_erases
        | exact audit_slot_update_erases
        | exact audit_slot_remove_erases
        | exact audit_slot_elements_erases
        | exact audit_slot_of_map_erases
        | exact audit_slot_to_map_erases
        | exact audit_dense_token_prepare_erases
        | exact audit_dense_token_read_erases
        | exact audit_uf_find_fuel_erases
        | exact audit_uf_find_erases
        | exact audit_uf_union_erases
        | exact audit_uf_equivb_erases
        | exact audit_uf_keys_erases
        | exact audit_uf_history_erases
        | exact audit_uf_of_unions_erases
        | exact audit_trie_get_source_work_bound
        | exact audit_trie_update_source_work_bound
        | exact audit_positive_eqb_source_bound
        | exact audit_map_get_source_work_bound
        | exact audit_map_set_source_work_bound
        | exact audit_map_remove_source_work_bound
        | exact audit_finset_of_list_source_bound
        | exact audit_finset_union_source_bound
        | exact audit_finset_inter_source_bound
        | exact audit_map_transform_source_bound
        | exact audit_map_union_source_bound
        | exact audit_map_fold_source_work_bound
        | exact audit_trie_elements_work_bound
        | exact audit_map_elements_work_bound
        | exact audit_finset_elements_work_bound
        | exact audit_prepared_lookup_source_bound
        | exact audit_prepared_update_source_bound
        | exact audit_prepared_remove_source_bound
        | exact audit_dense_prepare_source_bound
        | exact audit_slot_lookup_source_bound
        | exact audit_slot_update_source_bound
        | exact audit_slot_remove_source_bound
        | exact audit_slot_elements_source_bound
        | exact audit_slot_of_map_source_bound
        | exact audit_slot_to_map_source_bound
        | exact audit_dense_token_prepare_source_bound
        | exact audit_dense_token_read_source_bound
        | exact audit_prepare_slot_source_bound
        | exact audit_slot_read_source_bound
        | exact audit_prepare_slots_source_bound
        | exact audit_read_slots_source_bound
        | exact audit_uf_find_fuel_work_bound
        | exact audit_uf_union_work_bound
        | exact audit_uf_equivb_work_bound
        | exact audit_uf_keys_input_bound
        | exact audit_uf_history_bound
        | exact audit_uf_branches_bound
        | exact audit_uf_of_unions_source_bound
        | exact audit_uf_pair_of_unions_erases
        | exact audit_uf_list_of_unions_erases
        | exact audit_uf_pair_of_unions_source_bound
        | exact audit_uf_list_of_unions_source_bound
        | exact audit_trie_get_run_total
        | exact audit_trie_get_run_correct
        | exact audit_trie_update_run_total
        | exact audit_trie_update_run_correct
        | exact audit_trie_get_trace_adequate
        | exact audit_trie_update_trace_adequate
        | exact audit_map_code_get_run_total
        | exact audit_map_code_get_run_correct
        | exact audit_trie_access_source_clauses
        | exact audit_positive_succ_run_total
        | exact audit_positive_succ_run_correct
        | exact audit_nat_encode_run_total
        | exact audit_nat_encode_run_correct
        | exact audit_base_encoder_input_bound
        | exact audit_pair_input_bound
        | exact audit_list_input_bound
        | exact audit_sum_option_input_bound
        | exact audit_uf_whole_input_bound
        | exact audit_uf_pair_whole_input_bound
        | exact audit_uf_list_whole_input_bound
        | exact audit_uf_branches_whole_input_bound
        | exact prepared_key_refines_contract_holds
        | exact dense_map_refines_contract_holds
        | exact union_find_cost_contract_holds
        | exact audit_external_callback_observed
        | exact audit_uf_whole_input_bound_adapted
        | exact audit_uf_pair_whole_input_bound_adapted
        | exact audit_uf_list_whole_input_bound_adapted
        | exact audit_uf_branches_whole_input_bound_adapted
        | exact audit_pair_input_bound_adapted
        | exact audit_list_input_bound_adapted
        | exact audit_map_transform_adapted_input_bound
        | exact audit_map_union_adapted_input_bound
        | exact audit_map_fold_adapted_input_bound
        | exact audit_prepare_key_whole_input_bound
        | exact audit_dense_prepare_whole_input_bound
        | exact audit_slot_lookup_whole_input_bound
        | exact audit_slot_update_whole_input_bound
        | exact audit_slot_remove_whole_input_bound
        | exact audit_slot_elements_whole_input_bound
        | exact audit_slot_of_map_whole_input_bound
        | exact audit_slot_to_map_whole_input_bound
        | exact audit_dense_token_prepare_whole_input_bound
        | exact audit_dense_token_read_whole_input_bound
        | exact audit_prepare_slot_whole_input_bound
        | exact audit_slot_read_whole_input_bound
        | exact audit_prepare_slots_whole_input_bound
        | exact audit_read_slots_whole_input_bound].

(** Primitive erasure claims retain the input hypotheses of each primitive adequacy leaf. *)
Theorem audit_cl_primitive_erasure_closure : audit_cl_primitive_erasure_closure_statement.
Proof.
  unfold audit_cl_primitive_erasure_closure_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** Source-work claims retain each operation's own input and callback work assumptions. *)
Theorem audit_cl_source_work_closure : audit_cl_source_work_closure_statement.
Proof.
  unfold audit_cl_source_work_closure_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** Pair and list union-find adapters retain their per-invocation source bounds. *)
Theorem audit_cl_composite_union_find_closure :
  audit_cl_composite_union_find_closure_statement.
Proof.
  unfold audit_cl_composite_union_find_closure_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** The full source contract combines primitive erasure, source-work and adapter closures. *)
Theorem audit_cl_full_source_contract : audit_cl_full_source_contract_statement.
Proof.
  unfold audit_cl_full_source_contract_statement,
    audit_cl_primitive_erasure_closure_statement,
    audit_cl_source_work_closure_statement,
    audit_cl_composite_union_find_closure_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** Literal-run claims connect source traces to concrete trie and unary encoder bodies. *)
Theorem audit_cl_literal_body_closure : audit_cl_literal_body_closure_statement.
Proof.
  unfold audit_cl_literal_body_closure_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** Whole-input bounds keep each genuine external leaf-body premise explicit. *)
Theorem audit_cl_whole_input_closure : audit_cl_whole_input_closure_statement.
Proof.
  unfold audit_cl_whole_input_closure_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** Complete source adequacy combines literal execution, whole-input bounds and contract bundles. *)
Theorem audit_cl_complete_source_contract : audit_cl_complete_source_contract_statement.
Proof.
  unfold audit_cl_complete_source_contract_statement,
    audit_cl_full_source_contract_statement,
    audit_cl_primitive_erasure_closure_statement,
    audit_cl_source_work_closure_statement,
    audit_cl_composite_union_find_closure_statement,
    audit_cl_literal_body_closure_statement,
    audit_cl_whole_input_closure_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** Adapted contracts tie external source work to each actual typed callback invocation. *)
Theorem audit_cl_adapted_source_contract : audit_cl_adapted_source_contract_statement.
Proof.
  unfold audit_cl_adapted_source_contract_statement,
    audit_cl_complete_source_contract_statement,
    audit_cl_full_source_contract_statement,
    audit_cl_primitive_erasure_closure_statement,
    audit_cl_source_work_closure_statement,
    audit_cl_composite_union_find_closure_statement,
    audit_cl_literal_body_closure_statement,
    audit_cl_whole_input_closure_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** Dense whole-input contracts retain all numeric operand budgets used internally. *)
Theorem audit_cl_dense_whole_source_contract :
  audit_cl_dense_whole_source_contract_statement.
Proof.
  unfold audit_cl_dense_whole_source_contract_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.

(** The public contract composes adapted source laws with every independent dense input budget. *)
Theorem audit_cl_public_source_contract : audit_cl_public_source_contract_statement.
Proof.
  unfold audit_cl_public_source_contract_statement,
    audit_cl_adapted_source_contract_statement,
    audit_cl_complete_source_contract_statement,
    audit_cl_full_source_contract_statement,
    audit_cl_primitive_erasure_closure_statement,
    audit_cl_source_work_closure_statement,
    audit_cl_composite_union_find_closure_statement,
    audit_cl_literal_body_closure_statement,
    audit_cl_whole_input_closure_statement,
    audit_cl_dense_whole_source_contract_statement.
  repeat (first [audit_cl_leaf | split]).
Qed.
