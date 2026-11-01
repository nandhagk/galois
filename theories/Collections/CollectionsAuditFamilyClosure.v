(** * Canonical collections source adequacy closure

    These are complete future theorem types for the source-shaped family below.
    The groups make the full source-erasure and source-work obligations reviewable
    as one AUD-CL interface while keeping each operation's assumptions explicit.
    For example, primitive erasure is combined with source-work obligations.
    Builds on: the counted collection model modules. *)

From Galois.Collections Require Import CollectionsAuditTrie
  CollectionsAuditPrimitive
  CollectionsAuditEncoding
  CollectionsAuditElements
  CollectionsAuditMap
  CollectionsAuditFinSet
  CollectionsAuditUnion
  CollectionsAuditInter
  CollectionsAuditMapTraverse
  CollectionsAuditMapFold
  CollectionsAuditPrepared
  CollectionsAuditDense
  CollectionsAuditDenseSlots
  CollectionsAuditUnionFind
  CollectionsAuditUnionFindAdapters
  CollectionsAuditEncoderBudget
  CollectionsAuditUnionFindWhole
  CollectionsAuditContracts
  CollectionsAuditCallback
  CollectionsAuditAdapted
  CollectionsAuditTraversalBudget
  CollectionsAuditDenseInput.

(** The primitive closure combines erasure and accessor obligations across collection operations. *)
Definition audit_cl_primitive_erasure_closure_statement : Prop :=
  audit_trie_get_erases_statement /\ audit_trie_set_erases_statement /\
  audit_trie_remove_erases_statement /\ audit_map_code_get_erases_statement /\
  audit_trie_left_source_adequate_statement /\ audit_trie_right_source_adequate_statement /\
  audit_trie_value_source_adequate_statement /\ audit_trie_node_source_adequate_statement /\
  audit_positive_eqb_erases_statement /\ audit_positive_succ_erases_statement /\
  audit_nat_encode_erases_statement /\ audit_N_encode_erases_statement /\
  audit_positive_encode_erases_statement /\ audit_bool_encode_erases_statement /\
  audit_unit_encode_erases_statement /\ audit_z_encode_erases_statement /\
  audit_emit_code_erases_statement /\ audit_stream_positive_erases_statement /\
  audit_pair_encode_erases_statement /\ audit_emit_list_erases_statement /\
  audit_list_encode_erases_statement /\ audit_sum_encode_erases_statement /\
  audit_option_encode_erases_statement /\ audit_trie_elements_erases_statement /\
  audit_map_elements_erases_statement /\ audit_finset_elements_erases_statement /\
  audit_map_get_erases_statement /\ audit_map_set_erases_statement /\
  audit_map_remove_erases_statement /\ audit_finset_of_list_erases_statement /\
  audit_finset_add_erases_statement /\ audit_finset_mem_erases_statement /\
  audit_finset_remove_erases_statement /\ audit_finset_union_erases_statement /\
  audit_finset_inter_erases_statement /\ audit_map_transform_erases_statement /\
  audit_map_union_erases_statement /\ audit_map_fold_erases_statement /\
  audit_prepare_key_erases_statement /\ audit_prepared_lookup_erases_statement /\
  audit_prepared_update_erases_statement /\ audit_prepared_remove_erases_statement /\
  audit_dense_prepare_erases_statement /\ audit_slot_lookup_erases_statement /\
  audit_prepare_slot_erases_statement /\ audit_slot_read_erases_statement /\
  audit_prepare_slots_erases_statement /\ audit_read_slots_erases_statement /\
  audit_slot_update_erases_statement /\ audit_slot_remove_erases_statement /\
  audit_slot_elements_erases_statement /\ audit_slot_of_map_erases_statement /\
  audit_slot_to_map_erases_statement /\ audit_dense_token_prepare_erases_statement /\
  audit_dense_token_read_erases_statement /\ audit_uf_find_fuel_erases_statement /\
  audit_uf_find_erases_statement /\ audit_uf_union_erases_statement /\
  audit_uf_equivb_erases_statement /\ audit_uf_keys_erases_statement /\
  audit_uf_history_erases_statement /\ audit_uf_of_unions_erases_statement.

(** The source-work closure combines the bounds for the counted collection operations. *)
Definition audit_cl_source_work_closure_statement : Prop :=
  audit_trie_get_source_work_bound_statement /\ audit_trie_update_source_work_bound_statement /\
  audit_positive_eqb_source_bound_statement /\ audit_map_get_source_work_bound_statement /\
  audit_map_set_source_work_bound_statement /\ audit_map_remove_source_work_bound_statement /\
  audit_finset_of_list_source_bound_statement /\ audit_finset_union_source_bound_statement /\
  audit_finset_inter_source_bound_statement /\ audit_map_transform_source_bound_statement /\
  audit_map_union_source_bound_statement /\ audit_map_fold_source_work_bound_statement /\
  audit_trie_elements_work_bound_statement /\ audit_map_elements_work_bound_statement /\
  audit_finset_elements_work_bound_statement /\ audit_prepared_lookup_source_bound_statement /\
  audit_prepared_update_source_bound_statement /\ audit_prepared_remove_source_bound_statement /\
  audit_dense_prepare_source_bound_statement /\ audit_slot_lookup_source_bound_statement /\
  audit_slot_update_source_bound_statement /\ audit_slot_remove_source_bound_statement /\
  audit_slot_elements_source_bound_statement /\ audit_slot_of_map_source_bound_statement /\
  audit_slot_to_map_source_bound_statement /\ audit_dense_token_prepare_source_bound_statement /\
  audit_dense_token_read_source_bound_statement /\ audit_prepare_slot_source_bound_statement /\
  audit_slot_read_source_bound_statement /\ audit_prepare_slots_source_bound_statement /\
  audit_read_slots_source_bound_statement /\ audit_uf_find_fuel_work_bound_statement /\
  audit_uf_union_work_bound_statement /\ audit_uf_equivb_work_bound_statement /\
  audit_uf_keys_input_bound_statement /\ audit_uf_history_bound_statement /\
  audit_uf_branches_bound_statement /\ audit_uf_of_unions_source_bound_statement.

(** Pair and list union-find adapters share erasure and source-work obligations. *)
Definition audit_cl_composite_union_find_closure_statement : Prop :=
  audit_uf_pair_of_unions_erases_statement /\ audit_uf_list_of_unions_erases_statement /\
  audit_uf_pair_of_unions_source_bound_statement /\
  audit_uf_list_of_unions_source_bound_statement.

(** The full source contract combines primitive erasure, work and composite union-find
  obligations. *)
Definition audit_cl_full_source_contract_statement : Prop :=
  audit_cl_primitive_erasure_closure_statement /\
  audit_cl_source_work_closure_statement /\
  audit_cl_composite_union_find_closure_statement.

(** Source-run adequacy connects the event folds to the literal trie and unary encoding bodies. *)
Definition audit_cl_literal_body_closure_statement : Prop :=
  audit_trie_get_run_total_statement /\ audit_trie_get_run_correct_statement /\
  audit_trie_update_run_total_statement /\ audit_trie_update_run_correct_statement /\
  audit_trie_get_trace_adequate_statement /\ audit_trie_update_trace_adequate_statement /\
  audit_map_code_get_run_total_statement /\ audit_map_code_get_run_correct_statement /\
  audit_trie_access_source_clauses_statement /\
  audit_positive_succ_run_total_statement /\ audit_positive_succ_run_correct_statement /\
  audit_nat_encode_run_total_statement /\ audit_nat_encode_run_correct_statement.

(** Whole encoder and persistent-operation recurrences assume only genuine external leaf bodies. *)
Definition audit_cl_whole_input_closure_statement : Prop :=
  audit_base_encoder_input_bound_statement /\ audit_pair_input_bound_statement /\
  audit_list_input_bound_statement /\ audit_sum_option_input_bound_statement /\
  audit_uf_whole_input_bound_statement /\ audit_uf_pair_whole_input_bound_statement /\
  audit_uf_list_whole_input_bound_statement /\ audit_uf_branches_whole_input_bound_statement.

(** The final collection closure includes literal adequacy and every whole-operation input bound. *)
Definition audit_cl_complete_source_contract_statement : Prop :=
  audit_cl_full_source_contract_statement /\ audit_cl_literal_body_closure_statement /\
  audit_cl_whole_input_closure_statement /\
  prepared_key_refines_contract /\ dense_map_refines_contract /\ union_find_cost_contract.

(** Actual foreign source relations are bound to every retained collection callback invocation. *)
Definition audit_cl_adapted_source_contract_statement : Prop :=
  audit_cl_complete_source_contract_statement /\ audit_external_callback_observed_statement /\
  audit_uf_whole_input_bound_adapted_statement /\
  audit_uf_pair_whole_input_bound_adapted_statement /\
  audit_uf_list_whole_input_bound_adapted_statement /\
  audit_uf_branches_whole_input_bound_adapted_statement /\
  audit_pair_input_bound_adapted_statement /\ audit_list_input_bound_adapted_statement /\
  audit_map_transform_adapted_input_bound_statement /\
  audit_map_union_adapted_input_bound_statement /\ audit_map_fold_adapted_input_bound_statement.

(** Prepared and dense closure uses only operand budgets for all internal numeric encoders. *)
Definition audit_cl_dense_whole_source_contract_statement : Prop :=
  audit_prepare_key_whole_input_bound_statement /\
    audit_dense_prepare_whole_input_bound_statement /\
  audit_slot_lookup_whole_input_bound_statement /\ audit_slot_update_whole_input_bound_statement /\
  audit_slot_remove_whole_input_bound_statement /\
    audit_slot_elements_whole_input_bound_statement /\
  audit_slot_of_map_whole_input_bound_statement /\ audit_slot_to_map_whole_input_bound_statement /\
  audit_dense_token_prepare_whole_input_bound_statement /\
  audit_dense_token_read_whole_input_bound_statement /\
    audit_prepare_slot_whole_input_bound_statement /\
  audit_slot_read_whole_input_bound_statement /\ audit_prepare_slots_whole_input_bound_statement /\
  audit_read_slots_whole_input_bound_statement.

(** Final collection closure binds foreign source bodies and every independent internal input
  budget. *)
Definition audit_cl_public_source_contract_statement : Prop :=
  audit_cl_adapted_source_contract_statement /\ audit_cl_dense_whole_source_contract_statement.
