(** * Complete fixed memory source-contract closure

    These conjunctions close literal library adapters before the independently bounded public calls.
    For example, the memo query uses the saved incoming map and legacy clobbers build all rows.
    Builds on: concrete memory encoders, full producer models and unchanged semantic boundaries. *)

From Galois.Analyses Require Import AnalysesAuditMemoryState AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryEffects AnalysesAuditMemoryDistinct AnalysesAuditMemoryIndex
  AnalysesAuditMemoryTable AnalysesAuditMemoryRawNext AnalysesAuditMemoryInputBudget
  AnalysesAuditMemorySharedBudget AnalysesAuditMemorySearch AnalysesAuditMemorySearchInputBudget
  AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryClobbersSource AnalysesAuditMemoryMemoExecute
  AnalysesAuditMemoryMemoExecuteBound AnalysesAuditMemoryMemoPublicSource
  AnalysesAuditMemoryMemoSnapshot AnalysesAuditMemoryMemoSnapshotSource
  AnalysesAuditMemoryLegacyCfg AnalysesAuditMemoryLegacyGuard AnalysesAuditMemoryLegacySlice
  AnalysesAuditMemoryLegacySliceFull AnalysesAuditMemoryLegacyChecker
  AnalysesAuditMemoryLegacySuccessor AnalysesAuditMemoryLegacyNoClobber
  AnalysesAuditMemoryLegacyInputBudget AnalysesAuditMemoryLegacyProposalSource
  AnalysesAuditMemoryLegacySetupSource AnalysesAuditMemoryLegacyProjectionSource
  AnalysesAuditMemoryLegacyBytes AnalysesAuditMemoryPhiProducer AnalysesAuditMemoryPhiInputBudget
  AnalysesAuditMemoryPhiConsumer AnalysesAuditMemoryPhiSetup AnalysesAuditMemoryMemoAdaptedSource
  AnalysesAuditMemorySearchAdaptedSource AnalysesAuditMemoryPhiAdaptedSource
  AnalysesAuditMemorySnapshotPublic AnalysesAuditMemoryPhiPublic
  AnalysesAuditMemoryMemoLegacyPlain AnalysesAuditMemoryMemoLegacySource.

(** Internal closure combines scope injectivity, initial and busy-cut properties, encoder and
    search erasures, predecessor cost and memo-tree execution. *)
Definition audit_memory_internal_body_closure_statement : Prop :=
  scope_code_injective_statement /\ memo_initial_statement /\
  busy_cut_coverage_statement /\ busy_cut_trace_statement /\
  audit_memory_version_encode_erases_statement /\ audit_memory_footprint_encode_erases_statement /\
  audit_memory_scope_encode_erases_statement /\ audit_memory_memo_key_encode_erases_statement /\
  audit_memory_effects_from_erases_statement /\ audit_memory_effect_get_erases_statement /\
  audit_memory_distinct_from_erases_statement /\ audit_memory_distinct_erases_statement /\
  audit_memory_result_index_erases_statement /\ audit_memory_effect_table_erases_statement /\
  audit_memory_raw_next_erases_statement /\ audit_memory_search_run_erases_statement /\
  audit_memory_walk_index_erases_statement /\ audit_memory_clobbers_source_erases_statement /\
  audit_memo_pred_correct_statement /\
  audit_memo_execute_tree_statement /\
  audit_memo_execute_plain_erases_statement.

(** Memo closure combines input-work bounds, initialization and query erasures, query semantics
    and saved-snapshot query and refresh contracts. *)
Definition audit_memory_memo_source_closure_statement : Prop :=
  audit_memory_encoders_input_bound_statement /\ audit_raw_next_whole_input_bound_statement /\
  audit_memory_table_whole_input_bound_statement /\ audit_search_whole_input_bound_statement /\
  audit_memory_walk_index_whole_input_bound_statement /\
  audit_memory_clobbers_whole_input_bound_statement /\
  audit_memory_memo_initial_source_erases_statement /\
  audit_memory_memo_initial_whole_input_bound_statement /\
  audit_memory_memo_public_source_erases_statement /\
  audit_memory_memo_public_whole_input_bound_statement /\
  audit_memory_memo_query_semantics_statement /\
  audit_memory_memo_query_execution_contract_statement /\
  audit_snapshot_refresh_source_hit_statement /\ audit_snapshot_refresh_source_miss_statement /\
  audit_snapshot_refresh_whole_input_bound_statement /\
  audit_snapshot_query_saved_values_statement /\ audit_snapshot_query_source_erases_statement /\
  audit_snapshot_query_whole_input_bound_statement.

(** Legacy closure combines graph and checker erasures and bounds, projection setup and
    production, and conditional historical-byte preservation. *)
Definition audit_memory_legacy_source_closure_statement : Prop :=
  audit_legacy_cfg_erases_statement /\ audit_legacy_guard_erases_statement /\
  audit_legacy_successors_erases_statement /\
  audit_legacy_slice_nodes_erases_statement /\ audit_legacy_slice_full_erases_statement /\
  audit_legacy_pair_check_erases_statement /\ audit_legacy_check_nodes_erases_statement /\
  audit_legacy_no_clobber_erases_statement /\ audit_legacy_cfg_whole_input_bound_statement /\
  audit_legacy_no_clobber_whole_input_bound_statement /\
  audit_legacy_occurrence_source_erases_statement /\
  audit_legacy_occurrence_whole_input_bound_statement /\
  audit_legacy_projection_setup_erases_statement /\
    audit_legacy_setup_whole_input_bound_statement /\
  audit_legacy_projection_source_erases_statement /\
  audit_legacy_projection_check_source_erases_statement /\
  audit_legacy_projection_check_whole_input_bound_statement /\
  audit_legacy_projection_historical_bytes_statement.

(** Phi closure combines producer and setup erasures and bounds, returned-field closures and
    pruning semantics. *)
Definition audit_memory_phi_source_closure_statement : Prop :=
  audit_phi_cycle_flags_erases_statement /\ audit_phi_output_counted_erases_statement /\
  audit_phi_producer_whole_input_bound_statement /\
  audit_memory_phi_prune_counted_erases_statement /\
  audit_memory_phi_prune_whole_input_bound_statement /\
  audit_phi_output_optional_erases_statement /\ audit_phi_output_fields_erases_statement /\
  audit_phi_closure_whole_input_bound_statement /\ audit_memory_phi_producer_erases_statement /\
  audit_memory_phi_prune_semantics_statement.

(** The complete closure combines internal, memo, legacy and phi source obligations. *)
Definition audit_memory_complete_source_contract_statement : Prop :=
  audit_memory_internal_body_closure_statement /\ audit_memory_memo_source_closure_statement /\
  audit_memory_legacy_source_closure_statement /\ audit_memory_phi_source_closure_statement.

(** Plain snapshot refresh and saved queries preserve completed-entry semantics without ghost
  logs. *)
Definition audit_memory_snapshot_plain_closure_statement : Prop :=
  audit_snapshot_refresh_plain_erases_statement /\
    audit_snapshot_refresh_semantic_valid_statement /\
  audit_snapshot_query_semantic_valid_statement /\ audit_snapshot_query_coverage_statement /\
  audit_snapshot_query_complete_statement /\
  audit_snapshot_refresh_observation_context_statement /\
  audit_snapshot_refresh_epoch_compare_erases_statement /\
  audit_snapshot_query_current_coverage_statement /\
    audit_snapshot_query_current_complete_statement.

(** Adapted closure combines complete and plain-snapshot contracts with source bounds using
    the actual foreign callback inputs, results and bodies. *)
Definition audit_memory_adapted_source_contract_statement : Prop :=
  audit_memory_complete_source_contract_statement /\
    audit_memory_snapshot_plain_closure_statement /\
  audit_memory_memo_public_whole_input_bound_adapted_statement /\
  audit_memory_memo_initial_whole_input_bound_adapted_statement /\
  audit_snapshot_query_whole_input_bound_adapted_statement /\
  audit_snapshot_refresh_whole_input_bound_adapted_statement /\
  audit_memory_clobbers_whole_input_bound_adapted_statement /\
  audit_legacy_projection_check_whole_input_bound_adapted_statement /\
  audit_memory_phi_prune_whole_input_bound_adapted_statement.

(** Memo-threaded legacy closure combines checker and conditional byte semantics, erasure and
    source bounds for the same produced state and pairs. *)
Definition audit_memory_memo_legacy_contract_statement : Prop :=
  audit_memory_memo_legacy_semantics_statement /\
    audit_memory_memo_legacy_source_erases_statement /\
  audit_memo_legacy_lookup_source_bound_statement /\
  audit_memory_memo_legacy_whole_input_bound_statement.

(** The public closure combines memory source, snapshot, phi and memo-threaded legacy
    obligations. *)
Definition audit_memory_public_source_contract_statement : Prop :=
  audit_memory_adapted_source_contract_statement /\ audit_memory_memo_legacy_contract_statement /\
  audit_memory_phi_public_semantics_statement /\ audit_memory_phi_public_projection_statement /\
  audit_phi_optional_closure_source_bound_statement /\
  audit_phi_total_closure_source_bound_statement.
