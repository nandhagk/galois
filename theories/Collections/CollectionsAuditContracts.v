(** * Collection audit contract groups

    These proposition groups retain the prepared-key, dense-slot and persistent-forest claims.
    For example, bounded-slot refinement includes both conversion directions and removal.
    Builds on: G4 semantic contracts and the source-shaped collection observers. *)

From Galois.Collections Require Import CollectionsAuditState
  CollectionsAuditPrepared
  CollectionsAuditDense
  CollectionsAuditDenseSlots
  CollectionsAuditUnionFind
  CollectionsAuditComposite
  CollectionsAuditHistorical.

(** Key reuse retains injection, update and exact composite bit-length statements. *)
Definition prepared_key_refines_contract : Prop :=
  prepare_key_valid_statement /\ prepared_key_refinement_statement /\
  prepared_key_injection_statement /\ prepared_key_update_statement /\ prepared_pair_statement /\
  prepared_list_injection_statement /\ prepared_pair_bits_statement /\
    prepared_list_bits_statement /\
  prepared_pair_work_statement /\ prepared_list_work_statement /\
  audit_prepare_key_erases_statement /\ audit_prepared_lookup_erases_statement /\
  audit_prepared_update_erases_statement /\ audit_prepared_remove_erases_statement /\
  audit_prepared_encoder_reuse_statement /\ audit_prepared_lookup_source_bound_statement /\
  audit_prepared_update_source_bound_statement /\ audit_prepared_remove_source_bound_statement.

(** Dense-map refinement includes all original in/outside, canonicity and batch observations. *)
Definition dense_map_refines_contract : Prop :=
  slot_empty_statement /\ slot_update_statement /\ slot_present_update_statement /\
  slot_elements_statement /\ slot_canonical_statement /\ slot_to_map_statement /\
  slot_of_map_statement /\ slot_prepare_statement /\ slot_outside_statement /\
  slot_batch_refinement_statement /\ slot_update_refines_statement /\
    slot_remove_refines_statement /\
  slot_remove_frame_statement /\ slot_remove_outside_statement /\ slot_elements_refines_statement /\
  dense_token_prepare_statement /\ dense_token_read_statement /\ dense_token_scope_statement /\
  slot_batch_cost_statement /\ audit_read_slots_observation_statement /\
  audit_dense_prepare_erases_statement /\
  audit_dense_prepare_source_bound_statement /\ audit_slot_lookup_erases_statement /\
  audit_slot_update_erases_statement /\ audit_slot_remove_erases_statement /\
  audit_slot_elements_erases_statement /\ audit_slot_to_map_erases_statement /\
  audit_slot_of_map_erases_statement /\ audit_slot_elements_source_bound_statement /\
  audit_slot_to_map_source_bound_statement /\ audit_slot_of_map_source_bound_statement /\
  audit_dense_token_prepare_erases_statement /\ audit_dense_token_read_erases_statement /\
  audit_dense_token_prepare_source_bound_statement /\ audit_dense_token_read_source_bound_statement.

(** Source results and independently started branches are stated separately from native
  allocation. *)
Definition union_find_cost_contract : Prop :=
  trace_find_result_statement /\ trace_union_result_statement /\ trace_actions_result_statement /\
  trace_branch_sum_statement /\ union_source_work_statement /\
  audit_uf_find_fuel_erases_statement /\ audit_uf_find_erases_statement /\
  audit_uf_union_erases_statement /\ audit_uf_equivb_erases_statement /\
    audit_uf_keys_erases_statement /\
  audit_uf_history_erases_statement /\ audit_uf_of_unions_erases_statement /\
  audit_uf_find_fuel_count_statement /\ audit_uf_union_count_statement /\
    audit_uf_equivb_count_statement /\
  audit_uf_find_fuel_work_bound_statement /\ audit_uf_union_work_bound_statement /\
  audit_uf_equivb_work_bound_statement /\ audit_uf_keys_input_bound_statement /\
  audit_uf_history_bound_statement /\ audit_uf_branches_bound_statement /\
  audit_uf_of_unions_source_bound_statement.
