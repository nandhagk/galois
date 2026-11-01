(** * Dense collection contract adequacy

    These assemblies combine the independently checked prepared-key and dense-slot laws.
    For example, the dense contract includes both conversions and source-work bounds.
    Builds on: collection semantic and observer adequacy modules. *)

From Galois.Collections Require Import CollectionsAuditContracts CollectionsAuditStateENCAdequacy
  CollectionsAuditStateDENSEAdequacy CollectionsAuditCompositeAdequacy
  CollectionsAuditPreparedAdequacy CollectionsAuditDenseAdequacy
  CollectionsAuditDenseSlotsAdequacy CollectionsAuditHistoricalDENSEAdequacy.

(** * Contract assemblies *)

(** The prepared-key contract combines valid-key map laws, encoding lengths, conditional erasure
    and work bounds. *)
Theorem prepared_key_refines_contract_holds : prepared_key_refines_contract.
Proof.
  unfold prepared_key_refines_contract. repeat (
    first [exact prepare_key_valid | exact prepared_key_refinement | exact prepared_key_injection |
      exact prepared_key_update | exact prepared_pair | exact prepared_list_injection |
      exact prepared_pair_bits | exact prepared_list_bits | exact prepared_pair_work |
      exact prepared_list_work | exact audit_prepare_key_erases |
      exact audit_prepared_lookup_erases |
      exact audit_prepared_update_erases | exact audit_prepared_remove_erases |
      exact audit_prepared_encoder_reuse | exact audit_prepared_lookup_source_bound |
      exact audit_prepared_update_source_bound | exact audit_prepared_remove_source_bound | split]).
Qed.

(** The dense-map contract combines valid-slot refinement, conversions, conditional erasure and
    observer bounds. *)
Theorem dense_map_refines_contract_holds : dense_map_refines_contract.
Proof.
  unfold dense_map_refines_contract. repeat (
    first [exact slot_empty | exact slot_update | exact slot_present_update | exact slot_elements |
      exact slot_canonical | exact slot_to_map | exact slot_of_map | exact slot_prepare |
      exact slot_outside | exact slot_batch_refinement | exact slot_update_refines |
      exact slot_remove_refines | exact slot_remove_frame | exact slot_remove_outside |
      exact slot_elements_refines | exact dense_token_prepare | exact dense_token_read |
      exact dense_token_scope | exact slot_batch_cost | exact audit_read_slots_observation |
      exact audit_dense_prepare_erases | exact audit_dense_prepare_source_bound |
      exact audit_slot_lookup_erases | exact audit_slot_update_erases |
      exact audit_slot_remove_erases |
      exact audit_slot_elements_erases | exact audit_slot_to_map_erases |
      exact audit_slot_of_map_erases | exact audit_slot_elements_source_bound |
      exact audit_slot_to_map_source_bound | exact audit_slot_of_map_source_bound |
      exact audit_dense_token_prepare_erases | exact audit_dense_token_read_erases |
      exact audit_dense_token_prepare_source_bound | exact audit_dense_token_read_source_bound |
      split]).
Qed.
