(** * Adapted encoder budget adequacy

    Foreign component adapters supply bounds for the exact calls made by composite encoders.
    For example, a pair charges the actual left and right returned bodies.
    Builds on: CollectionsAuditAdapted and encoder budget adequacy. *)

From Galois.Collections Require Import CollectionsAuditAdapted CollectionsAuditCallback
  CollectionsAuditCallbackAdequacy CollectionsAuditEncoderBudgetAdequacy.

(** * Adapted pair and list calls *)

(** Pair encoding uses the observed foreign component budgets. *)
Theorem audit_pair_input_bound_adapted : audit_pair_input_bound_adapted_statement.
Proof.
  intros A B EA EB first second first_work second_work first_budget second_budget key
    first_source second_source Hfirst Hsecond.
  apply audit_pair_input_bound.
  - intro a. exact (proj2 (audit_external_callback_observed _ _ _ _ _ _ _ Hfirst a)).
  - intro b. exact (proj2 (audit_external_callback_observed _ _ _ _ _ _ _ Hsecond b)).
Qed.

(** List encoding uses the observed budget for each actual element call. *)
Theorem audit_list_input_bound_adapted : audit_list_input_bound_adapted_statement.
Proof.
  intros A E element work budget keys source Hadapter.
  apply audit_list_input_bound.
  intro a. exact (proj2 (audit_external_callback_observed _ _ _ _ _ _ _ Hadapter a)).
Qed.
