(** * Foreign-adapted union-find source bounds

    Actual-call laws supply only the external encoder budgets consumed by concrete proofs.
    For example, a pair key uses the bodies returned by both component calls on that key.
    Builds on: CollectionsAuditAdapted, callback adequacy and whole union-find adequacy. *)

From Galois.Collections Require Import CollectionsAuditAdapted CollectionsAuditCallbackAdequacy
  CollectionsAuditUnionFindWholeAdequacy.

(** * Actual foreign encoder invocations *)

(** Given a genuine external encoder adapter with actual input/result/body source laws and
    per-key work bounds, find, union, equivalence and history work obey their input upper bounds. *)
Theorem audit_uf_whole_input_bound_adapted : audit_uf_whole_input_bound_adapted_statement.
Proof.
  intros K CE enc work budget source Hadapter.
  apply audit_uf_whole_input_bound; intro key.
  exact (proj2 (audit_external_callback_observed _ _ _ _ _ _ _ Hadapter key)).
Qed.

(** Given genuine adapters with actual input/result/body source laws and per-component work
    bounds for both encoders, pair-key union source work is bounded by its history input
    recurrence. *)
Theorem audit_uf_pair_whole_input_bound_adapted : audit_uf_pair_whole_input_bound_adapted_statement.
Proof.
  intros A B EA EB first second fw sw fb sb inputs fs ss Hfirst Hsecond.
  apply audit_uf_pair_whole_input_bound.
  - intro key; exact (proj2 (audit_external_callback_observed _ _ _ _ _ _ _ Hfirst key)).
  - intro key; exact (proj2 (audit_external_callback_observed _ _ _ _ _ _ _ Hsecond key)).
Qed.

(** Given a genuine element adapter with actual input/result/body source laws and per-element
    work bounds, list-key union source work is bounded by its occurrence-sensitive history
    recurrence. *)
Theorem audit_uf_list_whole_input_bound_adapted : audit_uf_list_whole_input_bound_adapted_statement.
Proof.
  intros A CE element work budget inputs source Hadapter.
  apply audit_uf_list_whole_input_bound; intro key.
  exact (proj2 (audit_external_callback_observed _ _ _ _ _ _ _ Hadapter key)).
Qed.

(** Given a genuine external encoder adapter with actual input/result/body source laws and
    per-key work bounds, summed branch source work is bounded by their summed history
    recurrences. *)
Theorem audit_uf_branches_whole_input_bound_adapted :
  audit_uf_branches_whole_input_bound_adapted_statement.
Proof.
  intros K CE enc work budget left right forest source Hadapter.
  apply audit_uf_branches_whole_input_bound; intro key.
  exact (proj2 (audit_external_callback_observed _ _ _ _ _ _ _ Hadapter key)).
Qed.
