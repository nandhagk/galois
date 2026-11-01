(** * Foreign callback adequacy

    The adapter laws apply to the exact result and body returned by each call.
    For example, the budget applies to the body returned for the observed argument.
    Builds on: CollectionsAuditCallback. *)

From Galois.Collections Require Import CollectionsAuditCallback.

(** * Observed calls *)

(** The actual returned callback body satisfies its source law and budget. *)
Theorem audit_external_callback_observed : audit_external_callback_observed_statement.
Proof.
  intros A R B call work source budget Hadapter argument.
  destruct (call argument) as [result body] eqn:Hcall.
  simpl.
  split.
  - eapply audit_external_callback_source; eassumption.
  - eapply audit_external_callback_input_bound; eassumption.
Qed.
