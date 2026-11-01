(** * Composite work adequacy

    Historical work records agree with the prepared code widths and callback totals.
    For example, the empty list has one stream node and no callbacks.
    Builds on: CollectionsAuditComposite and prepared encoding adequacy. *)

From Galois.Collections Require Import CollectionsAuditComposite
  CollectionsAuditStateENCAdequacy.

(** * Pair and list work *)

(** Pair work accounts for both component codes and callback charges. *)
Theorem prepared_pair_work : prepared_pair_work_statement.
Proof.
  intros A B EA EB cost a b.
  unfold CollectionsAuditComposite.prepared_pair_work.
  cbn [composite_stream_nodes composite_emitted_bits composite_left_bits
    composite_right_bits composite_callback_work].
  rewrite prepared_pair_bits. repeat split; reflexivity.
Qed.

(** List work accounts for all element codes and callback charges. *)
Theorem prepared_list_work : prepared_list_work_statement.
Proof.
  intros A EA cost xs.
  unfold CollectionsAuditComposite.prepared_list_work.
  cbn [composite_list_stream_nodes composite_list_elements composite_list_emitted_bits
    composite_list_input_bits composite_list_callbacks].
  rewrite prepared_list_bits. repeat split; reflexivity.
Qed.
