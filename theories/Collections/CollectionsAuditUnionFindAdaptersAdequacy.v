(** * Composite-key union-find adequacy

    Concrete pair and list encoders preserve the original union-list results and frame bounds.
    For example, repeated list elements remain repeated encoder calls at each key access.
    Builds on: CollectionsAuditUnionFindAdapters and encoding and forest adequacy. *)

From Galois.Collections Require Import CollectionsAuditUnionFindAdapters
  CollectionsAuditUnionFindAdequacy CollectionsAuditEncodingAdequacy.

(** * Composite erasure and source frames *)

(** When both component encoders agree with their original encodings on every component,
    the pair-key union history returns exactly the original fold using the fixed pair encoding. *)
Theorem audit_uf_pair_of_unions_erases : audit_uf_pair_of_unions_erases_statement.
Proof.
  intros A B EA EB first second e1 e2 inputs Hfirst Hsecond.
  apply audit_uf_of_unions_erases; intros [a b].
  apply audit_pair_encode_erases; apply Hfirst || apply Hsecond.
Qed.

(** When the element encoder agrees with its original encoding on every element, the
    list-key union history returns exactly the original fold using the fixed list encoding. *)
Theorem audit_uf_list_of_unions_erases : audit_uf_list_of_unions_erases_statement.
Proof.
  intros A E element e inputs Henc.
  apply audit_uf_of_unions_erases; intro key.
  apply audit_list_encode_erases; intros x Hx; apply Henc.
Qed.

(** Pair-key union source work is at most four times its persistent-history frame budget
    from the empty forest plus the actual primitive work retained in that pair-key history. *)
Theorem audit_uf_pair_of_unions_source_bound : audit_uf_pair_of_unions_source_bound_statement.
Proof.
  intros A B EA EB first second first_work second_work inputs.
  apply audit_uf_of_unions_source_bound.
Qed.

(** List-key union source work is at most four times its persistent-history frame budget
    from the empty forest plus the actual primitive work retained in that list-key history. *)
Theorem audit_uf_list_of_unions_source_bound : audit_uf_list_of_unions_source_bound_statement.
Proof.
  intros A E element work inputs; apply audit_uf_of_unions_source_bound.
Qed.
