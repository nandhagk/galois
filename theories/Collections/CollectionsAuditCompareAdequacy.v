(** * Adequacy of positive comparisons

    Counted comparison follows the standard continuation comparison and bounds each
    recursive inspection. For example, different low bits still compare the remaining bits.
    Builds on: CollectionsAuditCompare and Stdlib positive arithmetic. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsAuditCompare.

(** Continuation comparison preserves its accumulator and charges at most two frames per bit. *)
Theorem audit_positive_compare_cont : audit_positive_compare_cont_statement.
Proof.
  intros acc left right; revert acc left.
  induction right as [right IH | right IH |]; intros acc left; destruct left as [left | left |];
    cbn [CollectionsAuditCompare.audit_positive_compare_cont Pos.compare_cont Pos.size_nat
      Nat.min audit_positive_compare_source_work];
    try (split; [reflexivity | unfold audit_positive_compare_source_work; cbn; lia]).
  - specialize (IH acc left).
    destruct (CollectionsAuditCompare.audit_positive_compare_cont acc left right)
      as [result events]; cbn [audit_positive_compare_source_work List.length] in *.
    destruct IH as [Hresult Hbound]; split; [exact Hresult |].
    unfold audit_positive_compare_source_work in *; cbn [List.length]; lia.
  - specialize (IH Lt left).
    destruct (CollectionsAuditCompare.audit_positive_compare_cont Lt left right)
      as [result events]; cbn [audit_positive_compare_source_work List.length] in *.
    destruct IH as [Hresult Hbound]; split; [exact Hresult |].
    unfold audit_positive_compare_source_work in *; cbn [List.length]; lia.
  - specialize (IH Gt left).
    destruct (CollectionsAuditCompare.audit_positive_compare_cont Gt left right)
      as [result events]; cbn [audit_positive_compare_source_work List.length] in *.
    destruct IH as [Hresult Hbound]; split; [exact Hresult |].
    unfold audit_positive_compare_source_work in *; cbn [List.length]; lia.
  - specialize (IH acc left).
    destruct (CollectionsAuditCompare.audit_positive_compare_cont acc left right)
      as [result events]; cbn [audit_positive_compare_source_work List.length] in *.
    destruct IH as [Hresult Hbound]; split; [exact Hresult |].
    unfold audit_positive_compare_source_work in *; cbn [List.length]; lia.
Qed.

(** Public counted comparison erases to standard positive comparison. *)
Theorem audit_positive_compare : audit_positive_compare_statement.
Proof.
  intros left right.
  pose proof (audit_positive_compare_cont Eq left right) as Hcompare.
  unfold CollectionsAuditCompare.audit_positive_compare, Pos.compare.
  destruct (CollectionsAuditCompare.audit_positive_compare_cont Eq left right)
    as [result events]; exact (proj1 Hcompare).
Qed.

(** Both order wrappers preserve results and include their fixed branch overhead. *)
Theorem audit_positive_order : audit_positive_order_statement.
Proof.
  intros left right.
  pose proof (audit_positive_compare_cont Eq left right) as Hcompare.
  unfold audit_positive_ltb, audit_positive_leb, CollectionsAuditCompare.audit_positive_compare.
  unfold Pos.ltb, Pos.leb, Pos.compare.
  destruct (CollectionsAuditCompare.audit_positive_compare_cont Eq left right)
    as [result events].
  destruct Hcompare as [Hresult Hbound].
  rewrite <- Hresult; destruct result;
    cbn [fst snd]; unfold audit_positive_order_source_work; repeat split; lia.
Qed.
