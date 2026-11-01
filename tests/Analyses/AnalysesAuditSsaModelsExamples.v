(** * SSA and SEG model observations

    These examples exercise the strict mention scan, liveness lookup and SEG truth-table splice.
    For example, a match in the first position still records the later comparison.
    Builds on: collection encodings and the original SEG audit model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Analyses Require Import AnalysesAuditSsaQueryBase AnalysesAuditSeg
  AnalysesAuditSegBuilder.
Import List.ListNotations.

(** * Strict mention scanning *)

Example seg_mentions_retains_later_comparison :
    let '(found, events) :=
      @audit_seg_strict_mentions positive positive positive_encoding 1%positive
        [1%positive; 2%positive] in
    found = true /\ length events = 6.
Proof.
  split; reflexivity.
Qed.

(** * Portfolio and sparse graph helpers *)

Example live_list_has_duplicate_use :
    audit_list_has positive_encoding 2%positive [1%positive; 2%positive; 2%positive] = true.
Proof.
  reflexivity.
Qed.

Example live_list_missing_use :
    audit_list_has positive_encoding 3%positive [1%positive; 2%positive] = false.
Proof.
  reflexivity.
Qed.

Example seg_splice_truth_tables :
    audit_seg_splice_compose (false, true) (true, false) = (true, false).
Proof.
  reflexivity.
Qed.

Example seg_mentions_missing_value :
    fst (@audit_seg_strict_mentions positive positive positive_encoding 3%positive
      [1%positive; 2%positive]) = false.
Proof.
  reflexivity.
Qed.

Example seg_mentions_event_order :
    snd (@audit_seg_strict_mentions positive positive positive_encoding 1%positive
      [1%positive; 2%positive]) =
    [AuditSegEncode 1%positive 1%positive; AuditSegEncode 1%positive 1%positive;
     AuditSegEqual 1%positive 1%positive true; AuditSegEncode 1%positive 1%positive;
     AuditSegEncode 2%positive 2%positive; AuditSegEqual 1%positive 2%positive false].
Proof.
  reflexivity.
Qed.

Example seg_mentions_empty :
    @audit_seg_strict_mentions positive positive positive_encoding 1%positive [] = (false, []).
Proof.
  reflexivity.
Qed.
