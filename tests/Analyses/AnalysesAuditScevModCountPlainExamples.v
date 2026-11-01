(** * Modular counting examples

    These computed examples exercise floor sums, modular counts and source charges.
    For example, a zero modulus selects the rejected floor-sum branch.
    Builds on: AnalysesAuditScevModCountPlain and AnalysesAuditScevCost. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Analyses Require Import AnalysesScev AnalysesAuditScevCost
  AnalysesAuditScevModCountPlain.
Import List.ListNotations.

(** A positive floor sum returns its result, update count and completion flag. *)
Example floor_positive : audit_floor_sum_counted 4 5 3 1 = (3%N, 4%N, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** The independent reference yields the same value on this input. *)
Example floor_reference : audit_floor_sum_reference 4 5 3 1 = 3%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty input has an empty sum. *)
Example floor_empty : audit_floor_sum_fast 0 5 3 1 = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** A zero modulus is rejected with no updates. *)
Example floor_zero_modulus : audit_floor_sum_counted 4 0 3 1 = (0%N, 0%N, false).
Proof.
  vm_compute. reflexivity.
Qed.

(** The two-bit unsigned comparison fails at both upper-half values. *)
Example count_boundary : scev_mod_count 2%positive Unsigned CmpLt 0 1 2 4 = 2%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty count range has no failures. *)
Example count_empty : scev_mod_count 2%positive Unsigned CmpLt 0 1 2 0 = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** A width charge depends on its operand. *)
Example charge_width : count_frame_weight (AuditArithmetic 41 [3%N]) = 4%nat.
Proof.
  vm_compute. reflexivity.
Qed.

(** A malformed charge operand list takes the default branch. *)
Example charge_malformed : count_frame_weight (AuditArithmetic 41 []) = 1%nat.
Proof.
  vm_compute. reflexivity.
Qed.
