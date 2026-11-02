(** * Arithmetic regressions for modular prefix counting

    These finite computations exercise the fixed floor producer and wrapped failure counts.
    For example, signed two-bit counting treats minus two and minus one as below zero.
    Builds on: AnalysesAuditScevModCountCorrectness, AnalysesAuditScevModCountPlain and
    AnalysesScev. *)

From Stdlib Require Import NArith ZArith List.
From Galois.Analyses Require Import AnalysesScev AnalysesAuditScevModCountPlain
  AnalysesAuditScevModCountCorrectness.

(** * Floor computations *)

(** A nontrivial Euclidean execution agrees with the independently summed staircase. *)
Example arithmetic_floor_positive :
  audit_floor_sum_fast 13 17 29 23 = audit_floor_sum_reference 13 17 29 23.
Proof.
  vm_compute; reflexivity.
Qed.

(** An empty range completes with the empty sum. *)
Example arithmetic_floor_empty : audit_floor_sum_counted 0 7 12 9 = (0%N, 1%N, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** A zero modulus is rejected before any step is performed. *)
Example arithmetic_floor_rejected : audit_floor_sum_counted 13 0 29 23 = (0%N, 0%N, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** The unit modulus absorbs every quotient in one update. *)
Example arithmetic_floor_unit : audit_floor_sum_counted 5 1 7 3 = (85%N, 1%N, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** A malformed live zero-modulus state retains the specified total division behavior. *)
Example arithmetic_floor_malformed :
  audit_floor_step (AuditFloorState 4 0 3 1 7 false 2) =
    AuditFloorState 0 3 0 13 7 false 3.
Proof.
  vm_compute; reflexivity.
Qed.

(** A completed malformed state is preserved exactly, including its update counter. *)
Example arithmetic_floor_done_malformed :
  audit_floor_step (AuditFloorState 4 0 99 17 7 true 2) =
    AuditFloorState 4 0 99 17 7 true 2.
Proof.
  vm_compute; reflexivity.
Qed.

(** * Wrapped comparisons *)

(** Two unsigned upper-half values fail the strict comparison in one full period. *)
Example arithmetic_count_unsigned :
  scev_mod_count 2%positive Unsigned CmpLt 0 1 2 4 = 2%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** Signed bias orders the negative half below zero. *)
Example arithmetic_count_signed :
  scev_mod_count 2%positive Signed CmpLt (-2) 1 0 4 = 2%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** Descending signed values fail the inclusive comparison only at the initial one. *)
Example arithmetic_count_descending :
  scev_mod_count 2%positive Signed CmpLe 1 (-1) 0 4 = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** Disequality fails exactly at the selected residue in a complete period. *)
Example arithmetic_count_disequality :
  scev_mod_count 2%positive Unsigned CmpNe 0 1 1 4 = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The largest unsigned bound accepts every value under inclusive comparison. *)
Example arithmetic_count_upper_boundary :
  scev_mod_count 2%positive Unsigned CmpLe 0 1 3 12 = 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The smallest unsigned bound rejects every value under strict comparison. *)
Example arithmetic_count_lower_boundary :
  scev_mod_count 2%positive Unsigned CmpLt 0 1 0 9 = 9%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** One-bit signed disequality remains exact across repeated wraps. *)
Example arithmetic_count_one_bit :
  scev_mod_count 1%positive Signed CmpNe (-1) 1 0 4 = 2%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** An empty modular prefix contains no failures. *)
Example arithmetic_count_empty :
  scev_mod_count 3%positive Signed CmpNe (-17) 29 7 0 = 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** * Symbolic coefficient coverage *)

(** Arbitrary coefficient magnitudes satisfy the proved bit bound without enumerating them. *)
Example arithmetic_symbolic_live_bits (a b : N) :
  (audit_floor_state_bits
    (N.iter 12 audit_floor_step (AuditFloorState 17 19 a b 0 false 0)) <=
    10 * (N.size 17 + N.size 19 + N.size a + N.size b + 1))%N.
Proof.
  apply audit_floor_live_bits; exact (N.lt_0_succ 18).
Qed.

(** The public exactness theorem supplies a distinct-index witness for this signed client. *)
Example arithmetic_exact_client :
  exists indices : list N,
    audit_failed_indices 2%positive Signed CmpLt (-2) 1 0 4 indices /\
    scev_mod_count 2%positive Signed CmpLt (-2) 1 0 4 = N.of_nat (length indices).
Proof.
  apply scev_mod_count_exact.
Qed.
