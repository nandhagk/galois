(** * Exact wrapped trip-count examples

    Exact wrapped failure and no-wrap evidence have separate observations.
    For example, a sequence can fail after wrapping while its no-wrap checker rejects.
    Builds on: AnalysesLoopsFailure and AnalysesLoopsChrecTest. *)

From Stdlib Require Import List Bool Arith ZArith NArith.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsFailure.
From Galois.Tests.Analyses.Loops Require Import AnalysesLoopsChrecTest.
Import List.ListNotations Chrec Failure.

Example scev_affine_five :
  trip_count scev_test_env 32%positive Unsigned CmpLt
    (scev_test_affine 0 1) (IConst 5) = Some 5%N /\
  nowrap_check 32%positive Unsigned scev_test_env
    (scev_test_affine 0 1) (IConst 5) 5%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_zero_trip :
  trip_count scev_test_env 32%positive Unsigned CmpLt
    (scev_test_affine 0 1) (IConst 0) = Some 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_constant_word_never_fails :
  trip_count scev_test_env 32%positive Unsigned CmpLt
    (scev_test_affine 0 0) (IConst 5) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_wrapped_cycle_has_no_failure :
  trip_count scev_test_env 2%positive Unsigned CmpLt
    (scev_test_affine 0 2) (IConst 3) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_wrapped_first_failure :
  trip_count scev_test_env 2%positive Unsigned CmpNe
    (scev_test_affine 3 1) (IConst 0) = Some 1%N /\
  nowrap_check 2%positive Unsigned scev_test_env
    (scev_test_affine 3 1) (IConst 0) 1%N = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_unsigned_boundary :
  trip_count scev_test_env 32%positive Unsigned CmpLt
    (scev_test_affine 4294967294 1) (IConst 4294967295) = Some 1%N /\
  nowrap_check 32%positive Unsigned scev_test_env
    (scev_test_affine 4294967294 1) (IConst 4294967295) 1%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_inclusive_first_failure :
  trip_count scev_test_env 8%positive Unsigned CmpLe
    (scev_test_affine 0 1) (IConst 5) = Some 6%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_signed_descending :
  trip_count scev_test_env 8%positive Signed CmpNe
    (scev_test_affine 2 (-1)) (IConst (-3)) = Some 5%N /\
  nowrap_check 8%positive Signed scev_test_env
    (scev_test_affine 2 (-1)) (IConst (-3)) 5%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_signed_minimum_wrap_rejected :
  trip_count scev_test_env 3%positive Signed CmpLt
    (scev_test_affine (-4) (-1)) (IConst (-3)) = Some 1%N /\
  nowrap_check 3%positive Signed scev_test_env
    (scev_test_affine (-4) (-1)) (IConst (-3)) 1%N = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_arbitrary_base_at_zero :
  trip_count scev_test_env 8%positive Unsigned CmpLt
    (CRec (CGeo (CInv (IConst 7)) (CInv (IConst 3))) (CInv (IConst 2)))
    (IConst 11) = Some 2%N /\
  nowrap_check 8%positive Unsigned scev_test_env
    (CRec (CGeo (CInv (IConst 7)) (CInv (IConst 3))) (CInv (IConst 2)))
    (IConst 11) 2%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_nonlinear_trip_rejected :
  trip_count scev_test_env 2%positive Unsigned CmpLt
    (CGeo (CInv (IConst 1)) (CInv (IConst 2))) (IConst 3) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_width_two_observations :
  List.map (fun k => view_z 2%positive Unsigned (2 * Z.of_N k)) [0; 1; 2; 3]%N =
    [0; 2; 0; 2]%Z.
Proof.
  vm_compute; reflexivity.
Qed.
