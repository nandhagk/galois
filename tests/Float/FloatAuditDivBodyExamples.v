(** * Shift and location traces

    These examples observe actual operands and ordered one-bit shifts.
    For example, shifting seven twice retains the intermediate record.
    Builds on: FloatAuditDivBody. *)

From Stdlib Require Import List ZArith PArith Floats.SpecFloat.
From Galois.Float Require Import FloatAuditDivBody.
Import List.ListNotations.

Example body_shift_two_trace :
  snd (float_body_shift_iter 2%positive (shr_record_of_loc 7 loc_Exact)) =
    [FloatBodyCase 0; FloatBodyCase 0;
     FloatBodyShiftOne (Build_shr_record 7 false false) (Build_shr_record 3 true false);
     FloatBodyCase 0;
     FloatBodyShiftOne (Build_shr_record 3 true false) (Build_shr_record 1 true true)].
Proof.
  vm_compute; reflexivity.
Qed.

Example body_location_exact_zero :
  float_body_location 0 0 =
    (loc_Exact, [FloatBodyParity 0; FloatBodyCase 17; FloatBodyCompare 0 0; FloatBodyCase 18]).
Proof.
  vm_compute; reflexivity.
Qed.

Example body_location_odd_boundary :
  fst (float_body_location 3 1) = loc_Inexact Lt /\
  fst (float_body_location 3 2) = loc_Inexact Gt.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example body_empty_work : float_body_work [] = 0%nat.
Proof.
  vm_compute; reflexivity.
Qed.

Example body_alignment_without_shift :
  fst (float_body_align 3 4 0 0 loc_Exact) = (Build_shr_record 0 false false, 0%Z).
Proof.
  vm_compute; reflexivity.
Qed.
