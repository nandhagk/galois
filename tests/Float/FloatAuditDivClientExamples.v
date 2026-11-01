(** * Float body client observations

    A client can inspect both the result and the operand-bearing cost events.
    For example, a zero divisor remains present in the division event.
    Builds on: FloatAuditDivBody. *)

From Stdlib Require Import List ZArith PArith Floats.SpecFloat.
From Galois.Float Require Import FloatAuditDivBody.
Import List.ListNotations.

Example body_client_zero_divisor_operand :
  exists dividend, In (FloatBodyDivide dividend 0) (snd (float_body_core 3 4 7 0 0 0)).
Proof.
  exists 7%Z; vm_compute; tauto.
Qed.

Example body_client_negative_rounding :
  fst (float_body_round 3 4 BinarySingleNaN.mode_ZR false (-1) 0 loc_Exact) = S754_nan.
Proof.
  vm_compute; reflexivity.
Qed.

Example body_client_shift_count :
  length (filter (fun event =>
    match event with
    | FloatBodyShiftOne _ _ => true
    | _ => false
    end)
    (snd (float_body_shift_iter 5%positive (Build_shr_record (-9) true false)))) = 5%nat.
Proof.
  vm_compute; reflexivity.
Qed.

Example body_client_overflow_modes :
  fst (float_body_fit 3 4 BinarySingleNaN.mode_NE false 7%positive 2) = S754_infinity false /\
  fst (float_body_fit 3 4 BinarySingleNaN.mode_ZR false 7%positive 2) =
    S754_finite false 7%positive 1.
Proof.
  vm_compute; split; reflexivity.
Qed.
