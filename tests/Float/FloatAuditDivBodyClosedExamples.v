(** * Closed finite division observations

    These computations compare the traced helpers with the pinned numeric operations.
    For example, division of two finite significands retains its exact location.
    Builds on: FloatAuditDivBody and the pinned Float helpers. *)

From Stdlib Require Import ZArith Floats.SpecFloat.
From Galois.Float Require Import FloatAuditDivBody.

Example body_finite_division_closed :
  fst (float_body_core 24 128 8388608 (-23) 12582912 (-22)) =
    SFdiv_core_binary 24 128 8388608 (-23) 12582912 (-22).
Proof.
  vm_compute; reflexivity.
Qed.

Example body_subnormal_rounding_closed :
  fst (float_body_round 24 128 BinarySingleNaN.mode_DN true 7 (-153) loc_Exact) =
    BinarySingleNaN.binary_round_aux 24 128 BinarySingleNaN.mode_DN true 7 (-153) loc_Exact.
Proof.
  vm_compute; reflexivity.
Qed.

Example body_malformed_zero_divisor_closed :
  fst (float_body_core 3 4 (-7) 0 0 0) = SFdiv_core_binary 3 4 (-7) 0 0 0.
Proof.
  vm_compute; reflexivity.
Qed.
