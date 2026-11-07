(** * Word operation examples

    These computations cover division, shifts and population counts at boundaries.
    For example, division by zero yields the all-ones word.
    Builds on: BitsFun. *)

From Stdlib Require Import ZArith.
From Galois.Bits Require Import BitsFun.

Open Scope Z_scope.

Example operation_boundaries :
  wudiv 8%positive 7 0 = 255 /\
  wsdiv 8%positive 249 0 = 1 /\
  wshl 8%positive 129 8 = 0 /\
  washr 8%positive 129 8 = 255 /\
  wpopcnt 1%positive 1 = 1 /\
  wpopcnt 8%positive 257 = 1 /\
  wpopcnt 64%positive (2 ^ 64 - 1) = 64.
Proof.
  vm_compute. repeat split.
Qed.
