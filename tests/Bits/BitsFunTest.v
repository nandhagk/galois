(** * Word operation examples

    These computations cover division, shifts and population counts at boundaries.
    For example, division by zero yields the all-ones word.
    Builds on: BitsFun. *)

From Stdlib Require Import ZArith.
From Galois.Bits Require Import BitsWord BitsFun.

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

(** Width one retains both signed values and the count of the zero word. *)
Example width_one :
  wnot 1%positive 1 = 0 /\ wneg 1%positive 1 = 1 /\
  signed 1%positive 1 = -1 /\
  wclz 1%positive 0 = 1 /\ wctz 1%positive 1 = 0 /\ wpopcnt 1%positive 1 = 1.
Proof.
  vm_compute. repeat split.
Qed.

(** Population count distinguishes zero, negative wrapping and above-modulus values. *)
Example popcount_boundaries :
  wpopcnt 1%positive 0 = 0 /\ wpopcnt 1%positive 2 = 0 /\
  wpopcnt 8%positive (-1) = 8 /\ popcount (-1) = 0 /\ popcount 0 = 0 /\
  wpopcnt 64%positive (2 ^ 64) = 0.
Proof.
  vm_compute. repeat split.
Qed.

(** The digit traversal charges leading zeros no recursion steps. *)
Example popcount_recursion_steps :
  popcount_steps_pos 1%positive = 1%nat /\
  popcount_steps_pos 255%positive = 8%nat /\
  popcount_steps_pos 256%positive = 9%nat.
Proof.
  vm_compute. repeat split.
Qed.
