(** * Arithmetic and testbit boundary examples

    Integer observations exercise total division, signed endpoints, counts and rotations.
    For example, signed remainder and signed modulus differ on operands of opposite signs.
    Builds on: Word, Fun, Testbit and Arith. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Fun Testbit Arith.
Import List.ListNotations.

Open Scope Z_scope.

(** Signed endpoints straddle the sign bit, including width one. *)
Example signed_endpoints :
  signed 8%positive 128 = -128 /\ signed 8%positive 127 = 127 /\
  signed 1%positive 1 = -1 /\ signed 1%positive 0 = 0.
Proof.
  vm_compute. repeat split.
Qed.

(** The overflowing signed quotient wraps to the minimum and its remainder is zero. *)
Example signed_minimum_division :
  wsdiv 8%positive 128 255 = 128 /\ wsrem 8%positive 128 255 = 0.
Proof.
  vm_compute. repeat split.
Qed.

(** Signed division, remainder and modulus discriminate every sign combination. *)
Example signed_division_signs :
  wsdiv 8%positive 249 3 = 254 /\ wsdiv 8%positive 7 253 = 254 /\
  wsdiv 8%positive 249 253 = 2 /\
  wsrem 8%positive 249 3 = 255 /\ wsrem 8%positive 7 253 = 1 /\
  wsrem 8%positive 249 253 = 255 /\
  wsmod 8%positive 249 3 = 2 /\ wsmod 8%positive 7 253 = 254 /\
  wsmod 8%positive 249 253 = 255.
Proof.
  vm_compute. repeat split.
Qed.

(** Both dividend signs and normalized zero divisors follow the total conventions. *)
Example zero_divisors :
  wudiv 8%positive 7 0 = 255 /\ wurem 8%positive 7 0 = 7 /\
  wsdiv 8%positive 7 0 = 255 /\ wsdiv 8%positive 249 0 = 1 /\
  wsrem 8%positive 249 0 = 249 /\ wsmod 8%positive 249 0 = 249 /\
  wudiv 8%positive 7 256 = 255 /\ wsmod 8%positive 249 256 = 249 /\
  wsmod 8%positive 250 3 = 0.
Proof.
  vm_compute. repeat split.
Qed.

(** Flipping the sign bit biases a signed comparison into an unsigned comparison. *)
Example sign_bit_bias :
  wslt 8%positive 255 1 = true /\
  wult 8%positive (wxor 8%positive 255 128) (wxor 8%positive 1 128) = true.
Proof.
  vm_compute. repeat split.
Qed.

(** Powers of two give matching multiplication, division, shift and mask results. *)
Example powers_of_two :
  wmul 8%positive 173 8 = 104 /\ wshl 8%positive 173 3 = 104 /\
  wudiv 8%positive 173 8 = 21 /\ wlshr 8%positive 173 3 = 21 /\
  wurem 8%positive 173 8 = 5 /\ wand 8%positive 173 7 = 5.
Proof.
  vm_compute. repeat split.
Qed.

(** Large shifts clear logical results and fill arithmetic results with the sign. *)
Example large_shifts :
  wshl 8%positive 129 8 = 0 /\ wlshr 8%positive 129 8 = 0 /\
  washr 8%positive 129 8 = 255 /\ washr 8%positive 127 255 = 0 /\
  washr 8%positive 129 1 = 192 /\ wshl 8%positive 129 256 = 129.
Proof.
  vm_compute. repeat split.
Qed.

(** Rotations use cyclic amounts and preserve overflow bits. *)
Example rotation_counts :
  wrotl 8%positive 129 0 = 129 /\ wrotl 8%positive 129 1 = 3 /\
  wrotl 8%positive 129 8 = 129 /\ wrotl 8%positive 129 17 = 3 /\
  wrotr 8%positive 3 17 = 129 /\ wrotr 8%positive 129 1 = 192 /\
  wrotl 3%positive 5 4 = 3 /\ wrotr 3%positive 5 4 = 6 /\
  wrotl 3%positive 5 2 = 6 /\ wrotr 3%positive 6 2 = 5.
Proof.
  vm_compute. repeat split.
Qed.

(** Zero distinguishes leading and trailing counts from population count. *)
Example zero_counts :
  wclz 8%positive 0 = 8 /\ wctz 8%positive 0 = 8 /\ wpopcnt 8%positive 0 = 0.
Proof.
  vm_compute. repeat split.
Qed.

(** Separated set bits and the sign bit distinguish the three count functions. *)
Example nonzero_counts :
  wclz 8%positive 24 = 3 /\ wctz 8%positive 24 = 3 /\ wpopcnt 8%positive 24 = 2 /\
  wpopcnt 8%positive (wnot 8%positive 24) = 6 /\ wctz 8%positive 128 = 7.
Proof.
  vm_compute. repeat split.
Qed.

(** Bitwise truth tables and testbit observations retain the width boundary. *)
Example bitwise_operators :
  wand 8%positive 170 204 = 136 /\ wor 8%positive 170 204 = 238 /\
  wxor 8%positive 170 204 = 102 /\ wnot 8%positive 170 = 85 /\
  Z.testbit (washr 8%positive 129 2) 7 = true /\
  Z.testbit (wshl 8%positive 129 2) 8 = false.
Proof.
  vm_compute. repeat split.
Qed.
