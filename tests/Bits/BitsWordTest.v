(** * Word boundary examples

    Wrapping and signed interpretation cover values on either side of the modulus.
    For example, eight-bit wrapping maps negative one to 255.
    Builds on: BitsWord. *)

From Stdlib Require Import ZArith.
From Galois.Bits Require Import BitsWord.

Open Scope Z_scope.

Example word_boundaries :
  wrap 8%positive (-1) = 255 /\
  wrap 8%positive 256 = 0 /\
  signed 8%positive 128 = -128 /\
  signed 1%positive 1 = -1.
Proof.
  vm_compute. repeat split.
Qed.
