(** * Word boundary examples

    Wrapping and signed interpretation cover values on either side of the modulus.
    For example, eight-bit wrapping maps negative one to 255.
    Builds on: BitsWord. *)

From Stdlib Require Import ZArith.
From Galois.Bits Require Import BitsWord.

Open Scope Z_scope.

(** Signed interpretation covers both sign-bit endpoints and malformed integers. *)
Example signed_value_boundaries :
  signed 8%positive 0 = 0 /\ signed 8%positive 127 = 127 /\
  signed 8%positive 128 = -128 /\ signed 8%positive 255 = -1 /\
  signed 8%positive (-1) = -1 /\ signed 8%positive (-129) = 127 /\
  signed 8%positive 256 = 0 /\ signed 8%positive 384 = -128 /\
  signed 1%positive 0 = 0 /\ signed 1%positive 1 = -1.
Proof.
  vm_compute. repeat split.
Qed.

(** A symbolic client selects the nonnegative signed branch through the public equation. *)
Example signed_value_symbolic_client : forall w x,
  (wrap w x <? half w) = true -> signed w x = wrap w x.
Proof.
  intros w x Hsign.
  rewrite signed_value, Hsign.
  reflexivity.
Qed.

Example word_boundaries :
  wrap 8%positive (-1) = 255 /\
  wrap 8%positive 256 = 0 /\
  signed 8%positive 128 = -128 /\
  signed 1%positive 1 = -1.
Proof.
  vm_compute. repeat split.
Qed.
