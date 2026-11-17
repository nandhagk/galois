(** * Word boundary examples

    Wrapping and signed interpretation cover values on either side of the modulus.
    For example, eight-bit wrapping maps negative one to 255.
    Builds on: Word. *)

From Stdlib Require Import ZArith.
From Galois.Bits Require Import Word.

Open Scope Z_scope.

(** One-bit wrapping is parity even for negative and far-above-modulus inputs. *)
Example wrap_width1_values :
  wrap 1%positive 0 = 0 /\
  wrap 1%positive (-1) = 1 /\
  wrap 1%positive (2 ^ 64) = 0 /\
  wrap 1%positive (2 ^ 64 + 5) = 1 /\
  wrap 1%positive (- (2 ^ 64) - 1) = 1 /\
  wrap 1%positive (2 ^ 200 + 3) = 1.
Proof.
  vm_compute. repeat split.
Qed.

(** Eight-bit wrapping keeps the residue modulo 256 for every prescribed raw input. *)
Example wrap_width8_values :
  wrap 8%positive 0 = 0 /\
  wrap 8%positive (-1) = 255 /\
  wrap 8%positive (2 ^ 64) = 0 /\
  wrap 8%positive (2 ^ 64 + 5) = 5 /\
  wrap 8%positive (- (2 ^ 64) - 1) = 255 /\
  wrap 8%positive (2 ^ 200 + 3) = 3.
Proof.
  vm_compute. repeat split.
Qed.

(** Sixty-four-bit wrapping keeps low bits across the modulus and much larger magnitudes. *)
Example wrap_width64_values :
  wrap 64%positive 0 = 0 /\
  wrap 64%positive (-1) = 2 ^ 64 - 1 /\
  wrap 64%positive (2 ^ 64) = 0 /\
  wrap 64%positive (2 ^ 64 + 5) = 5 /\
  wrap 64%positive (- (2 ^ 64) - 1) = 2 ^ 64 - 1 /\
  wrap 64%positive (2 ^ 200 + 3) = 3.
Proof.
  vm_compute. repeat split.
Qed.

(** The one-bit signed endpoints are zero and negative one, with wrapping below the minimum. *)
Example signed_width1_endpoints :
  signed 1%positive 0 = 0 /\
  signed 1%positive 1 = -1 /\
  signed 1%positive (-1) = -1 /\
  signed 1%positive (-2) = 0.
Proof.
  vm_compute. repeat split.
Qed.

(** Eight-bit signed reading handles both encodings of the minimum and its predecessor. *)
Example signed_width8_endpoints :
  signed 8%positive 127 = 127 /\
  signed 8%positive 128 = -128 /\
  signed 8%positive (-128) = -128 /\
  signed 8%positive (-129) = 127.
Proof.
  vm_compute. repeat split.
Qed.

(** Sixty-four-bit signed reading crosses the sign bit and wraps below the signed minimum. *)
Example signed_width64_endpoints :
  signed 64%positive (2 ^ 63 - 1) = 2 ^ 63 - 1 /\
  signed 64%positive (2 ^ 63) = - (2 ^ 63) /\
  signed 64%positive (- (2 ^ 63)) = - (2 ^ 63) /\
  signed 64%positive (- (2 ^ 63) - 1) = 2 ^ 63 - 1.
Proof.
  vm_compute. repeat split.
Qed.

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

(** A symbolic client combines the signed and remainder equations without foreign unfolding. *)
Example signed_mod_symbolic_client : forall w x,
  signed w x =
    if x mod modulus w <? half w
    then x mod modulus w else x mod modulus w - modulus w.
Proof.
  intros w x.
  rewrite signed_value, wrap_mod.
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

(** The modulus and its logarithm cover width one and an eight-bit word. *)
Example modulus_value_boundaries :
  modulus 1%positive = 2 /\ modulus 8%positive = 256 /\
  Z.log2 (modulus 1%positive) = 1 /\ Z.log2 (modulus 8%positive) = 8.
Proof.
  vm_compute. repeat split.
Qed.

(** A symbolic rank client derives the modulus logarithm through the public numeric equation. *)
Example modulus_value_symbolic_client : forall w,
  Z.log2 (modulus w) = Zpos w.
Proof.
  intro w. rewrite modulus_value.
  apply Z.log2_pow2. apply Z.lt_le_incl. apply Pos2Z.is_pos.
Qed.
