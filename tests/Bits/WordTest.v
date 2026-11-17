(** * Word boundary examples

    Wrapping and signed interpretation cover values on either side of the modulus.
    For example, eight-bit wrapping maps negative one to 255.

    Groups:
    - [WrapTests] Wrapping of raw integers to one, eight and sixty-four bits.
    - [SignedTests] Signed interpretation of words at the sign-bit endpoints.
    - [ModulusTests] The modulus of a width, and its logarithm.
    - [SymbolicTests] General facts about wrapping and signed values, for any width.

    Builds on: Word. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word.
Import List.ListNotations.

Open Scope Z_scope.

(** * Wrap *)

Module WrapTests.

  (** Wrapping at width one, as (raw integer, result). Every result is the low bit. *)
  Definition width1_cases : list (Z * Z) :=
    [(0, 0); (-1, 1); (2 ^ 64, 0); (2 ^ 64 + 5, 1); (- (2 ^ 64) - 1, 1); (2 ^ 200 + 3, 1)].

  (** Wrapping at width eight, as (raw integer, result). Every result is the residue modulo 256. *)
  Definition width8_cases : list (Z * Z) :=
    [(0, 0); (-1, 255); (256, 0); (2 ^ 64, 0); (2 ^ 64 + 5, 5); (- (2 ^ 64) - 1, 255);
     (2 ^ 200 + 3, 3)].

  (** Wrapping at width sixty-four, as (raw integer, result). Every result is the residue
      modulo 2 ^ 64. *)
  Definition width64_cases : list (Z * Z) :=
    [(0, 0); (-1, 2 ^ 64 - 1); (2 ^ 64, 0); (2 ^ 64 + 5, 5); (- (2 ^ 64) - 1, 2 ^ 64 - 1);
     (2 ^ 200 + 3, 3)].

  (** Width one wraps every raw integer to its low bit. *)
  Example width1_wraps_to_low_bit :
    forallb (fun c => Z.eqb (wrap 1%positive (fst c)) (snd c)) width1_cases = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Width eight wraps every raw integer to its residue modulo 256. *)
  Example width8_wraps_modulo_256 :
    forallb (fun c => Z.eqb (wrap 8%positive (fst c)) (snd c)) width8_cases = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Width sixty-four wraps every raw integer to its residue modulo 2 ^ 64. *)
  Example width64_wraps_modulo_two_to_the_64 :
    forallb (fun c => Z.eqb (wrap 64%positive (fst c)) (snd c)) width64_cases = true.
  Proof. vm_compute. reflexivity. Qed.

End WrapTests.

(** * Signed *)

Module SignedTests.

  (** Zero is zero at width one. *)
  Example width1_zero_is_zero : signed 1%positive 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The width-one word one is negative one. *)
  Example width1_one_is_negative_one : signed 1%positive 1 = -1.
  Proof. vm_compute. reflexivity. Qed.

  (** Negative one is negative one at width one. *)
  Example width1_negative_one_is_negative_one : signed 1%positive (-1) = -1.
  Proof. vm_compute. reflexivity. Qed.

  (** Negative two wraps to zero at width one. *)
  Example width1_negative_two_is_zero : signed 1%positive (-2) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The largest positive eight-bit value is 127. *)
  Example width8_largest_positive : signed 8%positive 127 = 127.
  Proof. vm_compute. reflexivity. Qed.

  (** The eight-bit word 128 is the minimum, negative 128. *)
  Example width8_sign_bit_is_minimum : signed 8%positive 128 = -128.
  Proof. vm_compute. reflexivity. Qed.

  (** Negative 128 is also the minimum at width eight. *)
  Example width8_negative_minimum_is_minimum : signed 8%positive (-128) = -128.
  Proof. vm_compute. reflexivity. Qed.

  (** Negative 129 wraps around to 127 at width eight. *)
  Example width8_below_minimum_wraps_to_127 : signed 8%positive (-129) = 127.
  Proof. vm_compute. reflexivity. Qed.

  (** The largest positive sixty-four-bit value is two to the sixty-third minus one. *)
  Example width64_largest_positive : signed 64%positive (2 ^ 63 - 1) = 2 ^ 63 - 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The sixty-four-bit word two to the sixty-third is the minimum. *)
  Example width64_sign_bit_is_minimum : signed 64%positive (2 ^ 63) = - (2 ^ 63).
  Proof. vm_compute. reflexivity. Qed.

  (** Negative two to the sixty-third is the minimum at width sixty-four. *)
  Example width64_negative_minimum_is_minimum :
    signed 64%positive (- (2 ^ 63)) = - (2 ^ 63).
  Proof. vm_compute. reflexivity. Qed.

  (** A value below the minimum wraps to the largest positive value at width sixty-four. *)
  Example width64_below_minimum_wraps_to_largest :
    signed 64%positive (- (2 ^ 63) - 1) = 2 ^ 63 - 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero and the largest positive eight-bit value read as themselves. *)
  Example width8_zero_and_largest_positive :
    signed 8%positive 0 = 0 /\ signed 8%positive 127 = 127.
  Proof. vm_compute. repeat split. Qed.

  (** The sign-bit endpoints of width eight read as the minimum and negative one. *)
  Example width8_sign_bit_endpoints :
    signed 8%positive 128 = -128 /\ signed 8%positive 255 = -1.
  Proof. vm_compute. repeat split. Qed.

  (** Negative one reads as negative one at width eight. *)
  Example width8_negative_one_reads_as_negative_one : signed 8%positive (-1) = -1.
  Proof. vm_compute. reflexivity. Qed.

  (** Negative 129 wraps to 127 at width eight. *)
  Example width8_negative_129_wraps_to_127 : signed 8%positive (-129) = 127.
  Proof. vm_compute. reflexivity. Qed.

  (** Two hundred fifty-six wraps to zero at width eight. *)
  Example width8_signed_256_reads_zero : signed 8%positive 256 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Three hundred eighty-four wraps to the minimum at width eight. *)
  Example width8_384_wraps_to_minimum : signed 8%positive 384 = -128.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero reads as zero at width one. *)
  Example width1_zero_reads_zero : signed 1%positive 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The word one reads as negative one at width one. *)
  Example width1_one_reads_negative_one : signed 1%positive 1 = -1.
  Proof. vm_compute. reflexivity. Qed.

End SignedTests.

(** * Modulus *)

Module ModulusTests.

  (** The modulus of width one is two. *)
  Example width1_modulus_is_two : modulus 1%positive = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** The modulus of width eight is 256. *)
  Example width8_modulus_is_256 : modulus 8%positive = 256.
  Proof. vm_compute. reflexivity. Qed.

  (** The base-two logarithm of the width-one modulus is one. *)
  Example width1_modulus_log2_is_one : Z.log2 (modulus 1%positive) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The base-two logarithm of the width-eight modulus is eight. *)
  Example width8_modulus_log2_is_eight : Z.log2 (modulus 8%positive) = 8.
  Proof. vm_compute. reflexivity. Qed.

End ModulusTests.

(** * Symbolic *)

Module SymbolicTests.

  (** A nonnegative wrapped word reads as itself through the public signed equation. *)
  Example nonnegative_word_is_its_own_signed_value : forall w x,
    (wrap w x <? half w) = true -> signed w x = wrap w x.
  Proof.
    intros w x Hsign.
    rewrite signed_value, Hsign.
    reflexivity.
  Qed.

  (** The signed value is the remainder, shifted down by the modulus in the upper half. *)
  Example signed_value_is_remainder_shifted : forall w x,
    signed w x =
      if x mod modulus w <? half w
      then x mod modulus w else x mod modulus w - modulus w.
  Proof.
    intros w x.
    rewrite signed_value, wrap_mod.
    reflexivity.
  Qed.

  (** The base-two logarithm of the modulus of a width is that width. *)
  Example modulus_log2_is_width : forall w,
    Z.log2 (modulus w) = Zpos w.
  Proof.
    intro w. rewrite modulus_value.
    apply Z.log2_pow2. apply Z.lt_le_incl. apply Pos2Z.is_pos.
  Qed.

End SymbolicTests.
