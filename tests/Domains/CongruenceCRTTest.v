(** * Exact CRT observations

    These fixtures compare the first-order CRT loop with the standard library.
    For example, signed inputs keep the same ordered Bezout coefficients.

    Groups:
    - [ExtgcdTests] The extended gcd agrees with the standard library.
    - [CombineTests] The CRT combination agrees with the standard library.
    - [MeetTests] Meet and narrow agree with a reference on congruence classes.
    - [DivisionTests] Aligned division agrees with Euclidean division.

    Builds on: Congruence and BitsLang. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Domains Require Import Congruence CongruenceSig BitsLang.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Payload := CongruenceCode WordLanguageCode.

(** Equality of two Bezout triples, component by component. *)
Definition triple_eqb (a b : Z * Z * Z) : bool :=
  let '(u, v, d) := a in
  let '(u', v', d') := b in
  (u =? u') && (v =? v') && (d =? d').

(** Signed integers that the reference examples cover. *)
Definition signed_samples : list Z := [-8; -3; -1; 0; 1; 2; 6; 9].

(** The meet of two congruence classes, computed from the standard gcd and lcm. *)
Definition reference_pmeet w a b :=
  match Payload.congr_norm w a, Payload.congr_norm w b with
  | CBot, _ | _, CBot => CBot
  | C m r, C n s =>
    if r mod Z.gcd m n =? s mod Z.gcd m n then
      Payload.congr_norm w (C (Z.lcm m n) (Z.combinecong m n r s))
    else CBot
  end.

(** Congruence classes that the meet examples cover, including bottom and negative moduli. *)
Definition payload_samples : list congr :=
  [CBot; C 0 0; C 0 3; C 0 (-1); C 0 300; C (-6) (-7); C 4 3; C 9 5].

(** Equality of two congruence classes, with bottom equal only to bottom. *)
Definition congr_eqb (a b : congr) : bool :=
  match a, b with
  | CBot, CBot => true
  | C m r, C n s => (m =? n) && (r =? s)
  | _, _ => false
  end.

(** Equality of two quotient and remainder pairs. *)
Definition div_pair_eqb (a b : Z * Z) : bool :=
  (fst a =? fst b) && (snd a =? snd b).

(** Two large coprime moduli, both above 2 ^ 43, for the checks on large inputs. *)
Definition large_modulus_a : Z := 17167680177565.
Definition large_modulus_b : Z := 27777890035288.

(** * Extended gcd *)

Module ExtgcdTests.

  (** The extended gcd matches the standard library on every signed sample pair. *)
  Example matches_standard_on_signed_samples :
    forallb (fun a => forallb (fun b =>
      triple_eqb (CongruenceCRT.extgcd a b) (Z.extgcd a b)) signed_samples)
      signed_samples = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The extended gcd matches the standard library on a pair of large inputs. *)
  Example matches_standard_on_large_inputs :
    CongruenceCRT.extgcd large_modulus_a large_modulus_b =
      Z.extgcd large_modulus_a large_modulus_b.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ExtgcdTests.

(** * Combination *)

Module CombineTests.

  (** The CRT combination matches the standard library on every signed sample. *)
  Example combinecong_matches_standard_on_signed_samples :
    forallb (fun m => forallb (fun n =>
      forallb (fun r => forallb (fun s =>
        CongruenceCRT.combinecong m n r s =? Z.combinecong m n r s)
        signed_samples) signed_samples) signed_samples) signed_samples = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CombineTests.

(** * Meet *)

Module MeetTests.

  (** The meet of two large classes equals the reference meet at width 46. *)
  Example pmeet_matches_reference_on_large_moduli :
    Payload.pmeet 46%positive (C large_modulus_a 0) (C large_modulus_b 0) =
      reference_pmeet 46%positive (C large_modulus_a 0) (C large_modulus_b 0).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The meet matches the reference on every sample pair at widths 1, 4 and 8. *)
  Example pmeet_matches_reference_on_samples :
    forallb (fun w => forallb (fun a => forallb (fun b =>
      congr_eqb (Payload.pmeet w a b) (reference_pmeet w a b))
      payload_samples) payload_samples) [1%positive; 4%positive; 8%positive] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The narrow matches the reference on every sample pair at widths 1, 4 and 8. *)
  Example pnarrow_matches_reference_on_samples :
    forallb (fun w => forallb (fun a => forallb (fun b =>
      congr_eqb (Payload.pnarrow w a b) (reference_pmeet w a b))
      payload_samples) payload_samples) [1%positive; 4%positive; 8%positive] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MeetTests.

(** * Aligned division *)

Module DivisionTests.

  (** Aligned division matches Euclidean division on every natural pair in the sample range. *)
  Example div_aligned_matches_div_eucl_on_natural_inputs :
    forallb (fun a => forallb (fun b =>
      div_pair_eqb (CongruenceCRT.div_aligned (Z.of_nat a) (Z.of_nat b))
        (Z.div_eucl (Z.of_nat a) (Z.of_nat b))) (seq 1 32)) (seq 0 128) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A dividend below the divisor gives quotient zero and the dividend as remainder. *)
  Example div_aligned_small_dividend_gives_zero_quotient :
    CongruenceCRT.div_aligned 1 (2 ^ 128) = (0, 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A dividend far above the divisor gives the Euclidean quotient and remainder. *)
  Example div_aligned_large_dividend_matches_div_eucl :
    CongruenceCRT.div_aligned (2 ^ 128 + 7) 3 = Z.div_eucl (2 ^ 128 + 7) 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative divisor gives the Euclidean quotient and remainder. *)
  Example div_aligned_negative_divisor_matches_div_eucl :
    CongruenceCRT.div_aligned 1 (-1) = Z.div_eucl 1 (-1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Aligned division matches Euclidean division on every signed sample pair, zero included. *)
  Example div_aligned_matches_div_eucl_on_signed_samples :
    forallb (fun a => forallb (fun b =>
      div_pair_eqb (CongruenceCRT.div_aligned a b) (Z.div_eucl a b))
      signed_samples) signed_samples = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End DivisionTests.
