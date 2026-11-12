(** * Selectable known-bit multiplication fixtures

    Independent concrete enumeration checks the audit's two five-bit multiplier witnesses.
    For example, three times {6,7} has concrete results {18,21}.
    Builds on: DomainsTnumMul and public Bits arithmetic. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Fun.
From Galois.Domains Require Import KnownBitsSig KnownBits.
Import List.ListNotations.

Local Open Scope Z_scope.

Definition mul_test_contains (w : width) (a : tnum) (x : Z) : bool :=
  (Z.land x (wrap w (zeros a)) =? 0) &&
    (Z.land (wrap w (ones a)) (Z.lnot x) =? 0).

Definition mul_test_words (w : width) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat (modulus w))).

Definition mul_test_products (w : width) (a b : tnum) : list Z :=
  flat_map (fun x => map (wmul w x) (filter (mul_test_contains w b) (mul_test_words w)))
    (filter (mul_test_contains w a) (mul_test_words w)).

Definition mul_test_pair (w : width) (a : tnum) : Z * Z :=
  (tnum_min w a, tnum_mask w a).

Example multiplier_first_enumeration :
  mul_test_products 5%positive (tnum_const 5%positive 3) (Tnum 28 1) = [3; 9].
Proof.
  vm_compute. reflexivity.
Qed.

Example multiplier_second_enumeration :
  mul_test_products 5%positive (tnum_const 5%positive 3) (Tnum 24 6) = [18; 21].
Proof.
  vm_compute. reflexivity.
Qed.

Example multiplier_first_witness :
  mul_test_pair 5%positive
    (tnum_mul_with MulStages 5%positive (tnum_const 5%positive 3) (Tnum 28 1)) = (1, 10) /\
  mul_test_pair 5%positive
    (tnum_mul_with MulAcc 5%positive (tnum_const 5%positive 3) (Tnum 28 1)) = (1, 14).
Proof.
  vm_compute. auto.
Qed.

Example multiplier_second_witness :
  mul_test_pair 5%positive
    (tnum_mul_with MulStages 5%positive (tnum_const 5%positive 3) (Tnum 24 6)) = (0, 31) /\
  mul_test_pair 5%positive
    (tnum_mul_with MulAcc 5%positive (tnum_const 5%positive 3) (Tnum 24 6)) = (16, 7).
Proof.
  vm_compute. auto.
Qed.

Example multiplier_witnesses_contain_concrete_products :
  forallb (fun b => forallb (fun choice =>
    forallb (mul_test_contains 5%positive
      (tnum_mul_with choice 5%positive (tnum_const 5%positive 3) b))
      (mul_test_products 5%positive (tnum_const 5%positive 3) b))
    [MulLow; MulStages; MulAcc; MulBoth]) [Tnum 28 1; Tnum 24 6] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example multiplier_meet_refines_both :
  forallb (fun b =>
    let a := tnum_const 5%positive 3 in
    let both := tnum_mul_with MulBoth 5%positive a b in
    tnum_leb 5%positive both (tnum_mul_with MulStages 5%positive a b) &&
    tnum_leb 5%positive both (tnum_mul_with MulAcc 5%positive a b))
    [Tnum 28 1; Tnum 24 6] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example multiplier_zero_left :
  tnum_mul_stages 8%positive (tnum_const 8%positive 0) tnum_top = Tnum 255 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example multiplier_zero_right :
  tnum_mul_acc 8%positive tnum_top (tnum_const 8%positive 0) = Tnum 255 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example multiplier_conflict :
  tnum_mul_with MulBoth 8%positive tnum_top (Tnum 128 128) = Tnum 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example multiplier_one_bit :
  tnum_mul_stages 1%positive (tnum_const 1%positive 1) tnum_top = Tnum 0 0 /\
  tnum_mul_acc 1%positive (tnum_const 1%positive 1) tnum_top = Tnum 0 0.
Proof.
  vm_compute. auto.
Qed.

Example multiplier_non_power_width :
  tnum_mul_stages 3%positive (tnum_const 3%positive 5) (Tnum 6 0) = Tnum 2 0 /\
  tnum_mul_acc 3%positive (tnum_const 3%positive 5) (Tnum 6 0) = Tnum 2 0.
Proof.
  vm_compute. auto.
Qed.

Example multiplier_wrapped_constants :
  tnum_mul_stages 8%positive (tnum_const 8%positive (-1)) (tnum_const 8%positive 258) =
    Tnum 1 254 /\
  tnum_mul_acc 8%positive (tnum_const 8%positive (-1)) (tnum_const 8%positive 258) =
    Tnum 1 254.
Proof.
  vm_compute. auto.
Qed.

Example multiplier_stage_count :
  tnum_mul_stage_count 8%positive tnum_top tnum_top = 8 /\
  tnum_mul_stage_count 8%positive (Tnum 1 1) tnum_top = 0.
Proof.
  vm_compute. auto.
Qed.


Example multiplier_legacy_stages_carry_and_known_bits :
  tnum_mul_stages 8%positive (tnum_const 8%positive 3) (Tnum 252 1) = Tnum 244 1 /\
  tnum_mul_stages 8%positive (tnum_const 8%positive 7) (Tnum 252 1) = Tnum 232 5 /\
  tnum_mul_stages 8%positive (Tnum 252 1) (tnum_const 8%positive 2) = Tnum 249 2 /\
  tnum_mul_stages 8%positive (tnum_const 8%positive 128) (Tnum 252 1) = Tnum 127 128 /\
  tnum_mul_stages 8%positive (tnum_const 8%positive 200) (tnum_const 8%positive 3) =
    Tnum 167 88.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example multiplier_legacy_normalized_masks :
  tnum_mul_stages 8%positive (tnum_const 8%positive 4) (Tnum (-2) 256) = Tnum 251 0 /\
  tnum_mul_stages 8%positive (Tnum 256 256) (tnum_const 8%positive 0) = Tnum 255 0 /\
  tnum_mul_stages 8%positive (Tnum 1 1) (tnum_const 8%positive 0) = Tnum 255 255.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example multiplier_legacy_low_rules :
  tnum_mul 8%positive (tnum_const 8%positive 3) (tnum_const 8%positive 7) = Tnum 234 21 /\
  tnum_mul 8%positive (Tnum 3 0) (Tnum 1 0) = Tnum 7 0.
Proof.
  vm_compute. auto.
Qed.

Example multiplier_legacy_remaining_stages :
  tnum_mul_stages 8%positive tnum_top (tnum_const 8%positive 0) = Tnum 255 0 /\
  tnum_mul_stages 8%positive tnum_top (Tnum 128 128) = Tnum 255 255 /\
  tnum_mul 8%positive (tnum_const 8%positive 4) (Tnum 254 0) = Tnum 3 0 /\
  tnum_mul_stages 8%positive (tnum_const 8%positive 4) (Tnum 254 0) = Tnum 251 0 /\
  tnum_leb 8%positive (Tnum 251 0) (Tnum 3 0) = true /\
  tnum_leb 8%positive (Tnum 3 0) (Tnum 251 0) = false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.


Example multiplier_acc_raw_mask_observations :
  tnum_mul_acc 5%positive (Tnum (-4) 35) (Tnum (-4) 33) = Tnum 16 1 /\
  tnum_mul_acc 5%positive (Tnum (-4) 35) (Tnum (-8) 38) = Tnum 8 16 /\
  tnum_mul_acc 5%positive (Tnum (-31) 33) (tnum_const 5%positive 0) = Tnum 31 31 /\
  tnum_mul_acc 5%positive (tnum_const 5%positive 0) (Tnum (-31) 33) = Tnum 31 31.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition mul_test_raw_equivalents : list (tnum * tnum) :=
  [(Tnum (-4) 35, Tnum 28 3); (Tnum (-4) 33, Tnum 28 1);
   (Tnum (-8) 38, Tnum 24 6); (Tnum 32 32, tnum_top); (Tnum (-31) 33, Tnum 1 1)].

Example multiplier_raw_gamma_equivalence_controls :
  forallb (fun p => forallb (fun z =>
    Bool.eqb (mul_test_contains 5%positive (fst p) z)
      (mul_test_contains 5%positive (snd p) z)) (mul_test_words 5%positive))
    mul_test_raw_equivalents = true /\
  filter (mul_test_contains 5%positive (Tnum (-31) 33)) (mul_test_words 5%positive) = [].
Proof.
  vm_compute. auto.
Qed.

(** All choices preserve gamma under equivalent raw masks, including conflicting masks. *)
Example multiplier_all_choice_raw_gamma_controls :
  forallb (fun p => forallb (fun q => forallb (fun choice => forallb (fun z =>
    Bool.eqb (mul_test_contains 5%positive
      (tnum_mul_with choice 5%positive (fst p) (fst q)) z)
      (mul_test_contains 5%positive
        (tnum_mul_with choice 5%positive (snd p) (snd q)) z))
    (mul_test_words 5%positive)) [MulLow; MulStages; MulAcc; MulBoth])
    mul_test_raw_equivalents) mul_test_raw_equivalents = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Concrete products independently check soundness for every choice on the raw fixtures. *)
Example multiplier_all_choice_raw_product_controls :
  forallb (fun p => forallb (fun q => forallb (fun choice =>
    forallb (mul_test_contains 5%positive
      (tnum_mul_with choice 5%positive (fst p) (fst q)))
      (mul_test_products 5%positive (fst p) (fst q))) [MulLow; MulStages; MulAcc; MulBoth])
    mul_test_raw_equivalents) mul_test_raw_equivalents = true.
Proof.
  vm_compute. reflexivity.
Qed.

(* The charged Cost interface was removed. These source clock observations are deferred
   to the later timing work and are not executable tests of generated clocks.
Example multiplier_early_stop_cost :
  Cost.ticks (tnum_mul_acc_c 8%positive tnum_top (tnum_const 8%positive 0)) = 5%N.
Proof. vm_compute. reflexivity. Qed.

Example multiplier_cost_bound_clients :
  (Cost.ticks (tnum_mul_with_c MulBoth 8%positive tnum_top tnum_top) <= 48)%N /\
  (Cost.ticks (tnum_mul_stages_c 8%positive tnum_top tnum_top) <= 24)%N.
Proof. vm_compute. intuition discriminate. Qed.
*)
