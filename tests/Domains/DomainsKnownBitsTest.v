(** * Known-bit word-harness regressions

    These fixtures retain the DOM-2 legacy precision policy through the shared harness.
    For example, singleton count operands intentionally retain the legacy count bound.
    Builds on: DomainsKnownBits and DomainsTagged. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTagged DomainsTnum DomainsTnumArith
  DomainsTnumShift DomainsTnumExpand DomainsTnumBack DomainsTnumMul DomainsKnownBitsForward
  DomainsKnownBitsBack DomainsKnownBits.
Import List.ListNotations.

Local Open Scope Z_scope.

Definition kb_forward := pforward known_bits_classic_domain.
Definition kb_assume := passume known_bits_classic_domain.

Example kb_forward_conflicting_masks :
  kb_forward bvadd [(8%positive, Tnum 1 1); (8%positive, tnum_const 8%positive 1)]
    8%positive = Tnum 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_shift_conflicting_amount :
  kb_forward bvshl [(8%positive, tnum_top); (8%positive, Tnum 1 1)]
    8%positive = Tnum 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_variable_logical_shift :
  kb_forward bvshl [(8%positive, tnum_const 8%positive 1); (8%positive, Tnum 252 0)]
    8%positive = Tnum 240 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_variable_oversized_shift :
  kb_forward bvlshr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 247 0)]
    8%positive = Tnum 127 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_variable_arithmetic_shift :
  kb_forward bvashr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 252 0)]
    8%positive = Tnum 15 128.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_variable_arithmetic_oversized :
  kb_forward bvashr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 247 0)]
    8%positive = Tnum 0 128.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_oversized_base :
  kb_forward bvshl [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 255)]
    8%positive = Tnum 255 0 /\
  kb_forward bvashr [(8%positive, Tnum 128 0); (8%positive, tnum_const 8%positive 255)]
    8%positive = Tnum 255 0.
Proof.
  vm_compute. auto.
Qed.

Example kb_wrapped_amount :
  kb_forward bvshl [(8%positive, Tnum 15 128); (8%positive, tnum_const 8%positive 256)]
    8%positive = Tnum 15 128.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_rotation_nonpower_width :
  kb_forward bvrotl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 15 0)]
    5%positive = Tnum 28 0 /\
  kb_forward bvrotr [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 15 0)]
    5%positive = Tnum 14 0.
Proof.
  vm_compute. auto.
Qed.

Example kb_rotation_width_one :
  kb_forward bvrotl [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
    1%positive = Tnum 0 1 /\
  kb_forward bvrotr [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
    1%positive = Tnum 0 1.
Proof.
  vm_compute. auto.
Qed.

Example kb_shift_width_one :
  kb_forward bvshl [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
    1%positive = Tnum 0 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_division_zero_boundary :
  kb_forward bvudiv [(8%positive, Tnum 240 0); (8%positive, tnum_const 8%positive 0)]
    8%positive = tnum_top /\
  kb_forward bvudiv [(8%positive, Tnum 240 0); (8%positive, Tnum 0 1)]
    8%positive = Tnum 240 0 /\
  kb_forward bvurem [(8%positive, Tnum 240 0); (8%positive, tnum_const 8%positive 0)]
    8%positive = Tnum 240 0.
Proof.
  vm_compute. auto.
Qed.

Example kb_signed_remainder_sign :
  kb_forward bvsrem [(8%positive, Tnum 128 0); (8%positive, tnum_top)]
    8%positive = Tnum 128 0 /\
  kb_forward bvsdiv [(8%positive, tnum_const 8%positive 7);
    (8%positive, tnum_const 8%positive 2)] 8%positive = tnum_top.
Proof.
  vm_compute. auto.
Qed.

Example kb_zero_counts :
  eval_op bvclz [(1%positive, 0)] = Some (1%positive, 1) /\
  eval_op bvctz [(1%positive, 0)] = Some (1%positive, 1) /\
  kb_forward bvclz [(5%positive, tnum_const 5%positive 0)]
    5%positive = Tnum 24 0 /\
  kb_forward bvpopcnt [(8%positive, tnum_top)] 8%positive = Tnum 240 0.
Proof.
  vm_compute. auto.
Qed.

Example kb_comparison_precision :
  kb_forward bvult [(8%positive, Tnum 128 0); (8%positive, tnum_const 8%positive 128)]
    1%positive = Tnum 0 1 /\
  kb_forward bvslt [(8%positive, Tnum 0 128); (8%positive, Tnum 128 0)]
    1%positive = Tnum 0 1 /\
  kb_forward bveq [(8%positive, Tnum 1 0); (8%positive, Tnum 0 1)]
    1%positive = Tnum 1 0.
Proof.
  vm_compute. auto.
Qed.

Example kb_conditional_precision :
  kb_forward bvite [(1%positive, tnum_const 1%positive 1); (8%positive, Tnum 15 128);
    (8%positive, tnum_top)] 8%positive = Tnum 15 128.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_width_change_precision :
  kb_forward (bvzext 4%positive) [(4%positive, Tnum 8 1)] 8%positive = Tnum 248 1 /\
  kb_forward (bvsext 4%positive) [(4%positive, Tnum 0 8)] 8%positive = Tnum 0 248 /\
  kb_forward (bvtrunc 4%positive) [(8%positive, Tnum 128 1)] 4%positive = Tnum 0 1 /\
  kb_forward (bvextract 5 2) [(8%positive, Tnum 24 4)] 4%positive = Tnum 6 1 /\
  kb_forward bvconcat [(3%positive, Tnum 2 4); (2%positive, Tnum 1 2)]
    5%positive = Tnum 9 18.
Proof.
  vm_compute. auto.
Qed.

Example kb_assume_add_constant :
  kb_assume bvadd [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 1)]
    8%positive (tnum_const 8%positive 7) = [Tnum 249 6; Tnum 254 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_assume_sign_fill :
  kb_assume bvashr [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 8)]
    8%positive (tnum_const 8%positive 255) = [Tnum 0 128; Tnum 247 8].
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_assume_unsigned_comparison :
  kb_assume bvult [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 8)]
    1%positive (tnum_const 1%positive 1) = [Tnum 248 0; Tnum 247 8].
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_assume_concat :
  kb_assume bvconcat [(3%positive, tnum_top); (2%positive, tnum_top)]
    5%positive (tnum_const 5%positive 21) = [Tnum 2 5; Tnum 2 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_malformed_width :
  forward (tagged_domain known_bits_classic_domain) bvadd
    [TVal 8%positive tnum_top; TVal 4%positive tnum_top] = TBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_assume_variable_shift :
  kb_assume bvshl [(8%positive, tnum_top); (8%positive, Tnum 254 0)]
    8%positive (tnum_const 8%positive 3) = [Tnum 124 1; Tnum 254 0] /\
  kb_assume bvashr [(8%positive, tnum_top); (8%positive, tnum_top)]
    8%positive (Tnum 0 128) = [Tnum 0 128; Tnum 0 0].
Proof.
  vm_compute. auto.
Qed.

Example kb_assume_variable_rotation :
  kb_assume bvrotl [(5%positive, tnum_top); (5%positive, Tnum 15 0)]
    5%positive (tnum_const 5%positive 1) = [Tnum 14 0; Tnum 15 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_assume_bitwise :
  kb_assume bvand [(8%positive, tnum_top); (8%positive, Tnum 0 2)]
    8%positive (Tnum 2 1) = [Tnum 2 1; Tnum 0 3] /\
  kb_assume bvor [(8%positive, tnum_top); (8%positive, Tnum 2 0)]
    8%positive (Tnum 1 2) = [Tnum 1 2; Tnum 3 0].
Proof.
  vm_compute. auto.
Qed.

Example kb_assume_width_changes :
  kb_assume (bvsext 4%positive) [(4%positive, tnum_top)]
    8%positive (Tnum 0 128) = [Tnum 0 8] /\
  kb_assume (bvextract 4 2) [(8%positive, tnum_top)]
    3%positive (tnum_const 3%positive 5) = [Tnum 8 20] /\
  kb_assume (bvtrunc 4%positive) [(8%positive, tnum_top)]
    4%positive (tnum_const 4%positive 3) = [Tnum 12 3].
Proof.
  vm_compute. auto.
Qed.

Example kb_assume_equality_and_subtraction :
  kb_assume bveq [(8%positive, Tnum 15 0); (8%positive, Tnum 0 128)]
    1%positive (tnum_const 1%positive 1) = [Tnum 15 128; Tnum 15 128] /\
  kb_assume bvsub [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 1)]
    8%positive (tnum_const 8%positive 7) = [Tnum 247 8; Tnum 254 1].
Proof.
  vm_compute. auto.
Qed.

Example kb_default_multiplier :
  pforward known_bits_domain bvmul
    [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)]
    8%positive = Tnum 251 0 /\
  kb_forward bvmul
    [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)]
    8%positive = Tnum 3 0.
Proof.
  vm_compute. auto.
Qed.

Example kb_variable_expansion_cost :
  Cost.ticks (tnum_variable_c bvshl 8%positive (tnum_const 8%positive 1) (Tnum 252 0)) =
    2%N /\
  Cost.ticks (tnum_back_variable_shift_c bvshl 8%positive (Tnum 252 0) (Tnum 0 1)) =
    4%N.
Proof.
  vm_compute. auto.
Qed.

Example kb_rotation_bridge_boundaries :
  wrotr 1%positive 1 255 = 1 /\
  wrotr 5%positive 1 16 = 16 /\
  wrotr 5%positive 33 0 = 1.
Proof.
  vm_compute. auto.
Qed.

Example kb_extract_bridge_boundaries :
  eval_op (bvextract 5 2) [(8%positive, 260)] = Some (4%positive, 1) /\
  eval_op (bvextract 5 2) [(8%positive, -1)] = Some (4%positive, 15) /\
  eval_op (bvextract 0 0) [(1%positive, -1)] = Some (1%positive, 1) /\
  eval_op (bvextract 8 0) [(8%positive, 1)] = None /\
  eval_op (bvextract 0 1) [(8%positive, 1)] = None.
Proof.
  vm_compute. auto.
Qed.

(** Extraction's arbitrary-integer client normalizes the source before division by the offset. *)
Example kb_extract_symbolic_client : forall w x,
  (6 <= Pos.to_nat w)%nat ->
  eval_op (bvextract 5 2) [(w, x)] =
    Some (4%positive, wrap 4%positive (wrap w x / 4)).
Proof.
  intros w x Hwidth. rewrite eval_op_extract.
  assert (Hslice : (2 <=? 5)%nat && (5 <? Pos.to_nat w)%nat = true).
  { apply andb_true_iff. split; [reflexivity|]. apply Nat.ltb_lt. lia. }
  rewrite Hslice. reflexivity.
Qed.

(** The right-rotation equation applies to arbitrary raw integers. *)
Example kb_rotr_symbolic_client : forall w x y,
  wrotr w x y = wrotl w x (Zpos w - wrap w y mod Zpos w).
Proof.
  apply wrotr_value.
Qed.

Example kb_rotr_negative_raw_inputs :
  wrotr 5%positive (-31) (-28) = 2 /\
  wrotr 1%positive (-1) (-1) = 1.
Proof.
  vm_compute. auto.
Qed.

Example kb_precise_preserves_invalid_width :
  pforward known_bits_precise_domain bvmul
    [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)] 4%positive =
  pforward known_bits_classic_domain bvmul
    [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)] 4%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_precise_preserves_invalid_arity :
  pforward known_bits_precise_domain bvmul [(8%positive, tnum_top)] 8%positive =
  pforward known_bits_classic_domain bvmul [(8%positive, tnum_top)] 8%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_nullary_legacy_choices :
  pforward known_bits_classic_domain bvadd [] 8%positive = tnum_top /\
  pforward known_bits_domain bvmul [] 4%positive = tnum_top.
Proof.
  vm_compute. auto.
Qed.

Example kb_nonempty_builder_charge_control :
  pforward_c (known_bits_word_domain known_bits_default_options) bvadd
    [(8%positive, Tnum 240 7); (8%positive, tnum_const 8%positive 1)] 8%positive =
  pforward_c (known_bits_word_builder known_bits_default_options) bvadd
    [(8%positive, Tnum 240 7); (8%positive, tnum_const 8%positive 1)] 8%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example kb_width_five_variable_cutoff_observations :
  kb_forward bvshl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 26 4)]
    5%positive = Tnum 15 0 /\
  kb_forward bvlshr [(5%positive, tnum_const 5%positive 16); (5%positive, Tnum 26 4)]
    5%positive = Tnum 30 0 /\
  kb_forward bvashr [(5%positive, tnum_const 5%positive 16); (5%positive, Tnum 23 0)]
    5%positive = Tnum 0 16 /\
  kb_forward bvrotl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 23 0)]
    5%positive = Tnum 22 0 /\
  kb_forward bvrotr [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 23 0)]
    5%positive = Tnum 26 0 /\
  kb_forward bvshl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 16 7)]
    5%positive = Tnum 31 0 /\
  kb_forward bvrotl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 16 7)]
    5%positive = Tnum 26 0.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition kb_test_contains (w : width) (a : tnum) (z : Z) : bool :=
  (Z.land z (wrap w (zeros a)) =? 0) &&
    (Z.land (wrap w (ones a)) (Z.lnot z) =? 0).

Definition kb_test_width_five_words : list Z := map Z.of_nat (seq 0 32).

(** Bounded enumeration checks counts around both the word width and the expansion cutoff. *)
Example kb_width_five_variable_cutoff_soundness :
  forallb (fun o => forallb (fun a => forallb (fun b =>
    forallb (fun x => forallb (fun k =>
      match eval_op o [(5%positive, x); (5%positive, k)] with
      | Some (_, z) => kb_test_contains 5%positive
          (kb_forward o [(5%positive, a); (5%positive, b)] 5%positive) z
      | None => false
      end) (filter (kb_test_contains 5%positive b) kb_test_width_five_words))
      (filter (kb_test_contains 5%positive a) kb_test_width_five_words))
    [Tnum 24 3; Tnum 26 4; Tnum 23 0; Tnum 16 7])
    [tnum_const 5%positive 1; tnum_const 5%positive 16; Tnum 16 0])
    [bvshl; bvlshr; bvashr; bvrotl; bvrotr] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition kb_test_malformed_inputs : list (width * tnum) :=
  [(5%positive, Tnum (-4) 33); (3%positive, Tnum (-2) 8); (1%positive, Tnum 3 3)].

Example kb_backward_malformed_arity_observations :
  kb_assume bvadd [] 5%positive tnum_top = [] /\
  kb_assume bvadd [(5%positive, Tnum (-4) 33)] 5%positive tnum_top = [Tnum 28 1] /\
  kb_assume bvadd kb_test_malformed_inputs 5%positive tnum_top =
    [Tnum 28 1; Tnum 6 0; Tnum 1 1].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example kb_refine_short_and_extra_result_observations :
  tnum_refine kb_test_malformed_inputs [] =
    [Tnum (-4) 33; Tnum (-2) 8; Tnum 3 3] /\
  tnum_refine kb_test_malformed_inputs [tnum_top] =
    [Tnum 28 1; Tnum (-2) 8; Tnum 3 3] /\
  tnum_refine kb_test_malformed_inputs [tnum_top; tnum_top; tnum_top; Tnum 31 31] =
    [Tnum 28 1; Tnum 6 0; Tnum 1 1] /\
  tnum_refine [] [Tnum 31 31] = [].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition kb_test_refines (xs : list (width * tnum)) (ys : list tnum) : bool :=
  Nat.eqb (length xs) (length ys) &&
    forallb (fun p => leb (tnum_lattice (fst (fst p))) (snd p) (snd (fst p))) (combine xs ys).

Example kb_malformed_backward_length_and_reductivity :
  forallb (fun xs => kb_test_refines xs (kb_assume bvadd xs 5%positive (Tnum 1 1)))
    [[]; [(5%positive, Tnum (-4) 33)]; kb_test_malformed_inputs] = true /\
  forallb (fun qs => kb_test_refines kb_test_malformed_inputs
    (tnum_refine kb_test_malformed_inputs qs))
    [[]; [tnum_top]; [tnum_top; tnum_top; tnum_top; Tnum 31 31]] = true.
Proof.
  vm_compute. auto.
Qed.
