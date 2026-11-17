(** * Selectable known-bit multiplication fixtures

    Independent concrete enumeration checks the audit's two five-bit multiplier witnesses.
    For example, three times {6,7} has concrete results {18,21}.
    Builds on: DomainsTnumMul and public Bits arithmetic.

    Groups:
    - Fixtures: the short-stage masks and the concrete enumeration helpers.
    - Products: sparse, constant and conflicting products of the short-stage masks.
    - Contexts: the cached staged, accumulating and combined loops, at two widths.
    - Enumeration: the concrete products and the witnesses of the audit.
    - Edge cases: zero, conflicting, one-bit, odd-width and wrapped operands.
    - Legacy: the carry, normalization and low-bit rules of the staged loops.
    - Raw masks: equivalent raw masks, and the gamma and product controls on them.
    - Shared low: the default multiplier agrees with the public specification. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Fun.
From Galois.Domains Require Import KnownBitsSig KnownBits BitsLang.
Import List.ListNotations.

Local Open Scope Z_scope.

(** * Fixtures *)

(** The staged multiplier configuration used by the short-width masks. *)
Module ShortStages <: TNUM_CONFIG.
  Definition multiplier := MulStages.
End ShortStages.

(** The known-bit masks over the word language, with the staged multiplier. *)
Module ShortMasks := KnownBitsCode WordLanguageCode ShortStages.

(** Whether a concrete value x is a member of the mask a at width w. *)
Definition mul_test_contains (w : width) (a : tnum) (x : Z) : bool :=
  (Z.land x (wrap w (zeros a)) =? 0) &&
    (Z.land (wrap w (ones a)) (Z.lnot x) =? 0).

(** Every concrete word of width w, in increasing order. *)
Definition mul_test_words (w : width) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat (modulus w))).

(** The concrete products of every member of a with every member of b. *)
Definition mul_test_products (w : width) (a b : tnum) : list Z :=
  flat_map (fun x => map (wmul w x) (filter (mul_test_contains w b) (mul_test_words w)))
    (filter (mul_test_contains w a) (mul_test_words w)).

(** The minimum and the mask of a mask at width w, as the audit's witness pair. *)
Definition mul_test_pair (w : width) (a : tnum) : Z * Z :=
  (tnum_min w a, tnum_mask w a).

(** * Products *)

Module ProductTests.

  (** The default multiplier gives Tnum 7 8 for the sparse product. *)
  Example sparse_product_default :
    ShortMasks.tnum_mul 16%positive (Tnum 0 1) (Tnum 65527 8) = Tnum 7 8.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Both stages give Tnum 7 8 for the sparse product. *)
  Example sparse_product_both :
    ShortMasks.tnum_mul_with MulBoth 16%positive (Tnum 0 1) (Tnum 65527 8) = Tnum 7 8.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The default multiplier keeps the empty product Tnum 0 0 for an empty right operand. *)
  Example zero_product_default :
    ShortMasks.tnum_mul 16%positive (Tnum 0 1) (Tnum 0 0) = Tnum 0 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Both stages keep the empty product Tnum 0 0 for an empty right operand. *)
  Example zero_product_both :
    ShortMasks.tnum_mul_with MulBoth 16%positive (Tnum 0 1) (Tnum 0 0) = Tnum 0 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constant-zero right operand gives constant zero under the default multiplier. *)
  Example constant_zero_product_default :
    ShortMasks.tnum_mul 16%positive (Tnum 0 1) (Tnum 65535 0) = Tnum 65535 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Both stages give the fully unknown result for a Tnum 7 7 left operand. *)
  Example conflicting_product_both :
    ShortMasks.tnum_mul_with MulBoth 16%positive (Tnum 7 7) (Tnum 65527 8) =
      Tnum 65535 65535.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A known value of one keeps a raw multiplier unchanged under the default multiplier. *)
  Example known_one_keeps_multiplier :
    ShortMasks.tnum_mul 16%positive (tnum_const 16%positive 1) (Tnum 65527 8) =
      Tnum 65527 8.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A known value of one keeps an equivalent raw multiplier at the same constant product. *)
  Example known_one_keeps_equivalent_multiplier :
    ShortMasks.tnum_mul 16%positive (tnum_const 16%positive 1) (Tnum (-9) 8) =
      Tnum 65527 8.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ProductTests.

(** * Contexts *)

Module ContextTests.

  (** The staged loop at width eight gives 208 13 for the two-operand fixture. *)
  Example stages_width_8 :
    ShortMasks.tnum_mul_with MulStages 8%positive (Tnum 240 15) (Tnum 252 1) = Tnum 208 13.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The accumulating loop at width eight gives 192 1 for the same fixture. *)
  Example acc_width_8 :
    ShortMasks.tnum_mul_with MulAcc 8%positive (Tnum 240 15) (Tnum 252 1) = Tnum 192 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The combined loop at width eight gives the staged result. *)
  Example both_width_8 :
    ShortMasks.tnum_mul_with MulBoth 8%positive (Tnum 240 15) (Tnum 252 1) = Tnum 208 13.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The staged loop at width sixty-four gives the same result as at width eight. *)
  Example stages_width_64 :
    ShortMasks.tnum_mul_with MulStages 64%positive (Tnum 240 15) (Tnum 252 1) = Tnum 208 13.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The accumulating loop at width sixty-four gives the same result as at width eight. *)
  Example acc_width_64 :
    ShortMasks.tnum_mul_with MulAcc 64%positive (Tnum 240 15) (Tnum 252 1) = Tnum 192 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The combined loop at width sixty-four gives the staged result. *)
  Example both_width_64 :
    ShortMasks.tnum_mul_with MulBoth 64%positive (Tnum 240 15) (Tnum 252 1) = Tnum 208 13.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The staged loop gives the fully unknown result for a Tnum 128 128 left operand. *)
  Example stages_conflicting_left :
    ShortMasks.tnum_mul_with MulStages 8%positive (Tnum 128 128) (Tnum 252 1) =
      Tnum 255 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The accumulating loop gives the fully unknown result for a Tnum 1 1 right operand. *)
  Example acc_conflicting_right :
    ShortMasks.tnum_mul_with MulAcc 8%positive (Tnum 240 15) (Tnum 1 1) = Tnum 255 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The combined loop gives the fully unknown result for a Tnum 128 128 left operand. *)
  Example both_conflicting_left :
    ShortMasks.tnum_mul_with MulBoth 8%positive (Tnum 128 128) (Tnum 252 1) = Tnum 255 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ContextTests.

(** * Enumeration *)

Module EnumerationTests.

  (** The concrete products of three with the first fixture are 3 and 9. *)
  Example first_products :
    mul_test_products 5%positive (tnum_const 5%positive 3) (Tnum 28 1) = [3; 9].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The concrete products of three with the second fixture are 18 and 21. *)
  Example second_products :
    mul_test_products 5%positive (tnum_const 5%positive 3) (Tnum 24 6) = [18; 21].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The staged loop gives the first audit witness pair, one and ten. *)
  Example staged_first_witness :
    mul_test_pair 5%positive
      (tnum_mul_with MulStages 5%positive (tnum_const 5%positive 3) (Tnum 28 1)) = (1, 10).
  Proof.
    vm_compute. auto.
  Qed.

  (** The accumulating loop gives the first audit witness pair, one and fourteen. *)
  Example acc_first_witness :
    mul_test_pair 5%positive
      (tnum_mul_with MulAcc 5%positive (tnum_const 5%positive 3) (Tnum 28 1)) = (1, 14).
  Proof.
    vm_compute. auto.
  Qed.

  (** The staged loop gives the second audit witness pair, zero and thirty-one. *)
  Example staged_second_witness :
    mul_test_pair 5%positive
      (tnum_mul_with MulStages 5%positive (tnum_const 5%positive 3) (Tnum 24 6)) = (0, 31).
  Proof.
    vm_compute. auto.
  Qed.

  (** The accumulating loop gives the second audit witness pair, sixteen and seven. *)
  Example acc_second_witness :
    mul_test_pair 5%positive
      (tnum_mul_with MulAcc 5%positive (tnum_const 5%positive 3) (Tnum 24 6)) = (16, 7).
  Proof.
    vm_compute. auto.
  Qed.

  (** Every choice of multiplier contains every concrete product of the fixtures. *)
  Example witnesses_contain_products :
    forallb (fun b => forallb (fun choice =>
      forallb (mul_test_contains 5%positive
        (tnum_mul_with choice 5%positive (tnum_const 5%positive 3) b))
        (mul_test_products 5%positive (tnum_const 5%positive 3) b))
      [MulLow; MulStages; MulAcc; MulBoth]) [Tnum 28 1; Tnum 24 6] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The combined product is below both the staged and the accumulating product. *)
  Example both_refines_stages_and_acc :
    forallb (fun b =>
      let a := tnum_const 5%positive 3 in
      let both := tnum_mul_with MulBoth 5%positive a b in
      tnum_leb 5%positive both (tnum_mul_with MulStages 5%positive a b) &&
      tnum_leb 5%positive both (tnum_mul_with MulAcc 5%positive a b))
      [Tnum 28 1; Tnum 24 6] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EnumerationTests.

(** * Edge cases *)

Module EdgeTests.

  (** A known zero on the left gives the constant zero under the staged loop at width eight. *)
  Example zero_left_stages :
    tnum_mul_stages 8%positive (tnum_const 8%positive 0) tnum_top = Tnum 255 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The accumulating loop gives the constant zero for a known zero on the right. *)
  Example zero_right_acc :
    tnum_mul_acc 8%positive tnum_top (tnum_const 8%positive 0) = Tnum 255 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The combined loop gives the fully unknown result for an unknown high bit at width eight. *)
  Example conflict_both :
    tnum_mul_with MulBoth 8%positive tnum_top (Tnum 128 128) = Tnum 255 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** At width one, the constant one times top gives Tnum 0 0 under the staged loop. *)
  Example one_bit_stages :
    tnum_mul_stages 1%positive (tnum_const 1%positive 1) tnum_top = Tnum 0 0.
  Proof.
    vm_compute. auto.
  Qed.

  (** At width one, the constant one times top gives Tnum 0 0 under the accumulating loop. *)
  Example one_bit_acc :
    tnum_mul_acc 1%positive (tnum_const 1%positive 1) tnum_top = Tnum 0 0.
  Proof.
    vm_compute. auto.
  Qed.

  (** At width three, the constant five times Tnum 6 0 gives Tnum 2 0 under the staged loop. *)
  Example width_3_stages :
    tnum_mul_stages 3%positive (tnum_const 3%positive 5) (Tnum 6 0) = Tnum 2 0.
  Proof.
    vm_compute. auto.
  Qed.

  (** The accumulating loop gives Tnum 2 0 for the constant five times Tnum 6 0 at width three. *)
  Example width_3_acc :
    tnum_mul_acc 3%positive (tnum_const 3%positive 5) (Tnum 6 0) = Tnum 2 0.
  Proof.
    vm_compute. auto.
  Qed.

  (** Minus one times 258 at width eight gives Tnum 1 254 under the staged loop. *)
  Example wrapped_constants_stages :
    tnum_mul_stages 8%positive (tnum_const 8%positive (-1)) (tnum_const 8%positive 258) =
      Tnum 1 254.
  Proof.
    vm_compute. auto.
  Qed.

  (** Minus one times 258 at width eight gives Tnum 1 254 under the accumulating loop. *)
  Example wrapped_constants_acc :
    tnum_mul_acc 8%positive (tnum_const 8%positive (-1)) (tnum_const 8%positive 258) =
      Tnum 1 254.
  Proof.
    vm_compute. auto.
  Qed.

  (** Two unknown operands at width eight need eight stages. *)
  Example top_operands_need_eight_stages :
    tnum_mul_stage_count 8%positive tnum_top tnum_top = 8.
  Proof.
    vm_compute. auto.
  Qed.

  (** A left operand of Tnum 1 1 needs no stages. *)
  Example known_left_operand_needs_no_stages :
    tnum_mul_stage_count 8%positive (Tnum 1 1) tnum_top = 0.
  Proof.
    vm_compute. auto.
  Qed.

End EdgeTests.

(** * Legacy *)

Module LegacyTests.

  (** Three times Tnum 252 1 gives Tnum 244 1 under the staged loop. *)
  Example three_times_unknown_low_bits :
    tnum_mul_stages 8%positive (tnum_const 8%positive 3) (Tnum 252 1) = Tnum 244 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Seven times Tnum 252 1 gives Tnum 232 5 under the staged loop. *)
  Example seven_times_unknown_low_bits :
    tnum_mul_stages 8%positive (tnum_const 8%positive 7) (Tnum 252 1) = Tnum 232 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Tnum 252 1 times two gives Tnum 249 2 under the staged loop. *)
  Example unknown_times_two :
    tnum_mul_stages 8%positive (Tnum 252 1) (tnum_const 8%positive 2) = Tnum 249 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The constant 128 times Tnum 252 1 gives Tnum 127 128 under the staged loop. *)
  Example high_bit_constant_times_unknown :
    tnum_mul_stages 8%positive (tnum_const 8%positive 128) (Tnum 252 1) = Tnum 127 128.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two hundred times three gives Tnum 167 88 under the staged loop. *)
  Example constants_200_times_3 :
    tnum_mul_stages 8%positive (tnum_const 8%positive 200) (tnum_const 8%positive 3) =
      Tnum 167 88.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constant four times a mask above the width normalizes the mask to 251 0. *)
  Example mask_above_width_normalized :
    tnum_mul_stages 8%positive (tnum_const 8%positive 4) (Tnum (-2) 256) = Tnum 251 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Tnum 256 256 times zero gives the constant zero at width eight. *)
  Example value_above_width_normalized :
    tnum_mul_stages 8%positive (Tnum 256 256) (tnum_const 8%positive 0) = Tnum 255 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An unknown low bit times zero gives the fully unknown result. *)
  Example unknown_low_bit_times_zero :
    tnum_mul_stages 8%positive (Tnum 1 1) (tnum_const 8%positive 0) = Tnum 255 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The default product of the constants three and seven gives Tnum 234 21. *)
  Example constant_product_low_rule :
    tnum_mul 8%positive (tnum_const 8%positive 3) (tnum_const 8%positive 7) = Tnum 234 21.
  Proof.
    vm_compute. auto.
  Qed.

  (** The default product of Tnum 3 0 and Tnum 1 0 gives Tnum 7 0. *)
  Example known_low_bits_rule :
    tnum_mul 8%positive (Tnum 3 0) (Tnum 1 0) = Tnum 7 0.
  Proof.
    vm_compute. auto.
  Qed.

  (** Top times zero gives the constant zero under the staged loop. *)
  Example top_times_zero_stages :
    tnum_mul_stages 8%positive tnum_top (tnum_const 8%positive 0) = Tnum 255 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Top times an unknown high bit gives the fully unknown result under the staged loop. *)
  Example top_times_unknown_high_bit_stages :
    tnum_mul_stages 8%positive tnum_top (Tnum 128 128) = Tnum 255 255.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The default product of four and a mask of 254 is 3 0. *)
  Example four_times_254_default :
    tnum_mul 8%positive (tnum_const 8%positive 4) (Tnum 254 0) = Tnum 3 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The staged product of four and a mask of 254 normalizes to 251 0. *)
  Example four_times_254_stages :
    tnum_mul_stages 8%positive (tnum_const 8%positive 4) (Tnum 254 0) = Tnum 251 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The order check accepts 251 0 below 3 0. *)
  Example order_251_below_3 :
    tnum_leb 8%positive (Tnum 251 0) (Tnum 3 0) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The order check rejects 3 0 below 251 0. *)
  Example order_3_not_below_251 :
    tnum_leb 8%positive (Tnum 3 0) (Tnum 251 0) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LegacyTests.

(** * Raw masks *)

Module RawMaskTests.

  (** The raw masks of each equivalent pair describe the same set of concrete words. *)
  Definition raw_equivalents : list (tnum * tnum) :=
    [(Tnum (-4) 35, Tnum 28 3); (Tnum (-4) 33, Tnum 28 1);
     (Tnum (-8) 38, Tnum 24 6); (Tnum 32 32, tnum_top); (Tnum (-31) 33, Tnum 1 1)].

  (** The accumulating loop gives 16 1 for the first raw mask pair. *)
  Example acc_first_raw_pair :
    tnum_mul_acc 5%positive (Tnum (-4) 35) (Tnum (-4) 33) = Tnum 16 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The accumulating loop gives 8 16 for the second raw mask pair. *)
  Example acc_second_raw_pair :
    tnum_mul_acc 5%positive (Tnum (-4) 35) (Tnum (-8) 38) = Tnum 8 16.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The accumulating loop gives Tnum 31 31 for Tnum (-31) 33 times zero. *)
  Example acc_conflicting_left_zero_right :
    tnum_mul_acc 5%positive (Tnum (-31) 33) (tnum_const 5%positive 0) = Tnum 31 31.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The accumulating loop gives Tnum 31 31 for zero times Tnum (-31) 33. *)
  Example acc_zero_left_conflicting_right :
    tnum_mul_acc 5%positive (tnum_const 5%positive 0) (Tnum (-31) 33) = Tnum 31 31.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Equivalent raw masks have the same members at width five. *)
  Example raw_equivalents_same_members :
    forallb (fun p => forallb (fun z =>
      Bool.eqb (mul_test_contains 5%positive (fst p) z)
        (mul_test_contains 5%positive (snd p) z)) (mul_test_words 5%positive))
      raw_equivalents = true.
  Proof.
    vm_compute. auto.
  Qed.

  (** The mask Tnum (-31) 33 has no members at width five. *)
  Example mask_without_members_at_width_five :
    filter (mul_test_contains 5%positive (Tnum (-31) 33)) (mul_test_words 5%positive) = [].
  Proof.
    vm_compute. auto.
  Qed.

  (** All choices keep equivalent raw masks at the same members, including conflicting masks. *)
  Example all_choices_keep_raw_members :
    forallb (fun p => forallb (fun q => forallb (fun choice => forallb (fun z =>
      Bool.eqb (mul_test_contains 5%positive
        (tnum_mul_with choice 5%positive (fst p) (fst q)) z)
        (mul_test_contains 5%positive
          (tnum_mul_with choice 5%positive (snd p) (snd q)) z))
      (mul_test_words 5%positive)) [MulLow; MulStages; MulAcc; MulBoth])
      raw_equivalents) raw_equivalents = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Concrete products are members of every choice's result on the raw fixtures. *)
  Example all_choices_contain_raw_products :
    forallb (fun p => forallb (fun q => forallb (fun choice =>
      forallb (mul_test_contains 5%positive
        (tnum_mul_with choice 5%positive (fst p) (fst q)))
        (mul_test_products 5%positive (fst p) (fst q))) [MulLow; MulStages; MulAcc; MulBoth])
      raw_equivalents) raw_equivalents = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RawMaskTests.

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

(** * Shared low *)

Module SharedLowTests.

  (** The default multiplier, as a module over the word language. *)
  Module SharedLowConfig <: TNUM_CONFIG.
    Definition multiplier := MulLow.
  End SharedLowConfig.

  (** The known-bit masks with the default multiplier. *)
  Module SharedLow := KnownBitsCode WordLanguageCode SharedLowConfig.

  (** Operand pairs at widths one, eight and sixty-four that the default multiplier must share. *)
  Definition shared_low_fixtures : list (positive * tnum * tnum) :=
    [(1%positive, Tnum 0 1, Tnum 0 1);
     (8%positive, Tnum 240 0, Tnum 248 0);
     (8%positive, Tnum 240 15, Tnum 252 1);
     (8%positive, Tnum 0 0, Tnum 0 0);
     (8%positive, Tnum 7 7, Tnum 0 0);
     (8%positive, Tnum (-16) 257, Tnum 65280 255);
     (64%positive, Tnum 240 0, Tnum 248 0)].

  (** The default multiplier keeps exact constants and shared trailing-zero facts. *)
  Example default_matches_public_specification :
    Forall (fun '(w, a, b) =>
      SharedLow.tnum_mul w a b = tnum_mul w a b /\
      SharedLow.tnum_mul_with MulLow w a b = tnum_mul w a b)
      shared_low_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; split; reflexivity|]).
    apply Forall_nil.
  Qed.

End SharedLowTests.
