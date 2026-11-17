(** * Known-bit harness observations

    Known-bit transfers run through the shared tagged word harness.
    For example, a variable shift joins the possible bit positions.
    Builds on: KnownBitsBack, Tagged and Harness.

    Groups:
    - Fixtures: the low and staged multiplier modules, the harness and the forward helpers.
    - Forward: forward transfers of operations, with their widths and conflicts.
    - Assume: backward transfers that narrow the operands of each operation.
    - Singletons: singleton operands and counts that the shared harness evaluates exactly.
    - Malformed: operand lists of the wrong arity, and the harness's answer for them.
    - Bridges: rotation, extraction and refinement at the boundaries of the word operations.
    - Multiplier: the default multiplier against the low multiplier on the same inputs.
    - Payload: the direct payload computations of the low and staged modules.
    - Symbolic: the extraction and rotation facts for every width and value.
    - Tables: the public table of the harness on shifted concatenation. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Bits Require Import Word Op Fun.
From Galois.Domains Require Import BitsLang WordSig KnownBitsSig KnownBits KnownBitsOps
  KnownBitsBack Tagged Harness.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

(** The low multiplier configuration. *)
Module Low <: TNUM_CONFIG.
  Definition multiplier := MulLow.
End Low.

(** The known-bit masks over the word language, with the low multiplier. *)
Module W := KnownBitsCode WordLanguageCode Low.
(** The known-bit table over the masks, with the low multiplier. *)
Module T := KnownBitsTableCode WordLanguageCode Low W.
(** The tagged known-bit module over the masks. *)
Module B := TaggedCode WordLanguageCode W.
(** The tagged table over the tagged module. *)
Module TT := TaggedTableCode WordLanguageCode W T.
(** The harness that runs the operations over the tagged table. *)
Module D := HarnessCode BitsLangCode B TT.

(** Tags a mask with its width-carrying position. *)
Definition tag (p : positive * tnum) := TVal (fst p) (snd p).

(** Removes the tag, mapping bottom to the empty mask and the unknown tag to top. *)
Definition untag (p : tagged tnum) : tnum :=
  match p with TBot => tnum_bot 1%positive | TAny => tnum_top | TVal _ a => a end.

(** The forward mask of an operation over operand masks, at the result width rw. *)
Definition kb_forward (o : op) (xs : list (positive * tnum)) (rw : positive) : tnum :=
  match D.forward (BOp o) (map tag xs) with
  | TBot => tnum_bot rw | TAny => tnum_top | TVal _ a => a
  end.

(** The backward masks of the operands for an operation with result width rw and mask q. *)
Definition kb_assume (o : op) (xs : list (positive * tnum)) (rw : positive) (q : tnum)
    : list tnum := map untag (D.backward (BOp o) (TVal rw q) (map tag xs)).

(** Whether a concrete value z is a member of the mask a at width w. *)
Definition kb_test_contains (w : width) (a : tnum) (z : Z) : bool :=
  (Z.land z (wrap w (zeros a)) =? 0) && (Z.land (wrap w (ones a)) (Z.lnot z) =? 0).

(** Every concrete word of width five. *)
Definition kb_test_width_five_words : list Z := map Z.of_nat (seq 0 32).

(** Operand lists of widths five, three and one, with masks of the wrong size. *)
Definition kb_test_malformed_inputs : list (width * tnum) :=
  [(5%positive, Tnum (-4) 33); (3%positive, Tnum (-2) 8); (1%positive, Tnum 3 3)].

(** Whether the refined masks have the lengths of the inputs and refine each of them. *)
Definition kb_test_refines (xs : list (width * tnum)) (ys : list tnum) : bool :=
  Nat.eqb (length xs) (length ys) &&
    forallb (fun p => tnum_leb (fst (fst p)) (snd p) (snd (fst p))) (combine xs ys).

(** The staged multiplier configuration. *)
Module Stages <: TNUM_CONFIG.
  Definition multiplier := MulStages.
End Stages.
(** The known-bit masks over the word language, with the staged multiplier. *)
Module StagesMasks := KnownBitsCode WordLanguageCode Stages.
(** The fast operations over the staged masks. *)
Module StagesOps := KnownBitsOpsFastCode WordLanguageCode Stages StagesMasks.
(** The fast operations over the low-multiplier masks. *)
Module LowOps := KnownBitsOpsFastCode WordLanguageCode Low W.

(** * Forward *)

Module ForwardTests.

  (** Adding a conflicting mask to a constant gives top at width eight. *)
  Example conflicting_masks_add :
    kb_forward bvadd [(8%positive, Tnum 1 1); (8%positive, tnum_const 8%positive 1)]
      8%positive = Tnum 255 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift by a conflicting amount gives top at width eight. *)
  Example shift_conflicting_amount :
    kb_forward bvshl [(8%positive, tnum_top); (8%positive, Tnum 1 1)]
      8%positive = Tnum 255 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift of the constant one by the mask 252 0 gives the mask 240 0. *)
  Example variable_logical_shift :
    kb_forward bvshl [(8%positive, tnum_const 8%positive 1); (8%positive, Tnum 252 0)]
      8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical right shift of 128 by the mask 247 0 gives the mask 127 0. *)
  Example variable_oversized_shift :
    kb_forward bvlshr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 247 0)]
      8%positive = Tnum 127 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift of 128 by the mask 252 0 keeps the sign bit. *)
  Example variable_arithmetic_shift :
    kb_forward bvashr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 252 0)]
      8%positive = Tnum 15 128.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift of 128 by the mask 247 0 gives the mask 0 128. *)
  Example variable_arithmetic_oversized :
    kb_forward bvashr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 247 0)]
      8%positive = Tnum 0 128.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift of top by the constant 255 gives the mask 255 0 at width eight. *)
  Example oversized_base_left :
    kb_forward bvshl [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 255)]
      8%positive = Tnum 255 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift of the mask 128 0 by the constant 255 gives the mask 255 0. *)
  Example oversized_base_arithmetic :
    kb_forward bvashr [(8%positive, Tnum 128 0); (8%positive, tnum_const 8%positive 255)]
      8%positive = Tnum 255 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift by the constant 256 wraps to a shift by zero at width eight. *)
  Example wrapped_amount :
    kb_forward bvshl [(8%positive, Tnum 15 128); (8%positive, tnum_const 8%positive 256)]
      8%positive = Tnum 15 128.
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation of the constant one by the mask 15 0 at width five gives 28 0. *)
  Example rotation_nonpower_left :
    kb_forward bvrotl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 15 0)]
      5%positive = Tnum 28 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation of the constant one by the mask 15 0 at width five gives 14 0. *)
  Example rotation_nonpower_right :
    kb_forward bvrotr [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 15 0)]
      5%positive = Tnum 14 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation at width one of the constant one gives the mask 0 1. *)
  Example rotation_width_one_left :
    kb_forward bvrotl [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
      1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation at width one of the constant one gives the mask 0 1. *)
  Example rotation_width_one_right :
    kb_forward bvrotr [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
      1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift at width one of the constant one gives the empty mask. *)
  Example shift_width_one :
    kb_forward bvshl [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
      1%positive = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned division of the mask 240 0 by the constant zero gives top. *)
  Example udiv_by_zero_is_top :
    kb_forward bvudiv [(8%positive, Tnum 240 0); (8%positive, tnum_const 8%positive 0)]
      8%positive = tnum_top.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned division of the mask 240 0 by the mask 0 1 gives the mask 240 0. *)
  Example udiv_by_one_bit_mask :
    kb_forward bvudiv [(8%positive, Tnum 240 0); (8%positive, Tnum 0 1)]
      8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The unsigned remainder of the mask 240 0 by the constant zero keeps the mask 240 0. *)
  Example urem_by_zero_keeps_dividend :
    kb_forward bvurem [(8%positive, Tnum 240 0); (8%positive, tnum_const 8%positive 0)]
      8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned less-than of the mask 128 0 and the constant 128 gives the mask 0 1. *)
  Example comparison_unsigned :
    kb_forward bvult [(8%positive, Tnum 128 0); (8%positive, tnum_const 8%positive 128)]
      1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed less-than of the masks 0 128 and 128 0 gives the mask 0 1. *)
  Example comparison_signed :
    kb_forward bvslt [(8%positive, Tnum 0 128); (8%positive, Tnum 128 0)]
      1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Equality of the masks 1 0 and 0 1 gives the mask 1 0. *)
  Example comparison_equal :
    kb_forward bveq [(8%positive, Tnum 1 0); (8%positive, Tnum 0 1)]
      1%positive = Tnum 1 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A choice with a known true condition gives the mask of its first branch. *)
  Example conditional_precision :
    kb_forward bvite [(1%positive, tnum_const 1%positive 1); (8%positive, Tnum 15 128);
      (8%positive, tnum_top)] 8%positive = Tnum 15 128.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension of the mask 8 1 from width four to width eight gives 248 1. *)
  Example width_zext :
    kb_forward (bvzext 4%positive) [(4%positive, Tnum 8 1)] 8%positive = Tnum 248 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of the mask 0 8 from width four to width eight gives 0 248. *)
  Example width_sext :
    kb_forward (bvsext 4%positive) [(4%positive, Tnum 0 8)] 8%positive = Tnum 0 248.
  Proof. vm_compute. reflexivity. Qed.

  (** Truncation of the mask 128 1 from width eight to width four gives 0 1. *)
  Example width_trunc :
    kb_forward (bvtrunc 4%positive) [(8%positive, Tnum 128 1)] 4%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits two to five of the mask 24 4 gives the mask 6 1. *)
  Example width_extract :
    kb_forward (bvextract 5 2) [(8%positive, Tnum 24 4)] 4%positive = Tnum 6 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenating the masks of widths three and two gives the mask 9 18 at width five. *)
  Example width_concat :
    kb_forward bvconcat [(3%positive, Tnum 2 4); (2%positive, Tnum 1 2)]
      5%positive = Tnum 9 18.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits zero to three of a known four-bit mask keeps its known bits. *)
  Example extract_low_known_word :
    kb_forward (bvextract 3 0) [(4%positive, Tnum 8 1)] 4%positive = Tnum 8 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits four to seven of a known byte gives the high nibble. *)
  Example extract_high_known_nibble :
    kb_forward (bvextract 7 4) [(8%positive, Tnum 240 15)] 4%positive = Tnum 15 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits zero to three of a known byte gives the low nibble with its mask. *)
  Example extract_low_nibble_of_byte :
    kb_forward (bvextract 3 0) [(8%positive, Tnum 240 15)] 4%positive = Tnum 0 15.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits zero to three of top at width four gives top. *)
  Example extract_low_top_of_nibble :
    kb_forward (bvextract 3 0) [(4%positive, tnum_top)] 4%positive = tnum_top.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits four to seven of top gives top. *)
  Example extract_high_top_of_byte :
    kb_forward (bvextract 7 4) [(8%positive, tnum_top)] 4%positive = tnum_top.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits zero to three of top at width eight gives top. *)
  Example extract_low_top_of_byte :
    kb_forward (bvextract 3 0) [(8%positive, tnum_top)] 4%positive = tnum_top.
  Proof. vm_compute. reflexivity. Qed.

End ForwardTests.

(** * Assume *)

Module AssumeTests.

  (** Assuming the sum of top and one is 7 narrows the first operand to 249 6. *)
  Example add_constant_first_operand :
    kb_assume bvadd [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 1)]
      8%positive (tnum_const 8%positive 7) = [Tnum 249 6; Tnum 254 1].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming an arithmetic shift of top by 8 gives 255 narrows the operands. *)
  Example sign_fill_operands :
    kb_assume bvashr [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 8)]
      8%positive (tnum_const 8%positive 255) = [Tnum 0 128; Tnum 247 8].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming an unsigned less-than holds narrows the operands against the constant 8. *)
  Example unsigned_comparison_operands :
    kb_assume bvult [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 8)]
      1%positive (tnum_const 1%positive 1) = [Tnum 248 0; Tnum 247 8].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a concatenation gives 21 narrows the two operands. *)
  Example concat_operands :
    kb_assume bvconcat [(3%positive, tnum_top); (2%positive, tnum_top)]
      5%positive (tnum_const 5%positive 21) = [Tnum 2 5; Tnum 2 1].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a left shift by the constant 3 narrows the shifted operand to 124 1. *)
  Example variable_shift_shifted_operand :
    kb_assume bvshl [(8%positive, tnum_top); (8%positive, Tnum 254 0)]
      8%positive (tnum_const 8%positive 3) = [Tnum 124 1; Tnum 254 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming an arithmetic shift gives the mask 0 128 narrows the operands to 0 128 and 0 0. *)
  Example variable_arithmetic_shift_operands :
    kb_assume bvashr [(8%positive, tnum_top); (8%positive, tnum_top)]
      8%positive (Tnum 0 128) = [Tnum 0 128; Tnum 0 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a left rotation of the constant one narrows the operands at width five. *)
  Example variable_rotation_operands :
    kb_assume bvrotl [(5%positive, tnum_top); (5%positive, Tnum 15 0)]
      5%positive (tnum_const 5%positive 1) = [Tnum 14 0; Tnum 15 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a bitwise and gives the mask 2 1 and narrows the second operand to 0 3. *)
  Example bitwise_and_operands :
    kb_assume bvand [(8%positive, tnum_top); (8%positive, Tnum 0 2)]
      8%positive (Tnum 2 1) = [Tnum 2 1; Tnum 0 3].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a bitwise or gives the mask 1 2 and narrows the first operand to 3 0. *)
  Example bitwise_or_operands :
    kb_assume bvor [(8%positive, tnum_top); (8%positive, Tnum 2 0)]
      8%positive (Tnum 1 2) = [Tnum 1 2; Tnum 3 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a sign extension gives the mask 0 128 narrows the width-four operand to 0 8. *)
  Example width_sext_operand :
    kb_assume (bvsext 4%positive) [(4%positive, tnum_top)]
      8%positive (Tnum 0 128) = [Tnum 0 8].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming an extraction of the constant 5 narrows the width-eight operand to 8 20. *)
  Example width_extract_operand :
    kb_assume (bvextract 4 2) [(8%positive, tnum_top)]
      3%positive (tnum_const 3%positive 5) = [Tnum 8 20].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a truncation of the constant 3 narrows the width-eight operand to 12 3. *)
  Example width_trunc_operand :
    kb_assume (bvtrunc 4%positive) [(8%positive, tnum_top)]
      4%positive (tnum_const 4%positive 3) = [Tnum 12 3].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming equality holds narrows both operands to the mask 15 128. *)
  Example equality_operands :
    kb_assume bveq [(8%positive, Tnum 15 0); (8%positive, Tnum 0 128)]
      1%positive (tnum_const 1%positive 1) = [Tnum 15 128; Tnum 15 128].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a subtraction of one gives 7 narrows the first operand to 247 8. *)
  Example subtraction_operands :
    kb_assume bvsub [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 1)]
      8%positive (tnum_const 8%positive 7) = [Tnum 247 8; Tnum 254 1].
  Proof. vm_compute. reflexivity. Qed.

End AssumeTests.

(** * Singletons *)

Module SingletonTests.

  (** Signed division of the constants 7 and 2 gives the exact mask 252 3. *)
  Example signed_division_of_constants :
    kb_forward bvsdiv [(8%positive, tnum_const 8%positive 7);
      (8%positive, tnum_const 8%positive 2)] 8%positive = Tnum 252 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The leading-zero count of the constant zero at width five is the exact mask 26 5. *)
  Example leading_zero_count_of_constant :
    kb_forward bvclz [(5%positive, tnum_const 5%positive 0)] 5%positive = Tnum 26 5.
  Proof. vm_compute. reflexivity. Qed.

  (** The signed remainder of the mask 128 0 keeps the sign bit even with an unknown divisor. *)
  Example signed_remainder_keeps_sign :
    kb_forward bvsrem [(8%positive, Tnum 128 0); (8%positive, tnum_top)]
      8%positive = Tnum 128 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of top keeps the bound 240 0 at width eight. *)
  Example population_count_of_top :
    kb_forward bvpopcnt [(8%positive, tnum_top)] 8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

End SingletonTests.

(** * Malformed *)

Module MalformedTests.

  (** The shared harness gives top for addition of operands of different widths. *)
  Example mixed_width_operands_are_top :
    D.forward (BOp bvadd) [TVal 8%positive tnum_top; TVal 4%positive tnum_top] = TAny.
  Proof. vm_compute. reflexivity. Qed.

  (** The harness gives bottom for addition with no operands. *)
  Example nullary_addition_is_bottom :
    D.forward (BOp bvadd) [] = TBot.
  Proof. vm_compute. reflexivity. Qed.

  (** The harness gives bottom for multiplication with no operands. *)
  Example nullary_multiplication_is_bottom :
    D.forward (BOp bvmul) [] = TBot.
  Proof. vm_compute. reflexivity. Qed.

  (* The old malformed fallback normalized the one-operand output to [Tnum 28 1]
     and the three-operand output to [Tnum 28 1; Tnum 6 0; Tnum 1 1].
     The shared harness keeps [Tnum (-4) 33] and
     [Tnum (-4) 33; Tnum (-2) 8; Tnum 3 3] respectively. *)

  (** Assuming addition with no operands gives no backward masks. *)
  Example backward_empty_inputs :
    kb_assume bvadd [] 5%positive tnum_top = [].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming addition with one operand keeps that operand's mask. *)
  Example backward_one_input :
    kb_assume bvadd [(5%positive, Tnum (-4) 33)] 5%positive tnum_top = [Tnum (-4) 33].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming addition with the malformed operands keeps each of them. *)
  Example backward_malformed_inputs :
    kb_assume bvadd kb_test_malformed_inputs 5%positive tnum_top =
      [Tnum (-4) 33; Tnum (-2) 8; Tnum 3 3].
  Proof. vm_compute. reflexivity. Qed.

End MalformedTests.

(** * Bridges *)

Module BridgeTests.

  (** A right rotation at width one of 255 gives 1. *)
  Example rotation_at_width_one :
    wrotr 1%positive 1 255 = 1.
  Proof. vm_compute. auto. Qed.

  (** A right rotation at width five of 16 by one gives 16. *)
  Example rotation_at_width_five :
    wrotr 5%positive 1 16 = 16.
  Proof. vm_compute. auto. Qed.

  (** A right rotation by the amount 33 reduces to a rotation by one at width five. *)
  Example rotation_amount_reduces_modulo_width :
    wrotr 5%positive 33 0 = 1.
  Proof. vm_compute. auto. Qed.

  (** Extracting bits two to five of 260 at width eight gives 1 at width four. *)
  Example extract_wraps_input :
    eval_op (bvextract 5 2) [(8%positive, 260)] = Some (4%positive, 1).
  Proof. vm_compute. auto. Qed.

  (** Extracting bits two to five of the all-ones byte gives 15 at width four. *)
  Example extract_all_ones :
    eval_op (bvextract 5 2) [(8%positive, -1)] = Some (4%positive, 15).
  Proof. vm_compute. auto. Qed.

  (** Extracting bit zero of the all-ones bit at width one gives one. *)
  Example extract_width_one :
    eval_op (bvextract 0 0) [(1%positive, -1)] = Some (1%positive, 1).
  Proof. vm_compute. auto. Qed.

  (** Extracting bits zero to eight of a byte is outside the operand and gives no result. *)
  Example extract_past_width_is_none :
    eval_op (bvextract 8 0) [(8%positive, 1)] = None.
  Proof. vm_compute. auto. Qed.

  (** Extracting bits one to zero, with the endpoints reversed, gives no result. *)
  Example extract_reversed_endpoints_is_none :
    eval_op (bvextract 0 1) [(8%positive, 1)] = None.
  Proof. vm_compute. auto. Qed.

  (** A right rotation of the negative raw amount -31 by -28 at width five gives 2. *)
  Example rotation_negative_raw_width_five :
    wrotr 5%positive (-31) (-28) = 2.
  Proof. vm_compute. auto. Qed.

  (** A right rotation of the negative raw amount -1 by -1 at width one gives 1. *)
  Example rotation_negative_raw_width_one :
    wrotr 1%positive (-1) (-1) = 1.
  Proof. vm_compute. auto. Qed.

  (** A left shift of the constant one by the mask 26 4 at width five gives 15 0. *)
  Example cutoff_left_shift :
    kb_forward bvshl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 26 4)]
      5%positive = Tnum 15 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical right shift of the constant 16 by the mask 26 4 at width five gives 30 0. *)
  Example cutoff_logical_right_shift :
    kb_forward bvlshr [(5%positive, tnum_const 5%positive 16); (5%positive, Tnum 26 4)]
      5%positive = Tnum 30 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift of the constant 16 by the mask 23 0 gives 0 16. *)
  Example cutoff_arithmetic_right_shift :
    kb_forward bvashr [(5%positive, tnum_const 5%positive 16); (5%positive, Tnum 23 0)]
      5%positive = Tnum 0 16.
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation of the constant one by the mask 23 0 gives 22 0. *)
  Example cutoff_left_rotation :
    kb_forward bvrotl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 23 0)]
      5%positive = Tnum 22 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation of the constant one by the mask 23 0 gives 26 0. *)
  Example cutoff_right_rotation :
    kb_forward bvrotr [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 23 0)]
      5%positive = Tnum 26 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift of the constant one by the wide mask 16 7 gives 31 0. *)
  Example cutoff_left_shift_wide_amount :
    kb_forward bvshl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 16 7)]
      5%positive = Tnum 31 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation of the constant one by the wide mask 16 7 gives 26 0. *)
  Example cutoff_left_rotation_wide_amount :
    kb_forward bvrotl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 16 7)]
      5%positive = Tnum 26 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Every variable shift and rotation at width five contains each concrete result. *)
  Example width_five_cutoffs_are_sound :
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

  (** Refining the malformed operands with no results gives their own masks. *)
  Example refine_without_results :
    tnum_refine kb_test_malformed_inputs [] =
      [Tnum (-4) 33; Tnum (-2) 8; Tnum 3 3].
  Proof. vm_compute. reflexivity. Qed.

  (** Refining the malformed operands with one result refines the first operand only. *)
  Example refine_with_one_result :
    tnum_refine kb_test_malformed_inputs [tnum_top] =
      [Tnum 28 1; Tnum (-2) 8; Tnum 3 3].
  Proof. vm_compute. reflexivity. Qed.

  (** Refining the malformed operands with extra results ignores the extra results. *)
  Example refine_with_extra_results :
    tnum_refine kb_test_malformed_inputs [tnum_top; tnum_top; tnum_top; Tnum 31 31] =
      [Tnum 28 1; Tnum 6 0; Tnum 1 1].
  Proof. vm_compute. reflexivity. Qed.

  (** Refining no operands gives no masks. *)
  Example refine_empty_operands :
    tnum_refine [] [Tnum 31 31] = [].
  Proof. vm_compute. reflexivity. Qed.

  (** Backward results keep the length and refine the operands for every tested input. *)
  Example backward_keeps_length_and_refines :
    forallb (fun xs => kb_test_refines xs (kb_assume bvadd xs 5%positive (Tnum 1 1)))
      [[]; [(5%positive, Tnum (-4) 33)]; kb_test_malformed_inputs] = true.
  Proof.
    vm_compute. auto.
  Qed.

  (** Refining the malformed operands by any tested results keeps their lengths and masks. *)
  Example refine_is_reductive :
    forallb (fun qs => kb_test_refines kb_test_malformed_inputs
      (tnum_refine kb_test_malformed_inputs qs))
      [[]; [tnum_top]; [tnum_top; tnum_top; tnum_top; Tnum 31 31]] = true.
  Proof.
    vm_compute. auto.
  Qed.

End BridgeTests.

(** * Multiplier *)

Module MultiplierTests.

  (** The default multiplier gives the mask 251 0 for four times 254 0 at width eight. *)
  Example default_multiplier_staged :
    StagesOps.tnum_forward_raw bvmul
      [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)]
      8%positive = Tnum 251 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The harness multiplier gives the mask 3 0 for four times 254 0 at width eight. *)
  Example default_multiplier_harness :
    kb_forward bvmul
      [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)]
      8%positive = Tnum 3 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The staged and low multipliers agree on an invalid result width of four. *)
  Example staged_matches_low_on_invalid_width :
    StagesOps.tnum_forward_raw bvmul
      [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)] 4%positive =
    LowOps.tnum_forward_raw bvmul
      [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)] 4%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** The staged and low multipliers agree on a single operand. *)
  Example staged_matches_low_on_invalid_arity :
    StagesOps.tnum_forward_raw bvmul [(8%positive, tnum_top)] 8%positive =
    LowOps.tnum_forward_raw bvmul [(8%positive, tnum_top)] 8%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** Each requested result width gives the same masks on both multipliers. *)
  Example result_width_on_both_multipliers :
    let check := fun forward =>
      forward bvnot [(4%positive, tnum_const 4%positive 0)] 3%positive = Tnum 0 7 /\
      forward bvnot [(4%positive, tnum_const 4%positive 0)] 5%positive = Tnum 0 15 /\
      forward bvadd [(4%positive, tnum_const 4%positive 15);
        (4%positive, tnum_const 4%positive 1)] 3%positive = Tnum 7 0 /\
      forward (bvzext 1%positive) [(4%positive, tnum_const 4%positive 15)]
        3%positive = Tnum 0 7 /\
      forward bvconcat [(4%positive, tnum_const 4%positive 2);
        (4%positive, tnum_const 4%positive 3)] 3%positive = Tnum 220 35 in
    check LowOps.tnum_forward_raw /\ check StagesOps.tnum_forward_raw.
  Proof. vm_compute. repeat split; reflexivity. Qed.

End MultiplierTests.

(** * Payload *)

Module PayloadTests.

  (** The payload backward computation of the malformed operands, as the refined masks. *)
  Definition kb_payload_assume (o : op) (xs : list (width * tnum)) (rw : width) (q : tnum) :=
    tnum_refine xs (tnum_backward_raw o xs rw q).

  (** The low payload gives the singleton signed division of 7 by 2 as the mask 0 0. *)
  Example singleton_signed_division :
    LowOps.tnum_forward_raw bvsdiv [(8%positive, tnum_const 8%positive 7);
      (8%positive, tnum_const 8%positive 2)] 8%positive = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The low payload gives the leading-zero count of the constant zero as the mask 24 0. *)
  Example singleton_leading_zero_count :
    LowOps.tnum_forward_raw bvclz [(5%positive, tnum_const 5%positive 0)]
      5%positive = Tnum 24 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The low payload gives top for addition with no operands. *)
  Example nullary_addition_is_top :
    LowOps.tnum_forward_raw bvadd [] 8%positive = tnum_top.
  Proof. vm_compute. reflexivity. Qed.

  (** The staged payload gives top for multiplication with no operands. *)
  Example nullary_multiplication_is_top :
    StagesOps.tnum_forward_raw bvmul [] 4%positive = tnum_top.
  Proof. vm_compute. reflexivity. Qed.

  (** The payload backward computation with no operands gives no masks. *)
  Example backward_empty_inputs :
    kb_payload_assume bvadd [] 5%positive tnum_top = [].
  Proof. vm_compute. reflexivity. Qed.

  (** The payload backward computation with one operand gives the mask 28 1. *)
  Example backward_one_input :
    kb_payload_assume bvadd [(5%positive, Tnum (-4) 33)] 5%positive tnum_top = [Tnum 28 1].
  Proof. vm_compute. reflexivity. Qed.

  (** The payload backward computation of the malformed operands gives the refined masks. *)
  Example backward_malformed_inputs :
    kb_payload_assume bvadd kb_test_malformed_inputs 5%positive tnum_top =
      [Tnum 28 1; Tnum 6 0; Tnum 1 1].
  Proof. vm_compute. reflexivity. Qed.

End PayloadTests.

(** * Symbolic *)

Module SymbolicTests.

  (** Extracting bits two to five of any value at width at least six gives the wrapped quotient. *)
  Example extract_for_any_value : forall w x,
    (6 <= Pos.to_nat w)%nat ->
    eval_op (bvextract 5 2) [(w, x)] =
      Some (4%positive, wrap 4%positive (wrap w x / 4)).
  Proof.
    intros w x Hwidth. rewrite eval_op_extract.
    assert (Hslice : (2 <=? 5)%nat && (5 <? Pos.to_nat w)%nat = true).
    { apply andb_true_iff. split; [reflexivity|]. apply Nat.ltb_lt. lia. }
    rewrite Hslice. reflexivity.
  Qed.

  (** A right rotation is a left rotation by the complement of the amount, for every value. *)
  Example rotation_right_is_left_for_any_amount : forall w x y,
    wrotr w x y = wrotl w x (Zpos w - wrap w y mod Zpos w).
  Proof.
    apply wrotr_value.
  Qed.

End SymbolicTests.

(** * Tables *)

Module TableTests.

  (** The public table gives the shifted concatenation of two byte masks as 61692 3841. *)
  Example shifted_concat_from_public_table :
    kb_forward bvconcat [(8%positive, Tnum 240 15); (8%positive, Tnum 252 1)]
      16%positive = Tnum 61692 3841.
  Proof. vm_compute. reflexivity. Qed.

End TableTests.

(** The source observations below are kept for reference and check nothing. *)

(* The old tagged domain returned TBot for this malformed input. *)
(* The landed payload-level source observations were:
Example kb_signed_remainder_sign :
  kb_forward bvsrem [(8%positive, Tnum 128 0); (8%positive, tnum_top)]
    8%positive = Tnum 128 0 /\
  kb_forward bvsdiv [(8%positive, tnum_const 8%positive 7);
  (8%positive, tnum_const 8%positive 2)] 8%positive = tnum_top.
Proof. vm_compute. auto. Qed.

Example kb_zero_counts :
  eval_op bvclz [(1%positive, 0)] = Some (1%positive, 1) /\
  eval_op bvctz [(1%positive, 0)] = Some (1%positive, 1) /\
  kb_forward bvclz [(5%positive, tnum_const 5%positive 0)]
    5%positive = Tnum 24 0 /\
  kb_forward bvpopcnt [(8%positive, tnum_top)] 8%positive = Tnum 240 0.
Proof. vm_compute. auto. Qed.
*)

(* The old malformed fallback normalized the one-operand output to [Tnum 28 1]
   and the three-operand output to [Tnum 28 1; Tnum 6 0; Tnum 1 1].
   The shared harness keeps [Tnum (-4) 33] and
   [Tnum (-4) 33; Tnum (-2) 8; Tnum 3 3] respectively. *)
(* The landed observation was:
Example kb_backward_malformed_arity_observations :
  kb_assume bvadd [] 5%positive tnum_top = [] /\
  kb_assume bvadd [(5%positive, Tnum (-4) 33)] 5%positive tnum_top = [Tnum 28 1] /\
  kb_assume bvadd kb_test_malformed_inputs 5%positive tnum_top =
    [Tnum 28 1; Tnum 6 0; Tnum 1 1].
Proof. vm_compute. repeat split; reflexivity. Qed.
*)

(* Original payload-level and tagged malformed observations:
Example kb_nullary_legacy_choices :
  pforward known_bits_classic_domain bvadd [] 8%positive = tnum_top /\
  pforward known_bits_domain bvmul [] 4%positive = tnum_top.
Proof. vm_compute. auto. Qed.
Example kb_malformed_width :
  forward (tagged_domain known_bits_classic_domain) bvadd
    [TVal 8%positive tnum_top; TVal 4%positive tnum_top] = TBot.
Proof. vm_compute. reflexivity. Qed.
*)

(* The charged Cost interface was removed. These source clock claims are deferred to
   timing and are not executable tests of generated clocks.
Example kb_variable_expansion_cost :
  Cost.ticks (tnum_variable_c bvshl 8%positive (tnum_const 8%positive 1) (Tnum 252 0)) =
    2%N /\
  Cost.ticks (tnum_back_variable_shift_c bvshl 8%positive (Tnum 252 0) (Tnum 0 1)) =
    4%N.
Proof. vm_compute. auto. Qed.
Example kb_nonempty_builder_charge_control :
  pforward_c (known_bits_word_domain known_bits_default_options) bvadd
    [(8%positive, Tnum 240 7); (8%positive, tnum_const 8%positive 1)] 8%positive =
  pforward_c (known_bits_word_builder known_bits_default_options) bvadd
    [(8%positive, Tnum 240 7); (8%positive, tnum_const 8%positive 1)] 8%positive.
Proof. vm_compute. reflexivity. Qed.
*)
