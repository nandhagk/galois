(** * Known-bit harness observations

    Known-bit transfers run through the shared tagged word harness.
    For example, a variable shift joins the possible bit positions.
    Builds on: KnownBitsBack, Tagged and Harness.

    Groups:
    - [ForwardTests] Forward transfers of operations, with their widths and conflicts.
    - [AssumeTests] Backward transfers that narrow the operands of each operation.
    - [SingletonTests] Singleton operands and counts that the shared harness evaluates exactly.
    - [MalformedTests] Operand lists of the wrong arity, and the harness's answer for them.
    - [BridgeTests] Rotation, extraction and refinement at the boundaries of the word operations.
    - [MultiplierTests] The staged multiplier against the low multiplier on the same inputs.
    - [PayloadTests] The direct payload computations of the low and staged modules.
    - [SymbolicTests] The extraction and rotation facts for every width and value.
    - [TableTests] The public table of the harness on shifted concatenation. *)

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

  (** Adding a mask with conflicting bits to a constant conflicts in every bit at width eight. *)
  Example conflicting_masks_add :
    kb_forward bvadd [(8%positive, Tnum 1 1); (8%positive, tnum_const 8%positive 1)]
      8%positive = Tnum 255 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift by an amount with conflicting bits conflicts in every bit at width eight. *)
  Example shift_conflicting_amount :
    kb_forward bvshl [(8%positive, tnum_top); (8%positive, Tnum 1 1)]
      8%positive = Tnum 255 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift of the constant one by zero to three bits keeps the high four bits zero. *)
  Example variable_logical_shift :
    kb_forward bvshl [(8%positive, tnum_const 8%positive 1); (8%positive, Tnum 252 0)]
      8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical right shift of 128 by zero or eight bits leaves only the top bit possible. *)
  Example variable_oversized_shift :
    kb_forward bvlshr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 247 0)]
      8%positive = Tnum 127 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift of 128 by zero to three bits keeps the sign bit one. *)
  Example variable_arithmetic_shift :
    kb_forward bvashr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 252 0)]
      8%positive = Tnum 15 128.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift of 128 by zero or eight bits keeps the sign bit one. *)
  Example variable_arithmetic_oversized :
    kb_forward bvashr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 247 0)]
      8%positive = Tnum 0 128.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift by the constant 255 is a shift past the width and gives zero at width eight. *)
  Example oversized_base_left :
    kb_forward bvshl [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 255)]
      8%positive = Tnum 255 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift of a non-negative value by 255 gives zero. *)
  Example oversized_base_arithmetic :
    kb_forward bvashr [(8%positive, Tnum 128 0); (8%positive, tnum_const 8%positive 255)]
      8%positive = Tnum 255 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift by the constant 256 wraps to a shift by zero at width eight. *)
  Example wrapped_amount :
    kb_forward bvshl [(8%positive, Tnum 15 128); (8%positive, tnum_const 8%positive 256)]
      8%positive = Tnum 15 128.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating a one left by zero or sixteen at width five leaves bits 0 and 1 unknown. *)
  Example rotation_nonpower_left :
    kb_forward bvrotl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 15 0)]
      5%positive = Tnum 28 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating a one right by zero or sixteen at width five leaves bits 0 and 4 unknown. *)
  Example rotation_nonpower_right :
    kb_forward bvrotr [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 15 0)]
      5%positive = Tnum 14 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation at width one of the constant one gives the constant one. *)
  Example rotation_width_one_left :
    kb_forward bvrotl [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
      1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation at width one of the constant one gives the constant one. *)
  Example rotation_width_one_right :
    kb_forward bvrotr [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
      1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift at width one of the constant one by an unknown amount is unknown. *)
  Example shift_width_one :
    kb_forward bvshl [(1%positive, tnum_const 1%positive 1); (1%positive, tnum_top)]
      1%positive = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned division of a value below sixteen by the constant zero is unknown. *)
  Example udiv_by_zero_is_top :
    kb_forward bvudiv [(8%positive, Tnum 240 0); (8%positive, tnum_const 8%positive 0)]
      8%positive = tnum_top.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned division of a value below sixteen by an odd divisor gives a value below sixteen. *)
  Example udiv_by_one_bit_mask :
    kb_forward bvudiv [(8%positive, Tnum 240 0); (8%positive, Tnum 0 1)]
      8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The unsigned remainder of a value below sixteen by zero stays below sixteen. *)
  Example urem_by_zero_keeps_dividend :
    kb_forward bvurem [(8%positive, Tnum 240 0); (8%positive, tnum_const 8%positive 0)]
      8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A value below 128 is known to be unsigned-less than the constant 128. *)
  Example comparison_unsigned :
    kb_forward bvult [(8%positive, Tnum 128 0); (8%positive, tnum_const 8%positive 128)]
      1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative value is known to be signed-less than a non-negative value. *)
  Example comparison_signed :
    kb_forward bvslt [(8%positive, Tnum 0 128); (8%positive, Tnum 128 0)]
      1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Values that differ in a known bit are known to be unequal. *)
  Example comparison_equal :
    kb_forward bveq [(8%positive, Tnum 1 0); (8%positive, Tnum 0 1)]
      1%positive = Tnum 1 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A choice with a known true condition gives the mask of its first branch. *)
  Example conditional_precision :
    kb_forward bvite [(1%positive, tnum_const 1%positive 1); (8%positive, Tnum 15 128);
      (8%positive, tnum_top)] 8%positive = Tnum 15 128.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension from width four to eight makes the new high bits known zero. *)
  Example width_zext :
    kb_forward (bvzext 4%positive) [(4%positive, Tnum 8 1)] 8%positive = Tnum 248 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of a negative four-bit value makes the new high bits known one. *)
  Example width_sext :
    kb_forward (bvsext 4%positive) [(4%positive, Tnum 0 8)] 8%positive = Tnum 0 248.
  Proof. vm_compute. reflexivity. Qed.

  (** Truncation to width four keeps the known low bit and drops the high bits. *)
  Example width_trunc :
    kb_forward (bvtrunc 4%positive) [(8%positive, Tnum 128 1)] 4%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits two to five of a byte moves them to the low end of a nibble. *)
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

  (** Extracting bits four to seven of the byte constant 15 gives the zero nibble. *)
  Example extract_high_known_nibble :
    kb_forward (bvextract 7 4) [(8%positive, Tnum 240 15)] 4%positive = Tnum 15 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits zero to three of the byte constant 15 gives the one nibble. *)
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

  (** Signed division of the constants 7 and 2 gives the constant 3. *)
  Example signed_division_of_constants :
    kb_forward bvsdiv [(8%positive, tnum_const 8%positive 7);
      (8%positive, tnum_const 8%positive 2)] 8%positive = Tnum 252 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The leading-zero count of the constant zero at width five is the constant 5. *)
  Example leading_zero_count_of_constant :
    kb_forward bvclz [(5%positive, tnum_const 5%positive 0)] 5%positive = Tnum 26 5.
  Proof. vm_compute. reflexivity. Qed.

  (** The signed remainder of a non-negative value stays non-negative for any divisor. *)
  Example signed_remainder_keeps_sign :
    kb_forward bvsrem [(8%positive, Tnum 128 0); (8%positive, tnum_top)]
      8%positive = Tnum 128 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of an unknown byte is below sixteen. *)
  Example population_count_of_top :
    kb_forward bvpopcnt [(8%positive, tnum_top)] 8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

End SingletonTests.

(** * Malformed *)

Module MalformedTests.

  (** The shared harness gives the unknown value for addition of operands of different widths. *)
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

  (** The shift and rotation operators whose cutoffs are checked. *)
  Definition cutoff_ops : list op := [bvshl; bvlshr; bvashr; bvrotl; bvrotr].

  (** The masks of the shifted value at width five. *)
  Definition cutoff_values : list tnum :=
    [tnum_const 5%positive 1; tnum_const 5%positive 16; Tnum 16 0].

  (** The masks of the shift amount at width five. *)
  Definition cutoff_amounts : list tnum := [Tnum 24 3; Tnum 26 4; Tnum 23 0; Tnum 16 7].

  (** The concrete words of width five that a mask contains. *)
  Definition cutoff_members (a : tnum) : list Z :=
    filter (kb_test_contains 5%positive a) kb_test_width_five_words.

  (** Whether the forward mask of an operator over two masks contains every concrete result. *)
  Definition cutoff_sound (o : op) (a b : tnum) : bool :=
    forallb (fun x => forallb (fun k =>
      match eval_op o [(5%positive, x); (5%positive, k)] with
      | Some (_, z) => kb_test_contains 5%positive
          (kb_forward o [(5%positive, a); (5%positive, b)] 5%positive) z
      | None => false
      end) (cutoff_members b)) (cutoff_members a).

  (** Every variable shift and rotation at width five contains each concrete result. *)
  Example width_five_cutoffs_are_sound :
    forallb (fun o => forallb (fun a => forallb (cutoff_sound o a) cutoff_amounts)
      cutoff_values) cutoff_ops = true.
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

  (** The staged multiplier leaves only bit two of four times zero or one unknown. *)
  Example default_multiplier_staged :
    StagesOps.tnum_forward_raw bvmul
      [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)]
      8%positive = Tnum 251 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The harness multiplier knows only bits 0 and 1 of four times zero or one. *)
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

  (** Cases of the requested result width: operator, operands, result width and expected mask. *)
  Definition result_width_cases : list (op * list (width * tnum) * width * tnum) :=
    [(bvnot, [(4%positive, tnum_const 4%positive 0)], 3%positive, Tnum 0 7);
     (bvnot, [(4%positive, tnum_const 4%positive 0)], 5%positive, Tnum 0 15);
     (bvadd, [(4%positive, tnum_const 4%positive 15); (4%positive, tnum_const 4%positive 1)],
       3%positive, Tnum 7 0);
     (bvzext 1%positive, [(4%positive, tnum_const 4%positive 15)], 3%positive, Tnum 0 7);
     (bvconcat, [(4%positive, tnum_const 4%positive 2); (4%positive, tnum_const 4%positive 3)],
       3%positive, Tnum 220 35)].

  (** The low multiplier gives the expected mask for each requested result width. *)
  Example result_width_on_low_multiplier :
    Forall (fun '(o, xs, rw, expected) => LowOps.tnum_forward_raw o xs rw = expected)
      result_width_cases.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The staged multiplier gives the expected mask for each requested result width. *)
  Example result_width_on_staged_multiplier :
    Forall (fun '(o, xs, rw, expected) => StagesOps.tnum_forward_raw o xs rw = expected)
      result_width_cases.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

End MultiplierTests.

(** * Payload *)

Module PayloadTests.

  (** The payload backward computation of the malformed operands, as the refined masks. *)
  Definition kb_payload_assume (o : op) (xs : list (width * tnum)) (rw : width) (q : tnum) :=
    tnum_refine xs (tnum_backward_raw o xs rw q).

  (** The low payload does not evaluate the signed division of 7 by 2 and gives top. *)
  Example singleton_signed_division :
    LowOps.tnum_forward_raw bvsdiv [(8%positive, tnum_const 8%positive 7);
      (8%positive, tnum_const 8%positive 2)] 8%positive = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The low payload bounds the leading-zero count of the constant zero below eight. *)
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

  (** The payload backward computation with one operand normalizes its mask to width five. *)
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

  (** The public table concatenates two byte masks with the first as the high byte. *)
  Example shifted_concat_from_public_table :
    kb_forward bvconcat [(8%positive, Tnum 240 15); (8%positive, Tnum 252 1)]
      16%positive = Tnum 61692 3841.
  Proof. vm_compute. reflexivity. Qed.

End TableTests.
