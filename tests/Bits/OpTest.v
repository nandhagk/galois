(** * Operator boundary examples

    Operators validate dynamic words before evaluating arithmetic and width changes.
    For example, unequal widths reject addition and concatenation accepts them.

    Groups:
    - [RawTests] Sixty-four-bit operands outside the normalized range.
    - [NormalizationTests] Normalization of in-range and out-of-range words.
    - [ArithmeticTests] Overflow and zero divisors.
    - [ComparisonTests] Unsigned, signed and equality comparisons, and their width checks.
    - [WidthTests] Width changes, concatenation, truncation and selection on valid operands.
    - [RejectionTests] Operand lists of the wrong length or with widths that do not fit.
    - [CountTests] Leading zeros, trailing zeros and population counts.
    - [CodeTests] The operator encodings and the distinctness of their tags.
    - [SymbolicTests] Width checks and value formulas for any operand width.

    Builds on: Word, Fun, Op and BaseEncoding. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Fun Op.
Import List.ListNotations.

Open Scope Z_scope.

(** * Raw operands *)

Module RawTests.

  (** Adding a negative and an above-modulus sixty-four-bit word normalizes the first operand. *)
  Example width64_add_normalizes_first_operand :
    eval_op bvadd [(64%positive, -1); (64%positive, 2 ^ 70)] = Some (64%positive, 2 ^ 64 - 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Adding the same operands in the other order normalizes the second operand. *)
  Example width64_add_normalizes_second_operand :
    eval_op bvadd [(64%positive, 2 ^ 70); (64%positive, -1)] = Some (64%positive, 2 ^ 64 - 1).
  Proof. vm_compute. reflexivity. Qed.

  (** The all-ones word is not unsigned-below an above-modulus word that normalizes to zero. *)
  Example width64_ult_all_ones_is_false :
    eval_op bvult [(64%positive, -1); (64%positive, 2 ^ 70)] = Some (1%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Zero is unsigned-below the all-ones word. *)
  Example width64_ult_zero_is_true :
    eval_op bvult [(64%positive, 2 ^ 70); (64%positive, -1)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

End RawTests.

(** * Normalization *)

Module NormalizationTests.

  (** Zero is a fixed point of normalization at width eight. *)
  Example normalize_keeps_zero : normalize_word (8%positive, 0) = (8%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** The largest eight-bit value is a fixed point of normalization. *)
  Example normalize_keeps_largest : normalize_word (8%positive, 255) = (8%positive, 255).
  Proof. vm_compute. reflexivity. Qed.

  (** The value 256 normalizes to zero at width eight. *)
  Example normalize_wraps_modulus_to_zero : normalize_word (8%positive, 256) = (8%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Negative one normalizes to 255 at width eight. *)
  Example normalize_negative_one_to_255 : normalize_word (8%positive, -1) = (8%positive, 255).
  Proof. vm_compute. reflexivity. Qed.

End NormalizationTests.

(** * Arithmetic *)

Module ArithmeticTests.

  (** Adding 200 and 100 at width eight wraps to 44. *)
  Example width8_add_wraps_to_44 :
    eval_op bvadd [(8%positive, 200); (8%positive, 100)] = Some (8%positive, 44).
  Proof. vm_compute. reflexivity. Qed.

  (** Multiplying 20 by 20 at width eight wraps to 144. *)
  Example width8_mul_wraps_to_144 :
    eval_op bvmul [(8%positive, 20); (8%positive, 20)] = Some (8%positive, 144).
  Proof. vm_compute. reflexivity. Qed.

  (** Subtracting one from zero at width eight wraps to 255. *)
  Example width8_sub_wraps_to_255 :
    eval_op bvsub [(8%positive, 0); (8%positive, 1)] = Some (8%positive, 255).
  Proof. vm_compute. reflexivity. Qed.

  (** Negating the minimum at width eight gives the minimum. *)
  Example width8_neg_minimum_is_minimum :
    eval_op bvneg [(8%positive, 128)] = Some (8%positive, 128).
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned division by a zero word yields the all-ones word. *)
  Example zero_divisor_udiv_is_all_ones :
    eval_op bvudiv [(8%positive, 7); (8%positive, 0)] = Some (8%positive, 255).
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned remainder by a zero word yields the dividend. *)
  Example zero_divisor_urem_is_dividend :
    eval_op bvurem [(8%positive, 7); (8%positive, 0)] = Some (8%positive, 7).
  Proof. vm_compute. reflexivity. Qed.

  (** Signed division by a zero word yields one for a negative dividend. *)
  Example zero_divisor_sdiv_is_one :
    eval_op bvsdiv [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Signed remainder by a zero word yields the dividend. *)
  Example zero_divisor_srem_is_dividend :
    eval_op bvsrem [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 249).
  Proof. vm_compute. reflexivity. Qed.

  (** Signed modulus by a zero word yields the dividend. *)
  Example zero_divisor_smod_is_dividend :
    eval_op bvsmod [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 249).
  Proof. vm_compute. reflexivity. Qed.

End ArithmeticTests.

(** * Comparisons *)

Module ComparisonTests.

  (** Unsigned order puts 255 above one. *)
  Example unsigned_order_puts_255_above_one :
    eval_op bvult [(8%positive, 255); (8%positive, 1)] = Some (1%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Signed order puts 255, which is negative one, below one. *)
  Example signed_order_puts_255_below_one :
    eval_op bvslt [(8%positive, 255); (8%positive, 1)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Equality normalizes negative one and 255 to the same word. *)
  Example equality_normalizes_inputs :
    eval_op bveq [(8%positive, -1); (8%positive, 255)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Inequality of zero and 255 holds. *)
  Example inequality_of_zero_and_255 :
    eval_op bvne [(8%positive, 0); (8%positive, 255)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned less-or-equal holds for equal operands. *)
  Example unsigned_order_reflexive :
    eval_op bvule [(8%positive, 5); (8%positive, 5)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Signed less-or-equal holds for the minimum and 127. *)
  Example signed_order_minimum_at_most_127 :
    eval_op bvsle [(8%positive, 128); (8%positive, 127)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned comparison of unequal widths is rejected. *)
  Example unsigned_comparison_rejects_unequal_widths :
    eval_op bvult [(8%positive, 1); (4%positive, 2)] = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Equality of unequal widths is rejected. *)
  Example equality_rejects_unequal_widths :
    eval_op bveq [(8%positive, -1); (4%positive, 255)] = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed comparison of unequal widths is rejected. *)
  Example signed_comparison_rejects_unequal_widths :
    eval_op bvslt [(8%positive, -1); (1%positive, 0)] = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Equal width-eight operands are accepted by equality. *)
  Example equality_accepts_equal_widths :
    eval_op bveq [(8%positive, -1); (8%positive, 255)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned comparison accepts equal width-eight operands. *)
  Example unsigned_comparison_accepts_equal_widths :
    eval_op bvult [(8%positive, 1); (8%positive, 2)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Signed comparison accepts equal width-eight operands. *)
  Example signed_comparison_accepts_equal_widths :
    eval_op bvslt [(8%positive, -1); (8%positive, 0)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Width-one unsigned comparison accepts equal width-one operands. *)
  Example width1_unsigned_comparison :
    eval_op bvult [(1%positive, 0); (1%positive, 1)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

End ComparisonTests.

(** * Width changes *)

Module WidthTests.

  (** Zero extension of 255 gives the sixteen-bit value 255. *)
  Example zext_of_255 :
    eval_op (bvzext 8%positive) [(8%positive, 255)] = Some (16%positive, 255).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of 255 gives the sixteen-bit all-ones value. *)
  Example sext_of_255 :
    eval_op (bvsext 8%positive) [(8%positive, 255)] = Some (16%positive, 65535).
  Proof. vm_compute. reflexivity. Qed.

  (** Truncating 165 to four bits keeps the low nibble, five. *)
  Example trunc_165_to_four_bits :
    eval_op (bvtrunc 4%positive) [(8%positive, 165)] = Some (4%positive, 5).
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits four to seven of 165 gives ten. *)
  Example extract_high_nibble_of_165 :
    eval_op (bvextract 7 4) [(8%positive, 165)] = Some (4%positive, 10).
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenating ten and five at width four gives 165. *)
  Example concat_of_nibbles_is_165 :
    eval_op bvconcat [(4%positive, 10); (4%positive, 5)] = Some (8%positive, 165).
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension of 127 keeps it. *)
  Example zext_keeps_127 :
    eval_op (bvzext 8%positive) [(8%positive, 127)] = Some (16%positive, 127).
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension of negative one wraps to 255 before widening. *)
  Example zext_wraps_negative_one :
    eval_op (bvzext 8%positive) [(8%positive, -1)] = Some (16%positive, 255).
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension of 256 wraps to zero before widening. *)
  Example zext_wraps_256_to_zero :
    eval_op (bvzext 8%positive) [(8%positive, 256)] = Some (16%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension of 257 wraps to one before widening. *)
  Example zext_wraps_257_to_one :
    eval_op (bvzext 8%positive) [(8%positive, 257)] = Some (16%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension of negative one at width one gives one. *)
  Example width1_zext_of_negative_one :
    eval_op (bvzext 1%positive) [(1%positive, -1)] = Some (2%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension of zero at width one gives zero. *)
  Example width1_zext_of_zero :
    eval_op (bvzext 1%positive) [(1%positive, 0)] = Some (2%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of 127 keeps it, since the sign bit is clear. *)
  Example sext_keeps_127 :
    eval_op (bvsext 8%positive) [(8%positive, 127)] = Some (16%positive, 127).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of 128 fills the upper bits with ones. *)
  Example sext_of_128 :
    eval_op (bvsext 8%positive) [(8%positive, 128)] = Some (16%positive, 65408).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of negative one gives the all-ones sixteen-bit word. *)
  Example sext_of_negative_one :
    eval_op (bvsext 8%positive) [(8%positive, -1)] = Some (16%positive, 65535).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of 256 wraps to zero before widening. *)
  Example sext_wraps_256_to_zero :
    eval_op (bvsext 8%positive) [(8%positive, 256)] = Some (16%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of 384 wraps to 128 before widening. *)
  Example sext_wraps_384_to_128 :
    eval_op (bvsext 8%positive) [(8%positive, 384)] = Some (16%positive, 65408).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of one at width one gives three. *)
  Example width1_sext_of_one :
    eval_op (bvsext 1%positive) [(1%positive, 1)] = Some (2%positive, 3).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension of zero at width one gives zero. *)
  Example width1_sext_of_zero :
    eval_op (bvsext 1%positive) [(1%positive, 0)] = Some (2%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Truncating negative one to four bits gives fifteen. *)
  Example trunc_negative_one_to_four_bits :
    eval_op (bvtrunc 4%positive) [(8%positive, -1)] = Some (4%positive, 15).
  Proof. vm_compute. reflexivity. Qed.

  (** Truncating 256 to four bits gives zero. *)
  Example trunc_256_to_four_bits_is_zero :
    eval_op (bvtrunc 4%positive) [(8%positive, 256)] = Some (4%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Truncating 271 to four bits gives fifteen. *)
  Example trunc_271_to_four_bits :
    eval_op (bvtrunc 4%positive) [(8%positive, 271)] = Some (4%positive, 15).
  Proof. vm_compute. reflexivity. Qed.

  (** Truncating 257 to the same width gives one. *)
  Example trunc_257_to_same_width :
    eval_op (bvtrunc 8%positive) [(8%positive, 257)] = Some (8%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Truncating negative one to width one gives one. *)
  Example width1_trunc_of_negative_one :
    eval_op (bvtrunc 1%positive) [(1%positive, -1)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Truncating a wider word to width one keeps its low bit. *)
  Example width1_trunc_of_wider_word :
    eval_op (bvtrunc 1%positive) [(8%positive, 2)] = Some (1%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenating four-bit ten with eight-bit five gives 2565. *)
  Example concat_normalizes_each_operand :
    eval_op bvconcat [(4%positive, 10); (8%positive, 5)] = Some (12%positive, 2565).
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenating negative operands normalizes each one to its own width. *)
  Example concat_normalizes_negative_operands :
    eval_op bvconcat [(4%positive, -1); (8%positive, -2)] = Some (12%positive, 4094).
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenation of a four-bit 17 wraps to one before joining. *)
  Example concat_wraps_four_bit_operand :
    eval_op bvconcat [(4%positive, 17); (8%positive, 258)] = Some (12%positive, 258).
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenation of a four-bit 16 and an eight-bit 256 gives zero. *)
  Example concat_of_wrapped_zeros_is_zero :
    eval_op bvconcat [(4%positive, 16); (8%positive, 256)] = Some (12%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenating two one-bit ones gives three. *)
  Example width1_concat_of_ones :
    eval_op bvconcat [(1%positive, 1); (1%positive, 1)] = Some (2%positive, 3).
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenating two one-bit zeros gives zero. *)
  Example width1_concat_of_zeros :
    eval_op bvconcat [(1%positive, 0); (1%positive, 0)] = Some (2%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Addition of a negative and an above-modulus operand at width eight normalizes both. *)
  Example width8_add_normalizes_both_operands :
    eval_op bvadd [(8%positive, -1); (8%positive, 257)] = Some (8%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Left shift of one by one at width eight gives two. *)
  Example width8_shl_by_one :
    eval_op bvshl [(8%positive, 1); (8%positive, 1)] = Some (8%positive, 2).
  Proof. vm_compute. reflexivity. Qed.

  (** Addition of width-one operands wraps one plus three to zero. *)
  Example width1_add_wraps_to_zero :
    eval_op bvadd [(1%positive, -1); (1%positive, 3)] = Some (1%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

  (** A selection with a true width-one condition of three chooses the first branch. *)
  Example ite_wraps_condition_three_to_true :
    eval_op bvite [(1%positive, 3); (8%positive, -1); (8%positive, 257)] = Some (8%positive, 255).
  Proof. vm_compute. reflexivity. Qed.

  (** A selection with a two-valued width-one condition takes the else branch. *)
  Example ite_condition_two_takes_else :
    eval_op bvite [(1%positive, 2); (8%positive, -1); (8%positive, 257)] = Some (8%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

  (** A selection with width-one branches and a negative condition chooses the first branch. *)
  Example width1_ite_negative_condition_takes_then :
    eval_op bvite [(1%positive, -1); (1%positive, 3); (1%positive, 0)] = Some (1%positive, 1).
  Proof. vm_compute. reflexivity. Qed.

End WidthTests.

(** * Rejected operands *)

Module RejectionTests.

  (** An operator and the operands that it rejects. *)
  Definition rejected_case := (op * list word)%type.

  (** The result [None] marks a rejected operand list. *)
  Definition is_rejected (c : rejected_case) : bool :=
    match eval_op (fst c) (snd c) with
    | None => true
    | Some _ => false
    end.

  (** Operand lists of the wrong length, each with the operator that expects another count. *)
  Definition bad_arity_cases : list rejected_case :=
    [(bvzext 1%positive, []);
     (bvzext 1%positive, [(1%positive, -1); (1%positive, 2)]);
     (bvsext 1%positive, []);
     (bvsext 1%positive, [(1%positive, -1); (1%positive, 2)]);
     (bvtrunc 1%positive, []);
     (bvtrunc 1%positive, [(1%positive, -1); (1%positive, 2)]);
     (bvconcat, []);
     (bvconcat, [(1%positive, -1)]);
     (bvconcat, [(1%positive, -1); (1%positive, 2); (1%positive, 0)]);
     (bvnot, []);
     (bvnot, [(8%positive, 0); (8%positive, 0)])].

  (** Operands whose widths do not fit the operator. They cover unequal operand widths, a shift
      amount of another width, truncation to a wider width, extraction bounds that are reversed
      or beyond the word, and selections with a wide condition or unequal branches. *)
  Definition bad_width_cases : list rejected_case :=
    [(bvadd, [(8%positive, 0); (4%positive, 0)]);
     (bvadd, [(8%positive, -1); (4%positive, 257)]);
     (bvshl, [(8%positive, 1); (1%positive, 1)]);
     (bvtrunc 9%positive, [(8%positive, -1)]);
     (bvtrunc 9%positive, [(8%positive, 1)]);
     (bvextract 2 3, [(8%positive, 1)]);
     (bvextract 8 0, [(8%positive, 1)]);
     (bvite, [(2%positive, 1); (8%positive, 1); (8%positive, 2)]);
     (bvite, [(1%positive, 1); (8%positive, 1); (4%positive, 2)]);
     (bvite, [(1%positive, 1); (8%positive, 7); (4%positive, 7)]);
     (bvite, [(1%positive, 0); (8%positive, 7); (4%positive, 7)]);
     (bvite, [(2%positive, 1); (8%positive, 7); (8%positive, 7)]);
     (bvite, [(2%positive, 0); (8%positive, 7); (8%positive, 7)]);
     (bvite, [(2%positive, 1); (1%positive, 1); (1%positive, 0)])].

  (** Every operand list of the arity table is rejected. *)
  Example wrong_operand_counts_are_rejected : forallb is_rejected bad_arity_cases = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Every operand list of the width table is rejected. *)
  Example mismatched_widths_are_rejected : forallb is_rejected bad_width_cases = true.
  Proof. vm_compute. reflexivity. Qed.

End RejectionTests.

(** * Counts *)

Module CountTests.

  (** The leading-zero count of 40 at width eight is two. *)
  Example clz_of_40 : eval_op bvclz [(8%positive, 40)] = Some (8%positive, 2).
  Proof. vm_compute. reflexivity. Qed.

  (** The trailing-zero count of 40 at width eight is three. *)
  Example ctz_of_40 : eval_op bvctz [(8%positive, 40)] = Some (8%positive, 3).
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of 40 at width eight is two. *)
  Example popcount_of_40 : eval_op bvpopcnt [(8%positive, 40)] = Some (8%positive, 2).
  Proof. vm_compute. reflexivity. Qed.

  (** The leading-zero count of zero at width eight is eight. *)
  Example clz_of_zero_is_width : eval_op bvclz [(8%positive, 0)] = Some (8%positive, 8).
  Proof. vm_compute. reflexivity. Qed.

  (** The trailing-zero count of zero at width eight is eight. *)
  Example ctz_of_zero_is_width : eval_op bvctz [(8%positive, 0)] = Some (8%positive, 8).
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of zero at width eight is zero. *)
  Example popcount_of_zero_is_zero : eval_op bvpopcnt [(8%positive, 0)] = Some (8%positive, 0).
  Proof. vm_compute. reflexivity. Qed.

End CountTests.

(** * Fixtures *)

(** Representative operators, one for each constructor of the operator type. *)
Definition representative_ops : list op :=
  [bvnot; bvneg; bvclz; bvctz; bvpopcnt; bvadd; bvsub; bvmul; bvudiv; bvurem;
   bvsdiv; bvsrem; bvsmod; bvand; bvor; bvxor; bvshl; bvlshr; bvashr; bvrotl;
   bvrotr; bveq; bvne; bvult; bvule; bvslt; bvsle; bvite; bvzext 3%positive;
   bvsext 3%positive; bvtrunc 2%positive; bvextract 2 1; bvconcat].

(** * Codes *)

Module CodeTests.

  (** Two extractions with different low bounds have different encodings. *)
  Example extraction_bounds_change_code :
    Pos.eqb (snd (snd (op_code (bvextract 7 0)))) (snd (snd (op_code (bvextract 7 1)))) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero extension and sign extension have different tags. *)
  Example extension_kinds_have_different_tags :
    Nat.eqb (fst (op_code (bvzext 4%positive))) (fst (op_code (bvsext 4%positive))) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The representative operators have distinct constructor tags, numbered from zero. *)
  Example descriptor_codes_are_unique :
    map (fun o => fst (op_code o)) representative_ops = seq 0 33.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CodeTests.

(** * Symbolic *)

Module SymbolicTests.

  (** The concatenation of a word of width [wa] and a word of width [wb], then resized by [o]. *)
  Definition resize_concat (o : op) (wa wb : positive) (x y : Z) : option word :=
    match eval_op bvconcat [(wa, x); (wb, y)] with
    | Some r => eval_op o [r]
    | None => None
    end.

  (** The value of that concatenation, from the equations of the operators. *)
  Definition concat_value (wa wb : positive) (x y : Z) : Z :=
    wrap (wa + wb)%positive (wrap wa x * modulus wb + wrap wb y).

  (** Zero extension of a symbolic concatenation keeps its value in the wider word. *)
  Example zext_of_concat_symbolic : forall extra wa wb x y,
    resize_concat (bvzext extra) wa wb x y =
      Some ((wa + wb + extra)%positive,
            wrap (wa + wb + extra)%positive (wrap (wa + wb)%positive (concat_value wa wb x y))).
  Proof.
    intros extra wa wb x y.
    unfold resize_concat. rewrite eval_op_concat, eval_op_zext.
    reflexivity.
  Qed.

  (** Sign extension of a symbolic concatenation extends the signed value of the word. *)
  Example sext_of_concat_symbolic : forall extra wa wb x y,
    resize_concat (bvsext extra) wa wb x y =
      Some ((wa + wb + extra)%positive,
            wrap (wa + wb + extra)%positive (signed (wa + wb)%positive (concat_value wa wb x y))).
  Proof.
    intros extra wa wb x y.
    unfold resize_concat. rewrite eval_op_concat, eval_op_sext.
    reflexivity.
  Qed.

  (** Truncation of a symbolic concatenation succeeds exactly when the target is not wider. *)
  Example trunc_of_concat_symbolic : forall target wa wb x y,
    resize_concat (bvtrunc target) wa wb x y =
      if Pos.leb target (wa + wb)%positive
      then Some (target, wrap target (wrap (wa + wb)%positive (concat_value wa wb x y)))
      else None.
  Proof.
    intros target wa wb x y.
    unfold resize_concat. rewrite eval_op_concat, eval_op_trunc.
    reflexivity.
  Qed.

  (** A binary operator client recovers its value formula after inverting operand widths. *)
  Example fun2_width_symbolic_client : forall o f wa wb x y r,
    word_fun2 o = Some f -> eval_op o [(wa, x); (wb, y)] = Some r ->
    r = (wa, eval_binary_tag f wa x y).
  Proof.
    intros o f wa wb x y r Hfun Hresult.
    pose proof (eval_op_fun2_width o f wa wb x y r Hfun Hresult) as Hwidth.
    subst wb. rewrite (eval_op_fun2 o wa x y f Hfun) in Hresult.
    congruence.
  Qed.

  (** A comparison client recovers its boolean word after inverting operand widths. *)
  Example cmp_width_symbolic_client : forall o f wa wb x y r,
    word_cmp o = Some f -> eval_op o [(wa, x); (wb, y)] = Some r ->
    r = (1%positive, if eval_comparison_tag f wa x y then 1 else 0).
  Proof.
    intros o f wa wb x y r Hfun Hresult.
    pose proof (eval_op_cmp_width o f wa wb x y r Hfun Hresult) as Hwidth.
    subst wb. rewrite (eval_op_cmp o wa x y f Hfun) in Hresult.
    congruence.
  Qed.

  (** A selection client recovers its value formula after inverting all width checks. *)
  Example ite_width_symbolic_client : forall wc wa wb c x y r,
    eval_op bvite [(wc, c); (wa, x); (wb, y)] = Some r ->
    r = (wa, if wrap 1%positive c =? 1 then wrap wa x else wrap wa y).
  Proof.
    intros wc wa wb c x y r Hresult.
    destruct (eval_op_ite_width wc wa wb c x y r Hresult) as [Hcondition Hbranches].
    subst wc wb. rewrite eval_op_ite in Hresult.
    injection Hresult as Hvalue.
    symmetry. exact Hvalue.
  Qed.

End SymbolicTests.
