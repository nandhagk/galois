(** * Word operation examples

    These computations cover division, shifts and population counts at boundaries.
    For example, division by zero yields the all-ones word.
    Builds on: Fun.

    Groups:
    - [RawTests] Operations on raw sixty-four-bit operands that are out of range.
    - [ArithmeticTests] Addition, subtraction, multiplication and negation at boundaries.
    - [DivisionTests] Signed and unsigned division and residues, including zero divisors.
    - [ShiftTests] Left, logical and arithmetic shifts at and beyond the width.
    - [ComparisonTests] Unsigned and signed comparisons at boundaries.
    - [PopcountTests] Population counts, and the steps of the digit traversal.
    - [SymbolicTests] General facts about the operations, for any width. *)

From Stdlib Require Import ZArith.
From Galois.Bits Require Import Word Fun.

Open Scope Z_scope.

(** * Raw *)

Module RawTests.

  (** Adding a negative and an above-modulus sixty-four-bit operand gives the all-ones word. *)
  Example width64_add_normalizes_operands : wadd 64%positive (-1) (2 ^ 70) = 2 ^ 64 - 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Adding the same operands in the other order gives the same word. *)
  Example width64_add_order_does_not_matter : wadd 64%positive (2 ^ 70) (-1) = 2 ^ 64 - 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The all-ones word is not below zero. *)
  Example width64_all_ones_not_below_zero : wult 64%positive (-1) (2 ^ 70) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero is below the all-ones word. *)
  Example width64_zero_below_all_ones : wult 64%positive (2 ^ 70) (-1) = true.
  Proof. vm_compute. reflexivity. Qed.

End RawTests.

(** * Arithmetic *)

Module ArithmeticTests.

  (** Addition of ordinary eight-bit values gives their sum. *)
  Example width8_add_ordinary : wadd 8%positive 2 3 = 5.
  Proof. vm_compute. reflexivity. Qed.

  (** Addition wraps past the modulus. *)
  Example width8_add_wraps : wadd 8%positive 255 1 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Addition normalizes a negative and an above-modulus operand. *)
  Example width8_add_normalizes_operands : wadd 8%positive (-1) 258 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Subtraction of ordinary values gives their difference. *)
  Example width8_sub_ordinary : wsub 8%positive 5 3 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** Subtraction below zero wraps to 255. *)
  Example width8_sub_wraps_below_zero : wsub 8%positive 0 1 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Subtraction normalizes a negative and an above-modulus operand. *)
  Example width8_sub_normalizes_operands : wsub 8%positive (-1) 258 = 253.
  Proof. vm_compute. reflexivity. Qed.

  (** Multiplication of ordinary values gives their product. *)
  Example width8_mul_ordinary : wmul 8%positive 2 3 = 6.
  Proof. vm_compute. reflexivity. Qed.

  (** Multiplication wraps to zero when the product is a multiple of the modulus. *)
  Example width8_mul_wraps_to_zero : wmul 8%positive 128 2 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Multiplication normalizes a negative and an above-modulus operand. *)
  Example width8_mul_normalizes_operands : wmul 8%positive (-1) 258 = 254.
  Proof. vm_compute. reflexivity. Qed.

  (** Negation of one gives 255. *)
  Example width8_neg_one_is_255 : wneg 8%positive 1 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Negation of the minimum gives the minimum. *)
  Example width8_neg_minimum_is_minimum : wneg 8%positive 128 = 128.
  Proof. vm_compute. reflexivity. Qed.

  (** Negation normalizes a value below the minimum. *)
  Example width8_neg_below_minimum : wneg 8%positive (-257) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Negation of the modulus gives zero. *)
  Example width8_neg_modulus_is_zero : wneg 8%positive 256 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one addition wraps one plus one to zero. *)
  Example width1_add_wraps_to_zero : wadd 1%positive 1 1 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one subtraction gives one minus zero. *)
  Example width1_sub_is_one : wsub 1%positive 0 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one multiplication gives one times one. *)
  Example width1_mul_is_one : wmul 1%positive 1 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one negation of one gives one. *)
  Example width1_neg_one_is_one : wneg 1%positive 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

End ArithmeticTests.

(** * Division *)

Module DivisionTests.

  (** Signed division of positive values gives the truncated quotient. *)
  Example width8_sdiv_positive : wsdiv 8%positive 7 3 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative dividend and a positive divisor give a negative quotient. *)
  Example width8_sdiv_negative_dividend : wsdiv 8%positive (-7) 3 = 254.
  Proof. vm_compute. reflexivity. Qed.

  (** A positive dividend and a negative divisor give a negative quotient. *)
  Example width8_sdiv_negative_divisor : wsdiv 8%positive 7 (-3) = 254.
  Proof. vm_compute. reflexivity. Qed.

  (** Two negative operands give a positive quotient. *)
  Example width8_sdiv_both_negative : wsdiv 8%positive (-7) (-3) = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** Dividing the minimum by negative one overflows to the minimum. *)
  Example width8_sdiv_minimum_by_negative_one : wsdiv 8%positive 128 (-1) = 128.
  Proof. vm_compute. reflexivity. Qed.

  (** An above-modulus dividend and divisor are normalized before division. *)
  Example width8_sdiv_normalizes_operands : wsdiv 8%positive 263 256 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A divisor that normalizes to zero makes the signed quotient one. *)
  Example width8_sdiv_normalized_zero_divisor : wsdiv 8%positive (-7) 256 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed remainder of positive values gives the truncated remainder. *)
  Example width8_srem_positive : wsrem 8%positive 7 3 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative dividend gives a negative remainder. *)
  Example width8_srem_negative_dividend : wsrem 8%positive (-7) 3 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative divisor does not change the sign of the remainder. *)
  Example width8_srem_negative_divisor : wsrem 8%positive 7 (-3) = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Two negative operands give a negative remainder. *)
  Example width8_srem_both_negative : wsrem 8%positive (-7) (-3) = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** The remainder of the minimum divided by negative one is zero. *)
  Example width8_srem_minimum_by_negative_one : wsrem 8%positive 128 (-1) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A remainder with a normalized divisor of zero keeps the normalized dividend. *)
  Example width8_srem_normalized_zero_divisor : wsrem 8%positive (-7) 256 = 249.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed modulus of positive values gives the remainder. *)
  Example width8_smod_positive : wsmod 8%positive 7 3 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed modulus takes the sign of the divisor for a negative dividend. *)
  Example width8_smod_negative_dividend : wsmod 8%positive (-7) 3 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed modulus takes the sign of a negative divisor. *)
  Example width8_smod_negative_divisor : wsmod 8%positive 7 (-3) = 254.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed modulus of two negative operands is negative. *)
  Example width8_smod_both_negative : wsmod 8%positive (-7) (-3) = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative dividend that divides exactly has modulus zero. *)
  Example width8_smod_exact_negative_is_zero : wsmod 8%positive (-6) 3 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The modulus of the minimum divided by negative one is zero. *)
  Example width8_smod_minimum_by_negative_one : wsmod 8%positive 128 (-1) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An above-modulus dividend and divisor are normalized before the modulus. *)
  Example width8_smod_normalizes_operands : wsmod 8%positive 263 256 = 7.
  Proof. vm_compute. reflexivity. Qed.

  (** A normalized zero divisor leaves a normalized negative dividend as its modulus. *)
  Example width8_smod_normalized_zero_divisor : wsmod 8%positive (-7) 256 = 249.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one division of one by one gives one. *)
  Example width1_sdiv_one_by_one : wsdiv 1%positive 1 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one remainder of one by one is zero. *)
  Example width1_srem_one_by_one : wsrem 1%positive 1 1 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one modulus of one by one is zero. *)
  Example width1_smod_one_by_one : wsmod 1%positive 1 1 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned division by zero yields the all-ones word. *)
  Example width8_udiv_by_zero_is_all_ones : wudiv 8%positive 7 0 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed division by a zero divisor yields one. *)
  Example width8_sdiv_by_zero_is_one : wsdiv 8%positive 249 0 = 1.
  Proof. vm_compute. reflexivity. Qed.

End DivisionTests.

(** * Shifts *)

Module ShiftTests.

  (** Shifting left by zero keeps the word. *)
  Example width8_shl_by_zero : wshl 8%positive 129 0 = 129.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting left by seven keeps only the lowest bit. *)
  Example width8_shl_by_seven : wshl 8%positive 129 7 = 128.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting left by the width clears the word. *)
  Example width8_shl_by_width_clears : wshl 8%positive 129 8 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative shift amount normalizes to a large amount that clears the word. *)
  Example width8_shl_negative_amount_clears : wshl 8%positive (-1) (-1) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A shift amount of 256 normalizes to zero. *)
  Example width8_shl_by_256_is_no_shift : wshl 8%positive 257 256 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A shift amount of 257 normalizes to one. *)
  Example width8_shl_by_257_shifts_once : wshl 8%positive 257 257 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** Logical right shift by zero keeps the word. *)
  Example width8_lshr_by_zero : wlshr 8%positive 129 0 = 129.
  Proof. vm_compute. reflexivity. Qed.

  (** Logical right shift by seven keeps the top bit as one. *)
  Example width8_lshr_by_seven : wlshr 8%positive 129 7 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Logical right shift by the width clears the word. *)
  Example width8_lshr_by_width_clears : wlshr 8%positive 129 8 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative logical shift amount normalizes to a clearing amount. *)
  Example width8_lshr_negative_amount_clears : wlshr 8%positive (-1) (-1) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical shift by 256 normalizes to zero. *)
  Example width8_lshr_by_256_is_no_shift : wlshr 8%positive 257 256 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical shift by 257 normalizes to one. *)
  Example width8_lshr_by_257_shifts_once : wlshr 8%positive 258 257 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic right shift by zero keeps the negative word. *)
  Example width8_ashr_by_zero_keeps_negative : washr 8%positive (-127) 0 = 129.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic right shift by seven fills the word with the sign bit. *)
  Example width8_ashr_by_seven_fills_sign : washr 8%positive (-127) 7 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic right shift by the width fills a negative word with the sign bit. *)
  Example width8_ashr_by_width_fills_sign : washr 8%positive (-127) 8 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic right shift by the width clears a positive word. *)
  Example width8_ashr_by_width_clears_positive : washr 8%positive 127 8 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative arithmetic shift amount normalizes to a sign-filling amount. *)
  Example width8_ashr_negative_amount_fills_sign : washr 8%positive (-1) (-1) = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A positive word shifted by a negative amount normalizes to a clearing amount. *)
  Example width8_ashr_positive_negative_amount_clears : washr 8%positive 127 (-1) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic shift by 256 normalizes to zero. *)
  Example width8_ashr_by_256_is_no_shift : washr 8%positive 384 256 = 128.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic shift by 257 normalizes to one. *)
  Example width8_ashr_by_257_shifts_once : washr 8%positive 384 257 = 192.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one left shift by one clears the word. *)
  Example width1_shl_by_one_clears : wshl 1%positive 1 1 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one logical right shift by one clears the word. *)
  Example width1_lshr_by_one_clears : wlshr 1%positive 1 1 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one arithmetic right shift by one keeps the word. *)
  Example width1_ashr_by_one_keeps_word : washr 1%positive 1 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A shift by the width or more with a symbolic amount is checked in the symbolic tests. *)
  Example shift_by_amounts_over_width_fill_or_clear :
    wshl 8%positive 129 8 = 0 /\ wlshr 8%positive 129 8 = 0.
  Proof. vm_compute. repeat split. Qed.

End ShiftTests.

(** * Comparisons *)

Module ComparisonTests.

  (** Unsigned less-than orders one below two. *)
  Example width8_ult_ordinary : wult 8%positive 1 2 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned less-than normalizes negative one to 255, which is not below zero. *)
  Example width8_ult_negative_one_not_below_zero : wult 8%positive (-1) 0 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned less-than normalizes above-modulus operands before comparing. *)
  Example width8_ult_normalizes_above_modulus : wult 8%positive 256 257 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned 255 is not below negative one, which normalizes to 255. *)
  Example width8_ult_255_not_below_negative_one : wult 8%positive 255 (-1) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned less-or-equal orders one below two. *)
  Example width8_ule_ordinary : wule 8%positive 1 2 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned less-or-equal rejects negative one against zero. *)
  Example width8_ule_negative_one_not_below_zero : wule 8%positive (-1) 0 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned 255 is at most negative one, which normalizes to 255. *)
  Example width8_ule_255_at_most_negative_one : wule 8%positive 255 (-1) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned 256 normalizes to zero, which is at most zero. *)
  Example width8_ule_256_at_most_zero : wule 8%positive 256 0 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed less-than puts negative one below zero. *)
  Example width8_slt_negative_below_zero : wslt 8%positive (-1) 0 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed less-than puts 127 above the minimum 128. *)
  Example width8_slt_127_not_below_minimum : wslt 8%positive 127 128 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed less-than normalizes an above-modulus operand before comparing. *)
  Example width8_slt_normalizes_above_modulus : wslt 8%positive 384 127 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed 255 is not below signed negative one. *)
  Example width8_slt_255_not_below_negative_one : wslt 8%positive 255 (-1) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed less-or-equal puts negative one at or below zero. *)
  Example width8_sle_negative_at_most_zero : wsle 8%positive (-1) 0 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed less-or-equal puts 127 above the minimum 128. *)
  Example width8_sle_127_not_at_most_minimum : wsle 8%positive 127 128 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed 255 is at most signed negative one. *)
  Example width8_sle_255_at_most_negative_one : wsle 8%positive 255 (-1) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed 256 normalizes to zero, which is at most zero. *)
  Example width8_sle_256_at_most_zero : wsle 8%positive 256 0 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one unsigned order puts zero below one. *)
  Example width1_ult_zero_below_one : wult 1%positive 0 1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one unsigned order makes one at most one. *)
  Example width1_ule_one_at_most_one : wule 1%positive 1 1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one signed order puts one below zero. *)
  Example width1_slt_one_below_zero : wslt 1%positive 1 0 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Width one signed order makes one at most one. *)
  Example width1_sle_one_at_most_one : wsle 1%positive 1 1 = true.
  Proof. vm_compute. reflexivity. Qed.

End ComparisonTests.

(** * Population count *)

Module PopcountTests.

  (** Population count of zero at width one is zero. *)
  Example width1_zero_has_no_bits : wpopcnt 1%positive 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of 257 at width eight is one, after normalization. *)
  Example width8_257_has_one_bit : wpopcnt 8%positive 257 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of all-ones at width sixty-four is sixty-four. *)
  Example width64_all_ones_has_64_bits : wpopcnt 64%positive (2 ^ 64 - 1) = 64.
  Proof. vm_compute. reflexivity. Qed.

  (** Population count of the one-bit word one is one. *)
  Example width1_one_has_one_bit : wpopcnt 1%positive 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The word two at width one normalizes to zero, which has no bits. *)
  Example width1_two_normalizes_to_no_bits : wpopcnt 1%positive 2 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Population count of negative one at width eight is eight. *)
  Example width8_negative_one_has_eight_bits : wpopcnt 8%positive (-1) = 8.
  Proof. vm_compute. reflexivity. Qed.

  (** The raw popcount of negative one is zero. *)
  Example raw_popcount_of_negative_one_is_zero : popcount (-1) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The raw popcount of zero is zero. *)
  Example raw_popcount_of_zero_is_zero : popcount 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Population count of two to the sixty-fourth at width sixty-four is zero. *)
  Example width64_power_of_two_has_no_bits : wpopcnt 64%positive (2 ^ 64) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The digit traversal of one takes one step. *)
  Example popcount_one_takes_one_step : popcount_steps_pos 1%positive = 1%nat.
  Proof. vm_compute. reflexivity. Qed.

  (** The digit traversal of 255 takes eight steps. *)
  Example popcount_255_takes_eight_steps : popcount_steps_pos 255%positive = 8%nat.
  Proof. vm_compute. reflexivity. Qed.

  (** The digit traversal of 256 takes nine steps. *)
  Example popcount_256_takes_nine_steps : popcount_steps_pos 256%positive = 9%nat.
  Proof. vm_compute. reflexivity. Qed.

End PopcountTests.

(** * Operation boundaries *)

Module OperationTests.

  (** Unsigned division by zero yields the all-ones word at width eight. *)
  Example unsigned_division_by_zero_is_all_ones : wudiv 8%positive 7 0 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed division by zero yields one at width eight. *)
  Example signed_division_by_zero_is_one : wsdiv 8%positive 249 0 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Left shift by the width clears the word. *)
  Example shl_by_width_clears_word : wshl 8%positive 129 8 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic right shift by the width fills the word with the sign bit. *)
  Example ashr_by_width_fills_with_sign : washr 8%positive 129 8 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Population count of one at width one is one. *)
  Example width1_popcount_of_one : wpopcnt 1%positive 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Population count of 257 at width eight is one. *)
  Example width8_popcount_of_257 : wpopcnt 8%positive 257 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Population count of all-ones at width sixty-four is sixty-four. *)
  Example width64_popcount_of_all_ones : wpopcnt 64%positive (2 ^ 64 - 1) = 64.
  Proof. vm_compute. reflexivity. Qed.

End OperationTests.

(** * Width one *)

Module WidthOneTests.

  (** Bitwise not of one at width one is zero. *)
  Example width1_not_one_is_zero : wnot 1%positive 1 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Negation of one at width one is one. *)
  Example width1_neg_one_is_one : wneg 1%positive 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The signed value of the word one at width one is negative one. *)
  Example width1_one_signed_is_negative_one : signed 1%positive 1 = -1.
  Proof. vm_compute. reflexivity. Qed.

  (** Count of leading zeros of zero at width one is one. *)
  Example width1_clz_of_zero_is_one : wclz 1%positive 0 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Count of trailing zeros of one at width one is zero. *)
  Example width1_ctz_of_one_is_zero : wctz 1%positive 1 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Population count of one at width one is one. *)
  Example width1_popcount_of_one_is_one : wpopcnt 1%positive 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

End WidthOneTests.

(** * Symbolic *)

Module SymbolicTests.

  (** Adding a difference and a product gives the same word as the reduced sum of values. *)
  Example arithmetic_value_symbolic_client : forall w x y,
    wadd w (wsub w x y) (wmul w (wneg w x) y) =
      wrap w (wrap w (x - y) + wrap w (wrap w (- x) * y)).
  Proof.
    intros w x y.
    rewrite wadd_value, wsub_value, wmul_value, wneg_value.
    reflexivity.
  Qed.

  (** Signed division and remainder of two negative words use their magnitudes. *)
  Example signed_division_value_symbolic_client : forall w x y,
    msb w x = true -> msb w y = true ->
    (wsdiv w x y, wsrem w x y) =
      (wudiv w (wneg w x) (wneg w y), wneg w (wurem w (wneg w x) (wneg w y))).
  Proof.
    intros w x y Hx Hy.
    rewrite wsdiv_value, wsrem_value, Hx, Hy.
    reflexivity.
  Qed.

  (** A zero residue of two negative words gives a zero signed modulus. *)
  Example signed_modulus_value_symbolic_client : forall w x y,
    msb w x = true -> msb w y = true ->
    wurem w (wneg w x) (wneg w y) = 0 -> wsmod w x y = 0.
  Proof.
    intros w x y Hx Hy Hrem.
    rewrite wsmod_value, Hx, Hy.
    cbn beta iota zeta.
    rewrite Hrem.
    reflexivity.
  Qed.

  (** A shift by a width or more clears left and logical shifts and sign-fills arithmetic shifts. *)
  Example shift_value_symbolic_client : forall w x y,
    (Zpos w <=? wrap w y) = true ->
    (wshl w x y, wlshr w x y, washr w x y) =
      (0, 0, if msb w x then modulus w - 1 else 0).
  Proof.
    intros w x y Hlarge.
    rewrite wshl_value, wlshr_value, washr_value, Hlarge.
    reflexivity.
  Qed.

  (** Unsigned and signed comparisons are the comparisons of their value equations. *)
  Example comparison_value_symbolic_client : forall w x y,
    (wult w x y, wule w x y, wslt w x y, wsle w x y) =
      (wrap w x <? wrap w y, wrap w x <=? wrap w y,
       signed w x <? signed w y, signed w x <=? signed w y).
  Proof.
    intros w x y.
    rewrite wult_value, wule_value, wslt_value, wsle_value.
    reflexivity.
  Qed.

End SymbolicTests.
