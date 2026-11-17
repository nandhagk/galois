(** * Arithmetic and testbit boundary examples

    Integer observations exercise total division, signed endpoints, counts and rotations.
    For example, signed remainder and signed modulus differ on operands of opposite signs.
    Builds on: Word, Fun, Testbit and Arith.

    Groups:
    - SignedTests: signed endpoints at width one and width eight.
    - DivisionTests: division and remainders, with overflow and zero divisors.
    - ArithmeticTests: products and powers of two.
    - ComparisonTests: the sign bit as a bias for comparisons.
    - ShiftTests: shifts beyond the width.
    - RotationTests: rotations with cyclic amounts.
    - CountTests: leading zeros, trailing zeros and population counts.
    - BitwiseTests: truth tables and testbit observations. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Fun Testbit Arith.
Import List.ListNotations.

Open Scope Z_scope.

(** * Signed *)

Module SignedTests.

  (** The sign bit at width eight is the minimum, negative 128. *)
  Example width8_sign_bit_is_minimum : signed 8%positive 128 = -128.
  Proof. vm_compute. reflexivity. Qed.

  (** The largest positive eight-bit value is 127. *)
  Example width8_largest_positive_is_127 : signed 8%positive 127 = 127.
  Proof. vm_compute. reflexivity. Qed.

  (** The word one at width one is negative one. *)
  Example width1_one_is_negative_one : signed 1%positive 1 = -1.
  Proof. vm_compute. reflexivity. Qed.

  (** The word zero at width one is zero. *)
  Example width1_zero_is_zero : signed 1%positive 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

End SignedTests.

(** * Division *)

Module DivisionTests.

  (** Dividing the signed minimum by negative one overflows to the minimum. *)
  Example minimum_divided_by_negative_one_is_minimum : wsdiv 8%positive 128 255 = 128.
  Proof. vm_compute. reflexivity. Qed.

  (** The remainder of the signed minimum divided by negative one is zero. *)
  Example minimum_remainder_by_negative_one_is_zero : wsrem 8%positive 128 255 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative dividend gives a quotient of 254 with a positive divisor. *)
  Example negative_dividend_quotient : wsdiv 8%positive 249 3 = 254.
  Proof. vm_compute. reflexivity. Qed.

  (** A positive dividend gives a quotient of 254 with a negative divisor. *)
  Example negative_divisor_quotient : wsdiv 8%positive 7 253 = 254.
  Proof. vm_compute. reflexivity. Qed.

  (** Two negative operands give a quotient of two. *)
  Example both_negative_quotient : wsdiv 8%positive 249 253 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative dividend gives a remainder of 255. *)
  Example negative_dividend_remainder : wsrem 8%positive 249 3 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative divisor does not change the sign of a positive remainder. *)
  Example negative_divisor_remainder : wsrem 8%positive 7 253 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Two negative operands give a remainder of 255. *)
  Example both_negative_remainder : wsrem 8%positive 249 253 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative dividend gives a modulus of two with a positive divisor. *)
  Example negative_dividend_modulus : wsmod 8%positive 249 3 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative divisor gives a modulus of 254. *)
  Example negative_divisor_modulus : wsmod 8%positive 7 253 = 254.
  Proof. vm_compute. reflexivity. Qed.

  (** Two negative operands give a modulus of 255. *)
  Example both_negative_modulus : wsmod 8%positive 249 253 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned division by zero yields the all-ones word. *)
  Example unsigned_division_by_zero : wudiv 8%positive 7 0 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Unsigned remainder by zero yields the dividend. *)
  Example unsigned_remainder_by_zero : wurem 8%positive 7 0 = 7.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed division by zero yields one for a negative dividend. *)
  Example signed_division_by_zero : wsdiv 8%positive 249 0 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed division by zero for a positive dividend yields all-ones. *)
  Example signed_division_by_zero_positive : wsdiv 8%positive 7 0 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed remainder by zero yields the dividend. *)
  Example signed_remainder_by_zero : wsrem 8%positive 249 0 = 249.
  Proof. vm_compute. reflexivity. Qed.

  (** Signed modulus by zero yields the dividend. *)
  Example signed_modulus_by_zero : wsmod 8%positive 249 0 = 249.
  Proof. vm_compute. reflexivity. Qed.

  (** An above-modulus divisor normalizes to zero, so unsigned division yields all-ones. *)
  Example unsigned_division_by_normalized_zero : wudiv 8%positive 7 256 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** An above-modulus divisor normalizes to zero, so signed modulus keeps the dividend. *)
  Example signed_modulus_by_normalized_zero : wsmod 8%positive 249 256 = 249.
  Proof. vm_compute. reflexivity. Qed.

  (** The negative dividend negative six is a multiple of three, so its modulus is zero. *)
  Example exact_division_modulus_is_zero : wsmod 8%positive 250 3 = 0.
  Proof. vm_compute. reflexivity. Qed.

End DivisionTests.

(** * Arithmetic *)

Module ArithmeticTests.

  (** Multiplying by a power of two at width eight gives the same result as a shift. *)
  Example power_of_two_multiplication : wmul 8%positive 173 8 = 104.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting left by three gives the product with eight. *)
  Example power_of_two_shift_left : wshl 8%positive 173 3 = 104.
  Proof. vm_compute. reflexivity. Qed.

  (** Dividing by eight gives the quotient that a logical shift gives. *)
  Example power_of_two_unsigned_division : wudiv 8%positive 173 8 = 21.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting right by three gives the same quotient as division by eight. *)
  Example power_of_two_logical_shift_right : wlshr 8%positive 173 3 = 21.
  Proof. vm_compute. reflexivity. Qed.

  (** The unsigned remainder by eight is the low three bits. *)
  Example power_of_two_unsigned_remainder : wurem 8%positive 173 8 = 5.
  Proof. vm_compute. reflexivity. Qed.

  (** Masking with seven keeps the low three bits. *)
  Example power_of_two_mask : wand 8%positive 173 7 = 5.
  Proof. vm_compute. reflexivity. Qed.

End ArithmeticTests.

(** * Comparison *)

Module ComparisonTests.

  (** Signed less-than puts 255 below one, because 255 is negative one. *)
  Example signed_order_puts_all_ones_below_one : wslt 8%positive 255 1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Flipping the sign bit turns the signed comparison into an unsigned one. *)
  Example sign_bit_flip_biases_comparison :
    wult 8%positive (wxor 8%positive 255 128) (wxor 8%positive 1 128) = true.
  Proof. vm_compute. reflexivity. Qed.

End ComparisonTests.

(** * Shifts *)

Module ShiftTests.

  (** Shifting left by eight clears the word. *)
  Example shift_left_by_width_clears : wshl 8%positive 129 8 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Logical shift right by eight clears the word. *)
  Example shift_right_by_width_clears : wlshr 8%positive 129 8 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic shift right by eight fills a negative word with the sign bit. *)
  Example arithmetic_shift_by_width_fills_sign : washr 8%positive 129 8 = 255.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic shift of a positive word by 255 gives zero. *)
  Example arithmetic_shift_positive_by_large_amount : washr 8%positive 127 255 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic shift right by one keeps the sign and the high bit. *)
  Example arithmetic_shift_by_one_keeps_sign : washr 8%positive 129 1 = 192.
  Proof. vm_compute. reflexivity. Qed.

  (** A shift amount of 256 normalizes to zero, so the shift changes nothing. *)
  Example shift_by_256_is_no_shift : wshl 8%positive 129 256 = 129.
  Proof. vm_compute. reflexivity. Qed.

End ShiftTests.

(** * Rotation *)

Module RotationTests.

  (** Rotating left by zero keeps the word. *)
  Example rotate_left_by_zero : wrotl 8%positive 129 0 = 129.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating left by one moves the top bit to the bottom. *)
  Example rotate_left_by_one : wrotl 8%positive 129 1 = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating left by the width keeps the word. *)
  Example rotate_left_by_width_keeps_word : wrotl 8%positive 129 8 = 129.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating left by 17 is rotating left by one, because the amount is cyclic. *)
  Example rotate_left_by_cyclic_amount : wrotl 8%positive 129 17 = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating right by 17 undoes rotating left by one. *)
  Example rotate_right_by_cyclic_amount : wrotr 8%positive 3 17 = 129.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating right by one moves the bottom bit to the top. *)
  Example rotate_right_by_one : wrotr 8%positive 129 1 = 192.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating left by four at width three wraps the bits around. *)
  Example rotate_left_width3_by_four : wrotl 3%positive 5 4 = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating right by four at width three wraps the bits around. *)
  Example rotate_right_width3_by_four : wrotr 3%positive 5 4 = 6.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating left by two at width three is rotating right by one. *)
  Example rotate_left_width3_by_two : wrotl 3%positive 5 2 = 6.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating right by two at width three undoes rotating left by two. *)
  Example rotate_right_width3_by_two : wrotr 3%positive 6 2 = 5.
  Proof. vm_compute. reflexivity. Qed.

End RotationTests.

(** * Counts *)

Module CountTests.

  (** The leading-zero count of zero is the width. *)
  Example zero_leading_zeros_is_width : wclz 8%positive 0 = 8.
  Proof. vm_compute. reflexivity. Qed.

  (** The trailing-zero count of zero is the width. *)
  Example zero_trailing_zeros_is_width : wctz 8%positive 0 = 8.
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of zero is zero. *)
  Example zero_population_is_zero : wpopcnt 8%positive 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The leading-zero count of 24 is three. *)
  Example leading_zeros_of_24 : wclz 8%positive 24 = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The trailing-zero count of 24 is three. *)
  Example trailing_zeros_of_24 : wctz 8%positive 24 = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of 24 is two. *)
  Example population_of_24 : wpopcnt 8%positive 24 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** The population count of the bitwise complement of 24 is six. *)
  Example population_of_complement_of_24 : wpopcnt 8%positive (wnot 8%positive 24) = 6.
  Proof. vm_compute. reflexivity. Qed.

  (** The trailing-zero count of the sign bit is seven. *)
  Example trailing_zeros_of_sign_bit : wctz 8%positive 128 = 7.
  Proof. vm_compute. reflexivity. Qed.

End CountTests.

(** * Bitwise *)

Module BitwiseTests.

  (** Bitwise and of 170 and 204 is 136. *)
  Example bitwise_and_truth_table : wand 8%positive 170 204 = 136.
  Proof. vm_compute. reflexivity. Qed.

  (** Bitwise or of 170 and 204 is 238. *)
  Example bitwise_or_truth_table : wor 8%positive 170 204 = 238.
  Proof. vm_compute. reflexivity. Qed.

  (** Bitwise exclusive or of 170 and 204 is 102. *)
  Example bitwise_xor_truth_table : wxor 8%positive 170 204 = 102.
  Proof. vm_compute. reflexivity. Qed.

  (** Bitwise not of 170 is 85. *)
  Example bitwise_not_truth_table : wnot 8%positive 170 = 85.
  Proof. vm_compute. reflexivity. Qed.

  (** Arithmetic shift right by two keeps bit seven set. *)
  Example testbit_after_arithmetic_shift : Z.testbit (washr 8%positive 129 2) 7 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting left past the width clears bit eight. *)
  Example testbit_beyond_width_is_clear : Z.testbit (wshl 8%positive 129 2) 8 = false.
  Proof. vm_compute. reflexivity. Qed.

End BitwiseTests.
