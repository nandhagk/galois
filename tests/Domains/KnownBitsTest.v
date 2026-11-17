(** * Known-bit mask and carry fixtures

    These examples check normalized masks, contradictory facts and closed-form arithmetic.
    For example, seven or fifteen plus one exposes uncertainty in the fourth and fifth bits.

    Groups:
    - [MaskTests] Order, equivalence and widening of raw masks.
    - [CarryTests] Addition, subtraction, negation and division with carries and borrows.
    - [ShiftTests] Variable shifts by unknown, constant, odd and conflicting amounts.
    - [RotationTests] Variable rotations by the same kinds of amount.
    - [FlatTests] Prepared xor, negation, addition, subtraction and carry operations.
    - [SpecificationTests] The masked operations agree with the reference operations.

    Builds on: DomainsTnum and DomainsTnumArith. *)

From Stdlib Require Import ZArith Bool List.
From Galois.Domains Require Import KnownBitsSig KnownBits BitsLang.
Import List.ListNotations.

Local Open Scope Z_scope.

(** * Fixtures *)

(** The low multiplier configuration used by the mask module. *)
Module LowMultiplier <: TNUM_CONFIG.
  Definition multiplier := MulLow.
End LowMultiplier.

(** The known-bit masks over the word language, with the low multiplier. *)
Module MaskCode := KnownBitsCode WordLanguageCode LowMultiplier.

(** * Masks *)

Module MaskTests.

  (** A mask with an oversized zero part is below the normal mask it reduces to. *)
  Example oversized_mask_below_normal :
    tnum_leb 8%positive (Tnum (-16) 257) (Tnum 240 1) = true.
  Proof. vm_compute. auto. Qed.

  (** The normal mask is below the oversized mask it reduces to. *)
  Example normal_mask_below_oversized :
    tnum_leb 8%positive (Tnum 240 1) (Tnum (-16) 257) = true.
  Proof. vm_compute. auto. Qed.

  (** A mask whose only known bit lies beyond the width is below top. *)
  Example out_of_width_mask_below_top :
    tnum_leb 4%positive (Tnum 16 0) tnum_top = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Top is below a mask whose only known bit lies beyond the width. *)
  Example top_below_out_of_width_mask :
    tnum_leb 4%positive tnum_top (Tnum 16 0) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Equivalent raw masks are different records, so they are not equal. *)
  Example raw_equivalence_is_not_record_equality :
    Tnum 16 0 <> tnum_top.
  Proof. vm_compute. intro H. discriminate. Qed.

  (** A conflicting bit is not in the concretization at width eight. *)
  Example conflicting_bit_not_in_gamma : ~ tnum_gamma 8%positive (Tnum 1 1) 0.
  Proof.
    vm_compute. intros [_ Hbad]. discriminate.
  Qed.

  (** The contradictory mask is below any other mask at width two. *)
  Example contradictory_mask_is_least :
    MaskCode.pleb 2%positive (Tnum 1 1) (Tnum 2 0) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Widening a raw mask by top keeps the raw mask. *)
  Example widen_keeps_raw_mask :
    MaskCode.pwiden tt 4%positive (Tnum 16 0) (Tnum 0 0) = Tnum 16 0.
  Proof. vm_compute. reflexivity. Qed.

End MaskTests.

(** * Carries *)

Module CarryTests.

  (** Adding one to seven or fifteen leaves the fourth and fifth bits unknown. *)
  Example carry_propagation :
    tnum_add 8%positive (Tnum 240 7) (tnum_const 8%positive 1) = Tnum 231 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Subtracting one from eight or nine leaves the low four bits unknown. *)
  Example borrow_propagation :
    tnum_sub 8%positive (Tnum 246 8) (tnum_const 8%positive 1) = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Negating the one-bit constant one gives the constant one. *)
  Example one_bit_negation :
    tnum_neg 1%positive (tnum_const 1%positive 1) = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The mask addition matches the Linux-style addition on the carry fixture. *)
  Example matches_linux_add :
    tnum_add 8%positive (Tnum 240 7) (tnum_const 8%positive 1) =
      tnum_linux_add 8%positive (Tnum 240 7) (tnum_const 8%positive 1).
  Proof. vm_compute. reflexivity. Qed.

  (** Dividing by a known zero gives the top mask. *)
  Example udiv_by_zero_is_top :
    tnum_udiv 8%positive (Tnum 240 0) (tnum_const 8%positive 0) = tnum_top.
  Proof. vm_compute. auto. Qed.

  (** Dividing a value below sixteen by an odd divisor gives a value below sixteen. *)
  Example udiv_by_one_bit_mask :
    tnum_udiv 8%positive (Tnum 240 0) (Tnum 0 1) = Tnum 240 0.
  Proof. vm_compute. auto. Qed.

  (** The unsigned remainder of a value below sixteen stays below sixteen. *)
  Example urem_keeps_mask :
    tnum_urem 8%positive (Tnum 240 0) = Tnum 240 0.
  Proof. vm_compute. auto. Qed.

End CarryTests.

(** * Shifts *)

Module ShiftTests.

  (** A left shift of the constant 15 by an unknown amount is unknown at width eight. *)
  Example shl_unknown_amount_8 :
    MaskCode.tnum_variable Op.bvshl 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical right shift of the constant 15 by an unknown amount keeps the high nibble zero. *)
  Example lshr_unknown_amount_8 :
    MaskCode.tnum_variable Op.bvlshr 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift of the constant 15 by an unknown amount keeps the nibble zero. *)
  Example ashr_unknown_amount_8 :
    MaskCode.tnum_variable Op.bvashr 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift of a value by an unknown amount is unknown at width sixty-four. *)
  Example shl_unknown_amount_64 :
    MaskCode.tnum_variable Op.bvshl 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical right shift by an unknown amount is unknown at width sixty-four. *)
  Example lshr_unknown_amount_64 :
    MaskCode.tnum_variable Op.bvlshr 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift by an unknown amount is unknown at width sixty-four. *)
  Example ashr_unknown_amount_64 :
    MaskCode.tnum_variable Op.bvashr 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting the constant 15 left by one at width eight gives the constant 30. *)
  Example shl_one_bit_8 :
    MaskCode.tnum_variable Op.bvshl 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
      Tnum 225 30.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting the constant 15 right by one at width eight gives the constant 7. *)
  Example lshr_one_bit_8 :
    MaskCode.tnum_variable Op.bvlshr 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
      Tnum 248 7.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting the constant 15 arithmetically right by one at width eight gives the constant 7. *)
  Example ashr_one_bit_8 :
    MaskCode.tnum_variable Op.bvashr 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
      Tnum 248 7.
  Proof. vm_compute. reflexivity. Qed.

  (** Shifting left by one at width sixty-four knows bits 0 to 8 and no higher bit. *)
  Example shl_one_bit_64 :
    MaskCode.tnum_variable Op.bvshl 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
      Tnum 481 30.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical right shift by one at width sixty-four makes the top bit known zero. *)
  Example lshr_one_bit_64 :
    MaskCode.tnum_variable Op.bvlshr 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
      Tnum (2 ^ 63 + 120) 7.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift by one at width sixty-four leaves the top bit unknown. *)
  Example ashr_one_bit_64 :
    MaskCode.tnum_variable Op.bvashr 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
      Tnum 120 7.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift by an odd amount below eight leaves only the low bit known zero. *)
  Example shl_odd_amount_8 :
    MaskCode.tnum_variable Op.bvshl 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 1 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical right shift by an odd amount below eight keeps the high five bits zero. *)
  Example lshr_odd_amount_8 :
    MaskCode.tnum_variable Op.bvlshr 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 248 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift by an odd amount below eight keeps the high five bits zero. *)
  Example ashr_odd_amount_8 :
    MaskCode.tnum_variable Op.bvashr 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 248 0.
  Proof. vm_compute. reflexivity. Qed.

  (** At width sixty-four, a left shift by an odd amount below eight knows only the low bit. *)
  Example shl_odd_amount_64 :
    MaskCode.tnum_variable Op.bvshl 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum 1 0.
  Proof. vm_compute. reflexivity. Qed.

  (** At width sixty-four, a right shift by an odd amount below eight zeroes the top bit. *)
  Example lshr_odd_amount_64 :
    MaskCode.tnum_variable Op.bvlshr 64%positive (Tnum 240 15) (Tnum 248 1) =
      Tnum (2 ^ 63) 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift by an odd amount below eight is unknown at width sixty-four. *)
  Example ashr_odd_amount_64 :
    MaskCode.tnum_variable Op.bvashr 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift of the one-bit constant one by an unknown amount is unknown. *)
  Example shl_width_one_unknown_amount :
    MaskCode.tnum_variable Op.bvshl 1%positive (Tnum 0 1) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift of a mask with conflicting bits by an unknown amount conflicts in every bit. *)
  Example shl_conflicting_mask_unknown_amount :
    MaskCode.tnum_variable Op.bvshl 8%positive (Tnum 7 7) (Tnum 0 0) = Tnum 255 255.
  Proof. vm_compute. reflexivity. Qed.

  (** A logical right shift by an amount with conflicting bits conflicts in every bit. *)
  Example lshr_by_conflicting_amount :
    MaskCode.tnum_variable Op.bvlshr 8%positive (Tnum 0 0) (Tnum 7 7) = Tnum 255 255.
  Proof. vm_compute. reflexivity. Qed.

End ShiftTests.

(** * Rotations *)

Module RotationTests.

  (** A left rotation of the constant 15 by an unknown amount is unknown at width eight. *)
  Example rotl_unknown_amount_8 :
    MaskCode.tnum_variable Op.bvrotl 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation of the constant 15 by an unknown amount is unknown at width eight. *)
  Example rotr_unknown_amount_8 :
    MaskCode.tnum_variable Op.bvrotr 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation by an unknown amount is unknown at width sixty-four. *)
  Example rotl_unknown_amount_64 :
    MaskCode.tnum_variable Op.bvrotl 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation by an unknown amount is unknown at width sixty-four. *)
  Example rotr_unknown_amount_64 :
    MaskCode.tnum_variable Op.bvrotr 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating the constant 15 left by one at width eight gives the constant 30. *)
  Example rotl_one_bit_8 :
    MaskCode.tnum_variable Op.bvrotl 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
      Tnum 225 30.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating the constant 15 right by one at width eight gives the constant 135. *)
  Example rotr_one_bit_8 :
    MaskCode.tnum_variable Op.bvrotr 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
      Tnum 120 135.
  Proof. vm_compute. reflexivity. Qed.

  (** Rotating left by one at width sixty-four leaves bit 0 unknown, as it comes from the top. *)
  Example rotl_one_bit_64 :
    MaskCode.tnum_variable Op.bvrotl 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
      Tnum 480 30.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation by one at width sixty-four wraps the low bit to the top. *)
  Example rotr_one_bit_64 :
    MaskCode.tnum_variable Op.bvrotr 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
      Tnum 120 (2 ^ 63 + 7).
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation of the constant 15 by an odd amount below eight is unknown at width eight. *)
  Example rotl_odd_amount_8 :
    MaskCode.tnum_variable Op.bvrotl 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation of the constant 15 by an odd amount below eight is unknown at width eight. *)
  Example rotr_odd_amount_8 :
    MaskCode.tnum_variable Op.bvrotr 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation by an odd amount below eight is unknown at width sixty-four. *)
  Example rotl_odd_amount_64 :
    MaskCode.tnum_variable Op.bvrotl 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation by an odd amount below eight is unknown at width sixty-four. *)
  Example rotr_odd_amount_64 :
    MaskCode.tnum_variable Op.bvrotr 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation at width one keeps the constant one. *)
  Example rotl_width_one :
    MaskCode.tnum_variable Op.bvrotl 1%positive (Tnum 0 1) (Tnum 0 0) = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation at width one keeps the constant one. *)
  Example rotr_width_one :
    MaskCode.tnum_variable Op.bvrotr 1%positive (Tnum 0 1) (Tnum 0 0) = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** At width seven, no power of two, a left rotation by an unknown amount is unknown. *)
  Example rotl_width_seven :
    MaskCode.tnum_variable Op.bvrotl 7%positive (Tnum 112 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** At width seven, no power of two, a right rotation by an unknown amount is unknown. *)
  Example rotr_width_seven :
    MaskCode.tnum_variable Op.bvrotr 7%positive (Tnum 112 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

End RotationTests.

(** * Flat arithmetic *)

Module FlatTests.

  (** Prepared xor of the one-bit constants one and one is the constant zero. *)
  Example xor_one_bit :
    tnum_xor_flat_m (Z.ones 1) (Tnum 0 1) (Tnum 0 1) = Tnum 1 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared xor of the byte constants 15 and 85 is the constant 90. *)
  Example xor_byte :
    tnum_xor_flat_m (Z.ones 8) (Tnum 240 15) (Tnum 170 85) = Tnum 165 90.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared xor at width 64 of masks that know only a byte knows only the low byte. *)
  Example xor_word :
    tnum_xor_flat_m (Z.ones 64) (Tnum 240 15) (Tnum 170 85) = Tnum 165 90.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared xor of the word constants 15 and 85 is the word constant 90. *)
  Example xor_wrapped_word :
    tnum_xor_flat_m (Z.ones 64) (Tnum (2 ^ 64 - 16) 15) (Tnum (2 ^ 64 - 86) 85) =
      Tnum (2 ^ 64 - 91) 90.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared xor clips an oversized mask to a byte. *)
  Example xor_oversized_mask_clips :
    tnum_xor_flat_m (Z.ones 8) (Tnum (-16) 257) (Tnum 240 15) = Tnum 241 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared xor with an unknown operand is unknown. *)
  Example xor_unknown_operand_gives_unknown :
    tnum_xor_flat_m (Z.ones 8) (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared xor of a mask with conflicting bits and a constant keeps the conflicting bits. *)
  Example xor_conflicting_mask_keeps_conflict :
    tnum_xor_flat_m (Z.ones 8) (Tnum 7 7) (Tnum 240 15) = Tnum 7 7.
  Proof. vm_compute. reflexivity. Qed.

  (** The fast negation of the one-bit constant one is the constant one. *)
  Example neg_fast_one_bit :
    tnum_neg_fast_m (Z.ones 1) (Tnum 0 1) = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The fast negation of the byte constant 15 is the constant 241. *)
  Example neg_fast_byte :
    tnum_neg_fast_m (Z.ones 8) (Tnum 240 15) = Tnum 14 241.
  Proof. vm_compute. reflexivity. Qed.

  (** The fast negation at width 64 of a mask that knows only a byte knows only the low byte. *)
  Example neg_fast_word :
    tnum_neg_fast_m (Z.ones 64) (Tnum 240 15) = Tnum 14 241.
  Proof. vm_compute. reflexivity. Qed.

  (** The fast negation of the word constant 15 is the word constant minus 15. *)
  Example neg_fast_wrapped_word :
    tnum_neg_fast_m (Z.ones 64) (Tnum (2 ^ 64 - 16) 15) = Tnum 14 (2 ^ 64 - 15).
  Proof. vm_compute. reflexivity. Qed.

  (** The fast negation clips an oversized mask to a byte. *)
  Example neg_fast_oversized_mask_clips :
    tnum_neg_fast_m (Z.ones 8) (Tnum (-16) 257) = Tnum 0 241.
  Proof. vm_compute. reflexivity. Qed.

  (** The fast negation of an unknown mask is unknown. *)
  Example neg_fast_unknown :
    tnum_neg_fast_m (Z.ones 8) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared addition of the one-bit constants one and one is the constant zero. *)
  Example add_one_bit :
    tnum_add_flat_m (Z.ones 1) (Tnum 0 1) (Tnum 0 1) = Tnum 1 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared addition of seven or fifteen and one leaves the fourth and fifth bits unknown. *)
  Example add_byte :
    tnum_add_flat_m (Z.ones 8) (Tnum 240 7) (Tnum 254 1) = Tnum 231 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared addition of the byte constants 15 and 85 is the constant 100. *)
  Example add_byte_uncertain_carry :
    tnum_add_flat_m (Z.ones 8) (Tnum 240 15) (Tnum 170 85) = Tnum 155 100.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared addition of the word constants 15 and 85 is the word constant 100. *)
  Example add_wrapped_word :
    tnum_add_flat_m (Z.ones 64) (Tnum (2 ^ 64 - 16) 15) (Tnum (2 ^ 64 - 86) 85) =
      Tnum (2 ^ 64 - 101) 100.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared subtraction of the one-bit constant one from zero is the constant one. *)
  Example sub_one_bit :
    tnum_sub_flat_m (Z.ones 1) (Tnum 1 0) (Tnum 0 1) = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared subtraction of one from eight or nine leaves the low four bits unknown. *)
  Example sub_byte :
    tnum_sub_flat_m (Z.ones 8) (Tnum 246 8) (Tnum 254 1) = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared subtraction of the byte constants 85 from 15 is the constant 186. *)
  Example sub_byte_uncertain_borrow :
    tnum_sub_flat_m (Z.ones 8) (Tnum 240 15) (Tnum 170 85) = Tnum 69 186.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared subtraction at width 64 of masks that know only a byte knows only the low byte. *)
  Example sub_word_uncertain_borrow :
    tnum_sub_flat_m (Z.ones 64) (Tnum 240 15) (Tnum 170 85) = Tnum 69 186.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared negation of the one-bit constant one is the constant one. *)
  Example neg_flat_one_bit :
    tnum_neg_flat_m (Z.ones 1) (Tnum 0 1) = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared negation of the byte constant 15 is the constant 241. *)
  Example neg_flat_byte :
    tnum_neg_flat_m (Z.ones 8) (Tnum 240 15) = Tnum 14 241.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared negation of the word constant 15 is the word constant minus 15. *)
  Example neg_flat_wrapped_word :
    tnum_neg_flat_m (Z.ones 64) (Tnum (2 ^ 64 - 16) 15) = Tnum 14 (2 ^ 64 - 15).
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared addition clips an oversized mask to a byte before adding. *)
  Example add_flat_oversized_mask_clips :
    tnum_add_flat_m (Z.ones 8) (Tnum (-16) 257) (Tnum 254 1) = Tnum 225 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared subtraction clips an oversized mask to a byte. *)
  Example sub_flat_oversized_mask_clips :
    tnum_sub_flat_m (Z.ones 8) (Tnum (-16) 257) (Tnum 254 1) = Tnum 241 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared negation clips an oversized mask to a byte. *)
  Example neg_flat_oversized_mask_clips :
    tnum_neg_flat_m (Z.ones 8) (Tnum (-16) 257) = Tnum 0 241.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared addition of unknown masks is unknown. *)
  Example add_flat_unknown :
    tnum_add_flat_m (Z.ones 8) (Tnum 0 0) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared subtraction of unknown masks is unknown. *)
  Example sub_flat_unknown :
    tnum_sub_flat_m (Z.ones 8) (Tnum 0 0) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Prepared negation of an unknown mask is unknown. *)
  Example neg_flat_unknown :
    tnum_neg_flat_m (Z.ones 8) (Tnum 0 0) = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An initial carry of true adds one to the byte sum 100, giving the constant 101. *)
  Example adc_initial_carry :
    tnum_adc_flat_m (Z.ones 8) (Tnum 240 15) (Tnum 170 85) true = Tnum 154 101.
  Proof. vm_compute. reflexivity. Qed.

End FlatTests.

(** * Specification *)

Module SpecificationTests.

  (** The raw fixtures include narrow words, unknown facts, contradictions and oversized masks. *)
  Definition shared_mask_fixtures : list (positive * tnum * tnum) :=
    [(1%positive, Tnum 240 15, Tnum 0 0);
     (1%positive, Tnum 7 7, Tnum 257 258);
     (8%positive, Tnum 240 15, Tnum 252 1);
     (8%positive, Tnum 0 0, Tnum 7 7);
     (8%positive, Tnum (-16) 257, Tnum 65280 255);
     (64%positive, Tnum 61680 3855, Tnum 65280 255);
     (64%positive, Tnum 0 0, Tnum 7 7)].

  (** The masked normalisation agrees with the reference on every shared fixture. *)
  Example normalise_agrees :
    Forall (fun '(w, a, _) => MaskCode.tnum_normalise w a = tnum_normalise w a)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked complement agrees with the reference on every shared fixture. *)
  Example not_agrees :
    Forall (fun '(w, a, _) => MaskCode.tnum_not w a = tnum_not w a)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked negation agrees with the reference on every shared fixture. *)
  Example neg_agrees :
    Forall (fun '(w, a, _) => MaskCode.tnum_neg w a = tnum_neg w a)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked addition agrees with the reference on every shared fixture. *)
  Example add_agrees :
    Forall (fun '(w, a, b) => MaskCode.tnum_add w a b = tnum_add w a b)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked subtraction agrees with the reference on every shared fixture. *)
  Example sub_agrees :
    Forall (fun '(w, a, b) => MaskCode.tnum_sub w a b = tnum_sub w a b)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked conjunction agrees with the reference on every shared fixture. *)
  Example and_agrees :
    Forall (fun '(w, a, b) => MaskCode.tnum_and w a b = tnum_and w a b)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked disjunction agrees with the reference on every shared fixture. *)
  Example or_agrees :
    Forall (fun '(w, a, b) => MaskCode.tnum_or w a b = tnum_or w a b)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked exclusive or agrees with the reference on every shared fixture. *)
  Example xor_agrees :
    Forall (fun '(w, a, b) => MaskCode.tnum_xor w a b = tnum_xor w a b)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked join agrees with the reference join on every shared fixture. *)
  Example join_agrees :
    Forall (fun '(w, a, b) => MaskCode.pjoin w a b = tnum_join w a b)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked meet agrees with the reference meet on every shared fixture. *)
  Example meet_agrees :
    Forall (fun '(w, a, b) => MaskCode.pmeet w a b = tnum_meet w a b)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked emptiness test agrees with the reference on every shared fixture. *)
  Example empty_agrees :
    Forall (fun '(w, a, _) => MaskCode.pis_bot w a = tnum_empty w a)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked constant agrees with the reference constant on every shared fixture. *)
  Example const_agrees :
    Forall (fun '(w, a, _) => MaskCode.pconst w (ones a) = tnum_const w (ones a))
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked point test agrees with the reference point test on every shared fixture. *)
  Example point_agrees :
    Forall (fun '(w, a, _) => MaskCode.ppoint w a = tnum_constant w a)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked order agrees with the reference order on every shared fixture. *)
  Example leb_agrees :
    Forall (fun '(w, a, b) =>
      MaskCode.pleb w a b = tnum_empty w a ||
        (tnum_subset w (zeros b) (zeros a) && tnum_subset w (ones b) (ones a)))
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

  (** The masked widening agrees with the reference widening on every shared fixture. *)
  Example widen_agrees :
    Forall (fun '(w, a, b) =>
      MaskCode.pwiden tt w a b =
        if tnum_empty w b || (tnum_subset w (zeros a) (zeros b) &&
          tnum_subset w (ones a) (ones b)) then a else tnum_join w a b)
      shared_mask_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

End SpecificationTests.
