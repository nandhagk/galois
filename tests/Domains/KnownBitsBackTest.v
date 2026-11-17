(** * Known-bit extraction table bounds

    Extraction offsets must be bounded before the table evaluates their arithmetic.
    For example, a one-bit operand cannot supply a bit at offset eight.
    Builds on: KnownBitsOps and the generated word-operation clocks.

    Groups:
    - [ClockTests] Lower bounds on the time of unchecked extraction.
    - [ExtractionTests] Forward and backward extraction, inside and outside the operand width.
    - [BackwardTests] Backward transfers of bitwise, projection, order, negation and shifts.
    - [RotationTests] Backward rotations at several widths. *)

From Stdlib Require Import ZArith NArith List Lia.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import BitsLang KnownBitsSig KnownBits KnownBitsOps KnownBitsBack.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

(** The multiplier stage configuration used by the known-bit modules. *)
Module Stages <: TNUM_CONFIG.
  Definition multiplier := MulStages.
End Stages.
(** The timed known-bit masks over the word language. *)
Module Masks := KnownBitsT WordLanguageT Stages.
(** The clocks of the unchecked known-bit operations. *)
Module RawClocks := KnownBitsOpsClock WordLanguageT Stages Masks.
(** The timed known-bit table over the masks. *)
Module Table := KnownBitsTableT WordLanguageT Stages Masks.

(** * Clocks *)

(** Converting a unary successor count visits every constructor. *)
Local Lemma successor_conversion_clock_lower : forall n,
  (N.of_nat n + 1 <= Op.Pos.T_of_succ_nat n)%N.
Proof.
  induction n as [|n IH]; time_unfold Op.Pos.T_of_succ_nat; time_cbn;
    rewrite ?Nat2N.inj_succ; lia.
Qed.

(** Converting a natural offset takes at least as many steps as its value. *)
Local Lemma offset_conversion_clock_lower : forall n,
  (N.of_nat n <= Op.Z.T_of_nat n)%N.
Proof.
  intros [|n]; time_unfold Op.Z.T_of_nat; time_cbn; [lia|].
  pose proof (successor_conversion_clock_lower n) as Hlower.
  rewrite ?Nat2N.inj_succ. lia.
Qed.

(** An unchecked extraction really pays for its arbitrary raw offset. *)
Local Lemma raw_extraction_clock_lower : forall lo,
  (N.of_nat lo <= RawClocks.T_tnum_forward_raw (bvextract 0 lo)
    [(1%positive, tnum_top)] 1%positive)%N.
Proof.
  intro lo. pose proof (offset_conversion_clock_lower lo) as Hlower.
  time_unfold RawClocks.T_tnum_forward_raw. time_cbn.
  time_unfold T_tnum_map. time_cbn. lia.
Qed.

Module ClockTests.

  (** Rejected offsets above the operand width cost the same however large they are. *)
  Example rejected_extraction_clock_constant : forall lo, (1 <= lo)%nat ->
    Table.T_wfwd (bvextract 0 lo) 1%positive [(1%positive, tnum_top)] =
    Table.T_wfwd (bvextract 0 1) 1%positive [(1%positive, tnum_top)].
  Proof. intros [|lo] Hlo; [lia|reflexivity]. Qed.

  (** Rejected backward offsets above the operand width cost the same however large they are. *)
  Example rejected_backward_extraction_clock_constant : forall lo, (1 <= lo)%nat ->
    Table.T_wbwd (bvextract 0 lo) 1%positive tnum_top [(1%positive, tnum_top)] =
    Table.T_wbwd (bvextract 0 1) 1%positive tnum_top [(1%positive, tnum_top)].
  Proof. intros [|lo] Hlo; [lia|reflexivity]. Qed.

  (** No fixed budget bounds the time of unchecked extraction at every offset. *)
  Example unchecked_extraction_clock_unbounded : forall budget : N,
    exists lo, (budget < RawClocks.T_tnum_forward_raw (bvextract 0 lo)
      [(1%positive, tnum_top)] 1%positive)%N.
  Proof.
    intro budget. exists (N.to_nat (N.succ budget)).
    pose proof (raw_extraction_clock_lower (N.to_nat (N.succ budget))) as Hlower.
    rewrite N2Nat.id in Hlower. lia.
  Qed.

End ClockTests.

(** * Extraction *)

Module ExtractionTests.

  (** A forward extraction past the operand width has no result. *)
  Example forward_extraction_past_width_is_none :
    Table.wfwd (bvextract 0 8) 1%positive [(1%positive, tnum_top)] = None.
  Proof. vm_compute; reflexivity. Qed.

  (** A backward extraction past the operand width has no result. *)
  Example backward_extraction_past_width_is_none :
    Table.wbwd (bvextract 0 8) 1%positive tnum_top [(1%positive, tnum_top)] = None.
  Proof. vm_compute; reflexivity. Qed.

  (** A forward extraction from bit zero keeps the top operand. *)
  Example forward_extraction_at_zero_keeps_top :
    Table.wfwd (bvextract 0 0) 1%positive [(1%positive, tnum_top)] = Some tnum_top.
  Proof. vm_compute; reflexivity. Qed.

  (** A backward extraction from bit zero keeps the constant operand. *)
  Example backward_extraction_at_zero_keeps_constant :
    Table.wbwd (bvextract 0 0) 1%positive (tnum_const 1%positive 1)
      [(1%positive, tnum_top)] = Some [tnum_const 1%positive 1].
  Proof. vm_compute; reflexivity. Qed.

End ExtractionTests.

(** * Backward *)

Module BackwardTests.

  (** A backward and with a constant result refines its operand to the constant. *)
  Example backward_and_constant_result :
    Table.wbwd bvand 8%positive (tnum_const 8%positive 15)
      [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 255)] =
        Some [tnum_const 8%positive 15; tnum_const 8%positive 255].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward or with a constant result refines its operand to the constant. *)
  Example backward_or_constant_result :
    Table.wbwd bvor 8%positive (tnum_const 8%positive 15)
      [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 0)] =
        Some [tnum_const 8%positive 15; tnum_const 8%positive 0].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward xor gives the operand the xor of the constant result and the other operand. *)
  Example backward_xor_constant_result :
    Table.wbwd bvxor 8%positive (tnum_const 8%positive 15)
      [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 3)] =
        Some [tnum_const 8%positive 12; tnum_const 8%positive 3].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward addition at width sixty-four refines its operand to the difference. *)
  Example backward_add_width_64 :
    Table.wbwd bvadd 64%positive (tnum_const 64%positive 15)
      [(64%positive, tnum_top); (64%positive, tnum_const 64%positive 3)] =
        Some [tnum_const 64%positive 12; tnum_const 64%positive 3].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward subtraction with a constant result refines its operand to the sum. *)
  Example backward_sub_constant_result :
    Table.wbwd bvsub 8%positive (tnum_const 8%positive 15)
      [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 3)] =
        Some [tnum_const 8%positive 18; tnum_const 8%positive 3].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward zero extension projects a constant onto its narrow source. *)
  Example backward_zero_extension_projects :
    Table.wbwd (bvzext 4%positive) 8%positive (tnum_const 8%positive 5)
      [(4%positive, tnum_top)] = Some [tnum_const 4%positive 5].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward sign extension projects a constant onto its narrow source. *)
  Example backward_sign_extension_projects :
    Table.wbwd (bvsext 4%positive) 8%positive (tnum_const 8%positive 253)
      [(4%positive, tnum_top)] = Some [tnum_const 4%positive 13].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward extraction projects a constant onto the bits it takes. *)
  Example backward_extraction_projects :
    Table.wbwd (bvextract 7 4) 4%positive (tnum_const 4%positive 5)
      [(8%positive, tnum_top)] = Some [Tnum 160 80].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward concatenation splits a constant into its two parts. *)
  Example backward_concat_splits_constant :
    Table.wbwd bvconcat 8%positive (tnum_const 8%positive 90)
      [(4%positive, tnum_top); (4%positive, tnum_top)] =
        Some [tnum_const 4%positive 5; tnum_const 4%positive 10].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward unsigned less-than bounds its first operand below the constant. *)
  Example backward_unsigned_less_than_bound :
    Table.wbwd bvult 1%positive (tnum_const 1%positive 1)
      [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 16)] =
        Some [Tnum 240 0; tnum_const 8%positive 16].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward unsigned less-or-equal bounds its first operand at the constant. *)
  Example backward_unsigned_less_equal_bound :
    Table.wbwd bvule 1%positive (tnum_const 1%positive 1)
      [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 15)] =
        Some [Tnum 240 0; tnum_const 8%positive 15].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward negation at width one gives the constant one. *)
  Example backward_not_at_width_one :
    Table.wbwd bvnot 1%positive (tnum_const 1%positive 0)
      [(1%positive, tnum_top)] = Some [tnum_const 1%positive 1].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward negation of a mask with conflicting bits keeps that mask. *)
  Example backward_not_of_exact_mask :
    Table.wbwd bvnot 8%positive (Tnum 7 7) [(8%positive, Tnum 7 7)] = Some [Tnum 7 7].
  Proof. vm_compute. reflexivity. Qed.

  (** A backward negation of a mask wider than the word wraps it first, giving the constant 255. *)
  Example backward_not_of_oversized_mask :
    Table.wbwd bvnot 8%positive (Tnum 511 256) [(8%positive, tnum_top)] =
      Some [Tnum 0 255].
  Proof. vm_compute. reflexivity. Qed.

  (** Undoing a left shift to 128 by zero to three bits makes the low four bits known zero. *)
  Example backward_shift_left_known_count :
    Table.wbwd bvshl 8%positive (tnum_const 8%positive 128)
      [(8%positive, tnum_top); (8%positive, Tnum 252 0)] =
        Some [Tnum 15 0; Tnum 252 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Undoing a logical right shift to 128 by zero to three bits makes bits 3 to 6 known zero. *)
  Example backward_shift_right_known_count :
    Table.wbwd bvlshr 8%positive (tnum_const 8%positive 128)
      [(8%positive, tnum_top); (8%positive, Tnum 252 0)] =
        Some [Tnum 120 0; Tnum 252 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Undoing an arithmetic right shift to 128 by zero to three bits keeps the sign bit one. *)
  Example backward_arithmetic_shift_keeps_sign :
    Table.wbwd bvashr 8%positive (tnum_const 8%positive 128)
      [(8%positive, tnum_top); (8%positive, Tnum 252 0)] =
        Some [Tnum 120 128; Tnum 252 0].
  Proof. vm_compute. reflexivity. Qed.

  (** A count that may equal the width leaves the operand of a backward logical shift unknown. *)
  Example backward_logical_shift_by_width_erases_bits :
    Table.wbwd bvlshr 8%positive (tnum_const 8%positive 15)
      [(8%positive, tnum_top); (8%positive, Tnum 247 0)] =
        Some [tnum_top; Tnum 247 0].
  Proof. vm_compute. reflexivity. Qed.

  (** A count that may equal the width leaves the sign bit of the operand known zero. *)
  Example backward_arithmetic_shift_by_width_keeps_sign :
    Table.wbwd bvashr 8%positive (tnum_const 8%positive 15)
      [(8%positive, tnum_top); (8%positive, Tnum 247 0)] =
        Some [Tnum 128 0; Tnum 247 0].
  Proof. vm_compute. reflexivity. Qed.

  (** At width one, a backward left shift gives no information about its operand. *)
  Example backward_shift_left_width_one :
    Table.wbwd bvshl 1%positive (tnum_const 1%positive 1)
      [(1%positive, tnum_top); (1%positive, tnum_top)] = Some [tnum_top; tnum_top].
  Proof. vm_compute. reflexivity. Qed.

  (** At width one, a backward arithmetic shift keeps the known result bit. *)
  Example backward_arithmetic_shift_width_one :
    Table.wbwd bvashr 1%positive (tnum_const 1%positive 1)
      [(1%positive, tnum_top); (1%positive, tnum_top)] = Some [Tnum 0 1; tnum_top].
  Proof. vm_compute. reflexivity. Qed.

  (** Masks wider than the word give no information about the operand of a left shift. *)
  Example backward_shift_raw_mask_left :
    Table.wbwd bvshl 8%positive (Tnum 511 256)
      [(8%positive, tnum_top); (8%positive, Tnum 256 0)] = Some [tnum_top; tnum_top].
  Proof. vm_compute. reflexivity. Qed.

  (** A result mask and a count mask wider than the word leave the operand sign bit known zero. *)
  Example backward_shift_raw_mask_arithmetic :
    Table.wbwd bvashr 8%positive (Tnum 511 256)
      [(8%positive, tnum_top); (8%positive, Tnum 256 0)] = Some [Tnum 128 0; tnum_top].
  Proof. vm_compute. reflexivity. Qed.

  (** A logical shift of a mask with conflicting bits by zero to three bits keeps the mask. *)
  Example backward_shift_exact_mask_logical :
    Table.wbwd bvlshr 8%positive (Tnum 7 7)
      [(8%positive, Tnum 7 7); (8%positive, Tnum 252 0)] = Some [Tnum 7 7; Tnum 252 0].
  Proof. vm_compute. reflexivity. Qed.

End BackwardTests.

(** * Rotation *)

Module RotationTests.

  (** A count of zero or eight rotates a byte by zero, so the left rotation keeps the constant. *)
  Example backward_rotate_left_keeps_constant :
    Table.wbwd bvrotl 8%positive (tnum_const 8%positive 15)
      [(8%positive, tnum_top); (8%positive, Tnum 247 0)] =
        Some [tnum_const 8%positive 15; Tnum 247 0].
  Proof. vm_compute. reflexivity. Qed.

  (** A count of zero or eight rotates a byte by zero, so the right rotation keeps the constant. *)
  Example backward_rotate_right_keeps_constant :
    Table.wbwd bvrotr 8%positive (tnum_const 8%positive 15)
      [(8%positive, tnum_top); (8%positive, Tnum 247 0)] =
        Some [tnum_const 8%positive 15; Tnum 247 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Undoing a left rotation by zero or one at width five leaves bits 0 and 4 possible. *)
  Example backward_rotate_left_nonpower_width :
    Table.wbwd bvrotl 5%positive (tnum_const 5%positive 1)
      [(5%positive, tnum_top); (5%positive, Tnum 15 0)] =
        Some [Tnum 14 0; Tnum 15 0].
  Proof. vm_compute. reflexivity. Qed.

  (** Undoing a right rotation by zero or one at width five leaves bits 0 and 1 possible. *)
  Example backward_rotate_right_nonpower_width :
    Table.wbwd bvrotr 5%positive (tnum_const 5%positive 1)
      [(5%positive, tnum_top); (5%positive, Tnum 15 0)] =
        Some [Tnum 28 0; Tnum 15 0].
  Proof. vm_compute. reflexivity. Qed.

  (** A left rotation of the all-ones constant at width sixty-four keeps the constant. *)
  Example backward_rotate_left_width_64 :
    Table.wbwd bvrotl 64%positive (Tnum 0 18446744073709551615)
      [(64%positive, tnum_top); (64%positive, tnum_top)] =
        Some [Tnum 0 18446744073709551615; tnum_top].
  Proof. vm_compute. reflexivity. Qed.

  (** A right rotation of the all-ones constant at width sixty-four keeps the constant. *)
  Example backward_rotate_right_width_64 :
    Table.wbwd bvrotr 64%positive (Tnum 0 18446744073709551615)
      [(64%positive, tnum_top); (64%positive, tnum_top)] =
        Some [Tnum 0 18446744073709551615; tnum_top].
  Proof. vm_compute. reflexivity. Qed.

End RotationTests.
