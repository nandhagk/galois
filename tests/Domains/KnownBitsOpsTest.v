(** * Known-bit transfer observations

    Forward and backward operations retain their source mask observations.
    For example, an unknown shift count can retain several possible bits.
    Builds on: KnownBitsOps and KnownBitsBack. *)

(* Groups:
   - Fixtures: the stage configuration, the mask and operation modules, and the tables.
   - Shifts: shifts with variable and negative counts.
   - Extraction: bit extraction with known and unknown endpoints.
   - Ranges: unsigned range queries and the public range contract.
   - Operators: rotation, comparison, arithmetic shift and concatenation.
   - Backward: backward transfer of addition. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import ValueSig WordSig BitsLang KnownBitsSig KnownBits KnownBitsOps
  KnownBitsBack Tagged Harness.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

(** The multiplier stage configuration used by the known-bit modules. *)
Module Stages <: TNUM_CONFIG.
  Definition multiplier := MulStages.
End Stages.
(** The known-bit masks over the word language. *)
Module Masks := KnownBitsCode WordLanguageCode Stages.
(** The fast known-bit operations over the masks. *)
Module Ops := KnownBitsOpsFastCode WordLanguageCode Stages Masks.
(** The known-bit table over the masks. *)
Module Table := KnownBitsTableCode WordLanguageCode Stages Masks.
(** The range queries over the masks. *)
Module Ranges := KnownBitsRangeCode WordLanguageCode Stages Masks.

(** The checked known-bit modules, with their public specifications. *)
Module CheckedMasks := KnownBits WordLanguage Stages.
Module CheckedTable := KnownBitsTable WordLanguage Stages CheckedMasks.
Module CheckedBase := Tagged WordLanguage CheckedMasks.
Module CheckedTaggedTable := TaggedTable WordLanguage CheckedMasks CheckedTable CheckedBase.
Module CheckedDomain := Harness BitsLang CheckedBase CheckedTaggedTable.
Module CheckedRanges := KnownBitsRange WordLanguage Stages CheckedMasks CheckedDomain.

(** Concatenation fixtures: width, width, first mask, second mask. *)
Definition shifted_concat_fixtures : list (positive * positive * tnum * tnum) :=
  [(1%positive, 1%positive, Tnum 0 1, Tnum 1 0);
   (8%positive, 8%positive, Tnum 240 15, Tnum 252 1);
   (8%positive, 8%positive, Tnum (-16) 257, Tnum 0 0);
   (8%positive, 1%positive, Tnum 7 7, Tnum 0 0);
   (64%positive, 64%positive, Tnum 61680 3855, Tnum 65280 255)].

(** * Shifts *)

Module ShiftTests.

  (** A negative scalar shift count of left shift at width eight gives two. *)
  Example negative_count_left_shift_is_two :
    tnum_scalar_value bvshl 8%positive (-1) 2 = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative scalar shift count of logical right shift at width eight gives one. *)
  Example negative_count_logical_shift_is_one :
    tnum_scalar_value bvlshr 8%positive (-1) 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A negative scalar shift count of arithmetic right shift at width eight gives one. *)
  Example negative_count_arithmetic_shift_is_one :
    tnum_scalar_value bvashr 8%positive (-1) 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A left shift by a known count gives the shifted known bits. *)
  Example variable_left_shift_known_count :
    Ops.tnum_forward_raw bvshl [(8%positive, tnum_const 8%positive 1);
      (8%positive, Tnum 252 0)] 8%positive = Tnum 240 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An arithmetic right shift keeps the sign bit known. *)
  Example variable_arithmetic_shift_keeps_sign :
    Ops.tnum_forward_raw bvashr [(8%positive, tnum_const 8%positive 128);
      (8%positive, Tnum 252 0)] 8%positive = Tnum 15 128.
  Proof. vm_compute. reflexivity. Qed.

End ShiftTests.

(** * Extraction *)

Module ExtractionTests.

  (** Extracting bits 7 to 4 from a known four-bit value gives the high bits. *)
  Example extract_high_bits_of_known_word :
    Ops.tnum_forward_raw (bvextract 7 4) [(4%positive, Tnum 8 1)] 4%positive = Tnum 15 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits 3 to 0 from a four-bit value keeps its known bits. *)
  Example extract_low_bits_of_known_word :
    Ops.tnum_forward_raw (bvextract 3 0) [(4%positive, Tnum 8 1)] 4%positive = Tnum 8 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits 7 to 4 from an eight-bit value with known bits gives the high nibble. *)
  Example extract_high_nibble_of_eight_bits :
    Ops.tnum_forward_raw (bvextract 7 4) [(8%positive, Tnum 240 15)] 4%positive =
      Tnum 15 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits 3 to 0 from an eight-bit value with known bits gives the low nibble. *)
  Example extract_low_nibble_of_eight_bits :
    Ops.tnum_forward_raw (bvextract 3 0) [(8%positive, Tnum 240 15)] 4%positive =
      Tnum 0 15.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits 7 to 4 from an unknown four-bit value gives unknown bits. *)
  Example extract_high_bits_of_unknown_word :
    Ops.tnum_forward_raw (bvextract 7 4) [(4%positive, Tnum 0 0)] 4%positive = Tnum 15 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits 3 to 0 from an unknown four-bit value gives zero. *)
  Example extract_low_bits_of_unknown_word :
    Ops.tnum_forward_raw (bvextract 3 0) [(4%positive, Tnum 0 0)] 4%positive = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits 7 to 4 from an unknown eight-bit value gives zero. *)
  Example extract_high_bits_of_unknown_eight_bits :
    Ops.tnum_forward_raw (bvextract 7 4) [(8%positive, Tnum 0 0)] 4%positive = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Extracting bits 3 to 0 from an unknown eight-bit value gives zero. *)
  Example extract_low_bits_of_unknown_eight_bits :
    Ops.tnum_forward_raw (bvextract 3 0) [(8%positive, Tnum 0 0)] 4%positive = Tnum 0 0.
  Proof. vm_compute. reflexivity. Qed.

End ExtractionTests.

(** * Ranges *)

Module RangeTests.

  (** The range of a known word with a known high part is its low and high bounds. *)
  Example range_of_known_high_part :
    Ranges.range (TVal 8%positive (Tnum 240 7)) = (Fin 7, Fin 15).
  Proof. vm_compute. reflexivity. Qed.

  (** The range of a constant is the constant at both ends. *)
  Example range_of_constant :
    Ranges.range (TVal 8%positive (tnum_const 8%positive 42)) = (Fin 42, Fin 42).
  Proof. vm_compute. reflexivity. Qed.

  (** A word with inconsistent known bits has the empty range. *)
  Example range_of_inconsistent_bits_is_empty :
    Ranges.range (TVal 8%positive (Tnum 1 1)) = (PosInf, NegInf).
  Proof. vm_compute. reflexivity. Qed.

  (** The bottom tagged value has the empty range. *)
  Example range_of_bottom_is_empty :
    Ranges.range TBot = (PosInf, NegInf).
  Proof. vm_compute. reflexivity. Qed.

  (** The unknown tagged value has the whole range. *)
  Example range_of_unknown_is_whole :
    Ranges.range TAny = (NegInf, PosInf).
  Proof. vm_compute. reflexivity. Qed.

  (** The public range query is sound for every concrete value of the transfer domain. *)
  Example range_query_is_sound : forall c,
    CheckedDomain.gamma (TVal 8%positive (Tnum 240 7)) c ->
    in_bnd (Fin 7) (Fin 15) (KnownBitsNumU.num c).
  Proof.
    apply CheckedRanges.range_sound.
  Qed.

End RangeTests.

(** * Operators *)

Module OperatorTests.

  (** Rotating left a constant one by a known count at width five gives 28. *)
  Example rotate_left_at_width_five :
    Ops.tnum_forward_raw bvrotl [(5%positive, tnum_const 5%positive 1);
      (5%positive, Tnum 15 0)] 5%positive = Tnum 28 0.
  Proof. vm_compute. auto. Qed.

  (** Rotating right a constant one by a known count at width five gives 14. *)
  Example rotate_right_at_width_five :
    Ops.tnum_forward_raw bvrotr [(5%positive, tnum_const 5%positive 1);
      (5%positive, Tnum 15 0)] 5%positive = Tnum 14 0.
  Proof. vm_compute. auto. Qed.

  (** An unsigned comparison of a known high-bit value and a constant keeps its precision. *)
  Example unsigned_comparison_keeps_precision :
    Ops.tnum_forward_raw bvult [(8%positive, Tnum 128 0);
      (8%positive, tnum_const 8%positive 128)] 1%positive = Tnum 0 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenating the known bits of two words gives the concatenated known bits. *)
  Example concat_known_bits :
    Ops.tnum_forward_raw bvconcat [(8%positive, Tnum 240 15); (8%positive, Tnum 252 1)]
      16%positive = Tnum 61692 3841.
  Proof. vm_compute. reflexivity. Qed.

  (** Concatenation of each fixture gives the concatenation specification. *)
  Example concat_matches_specification :
    Forall (fun '(w, v, a, b) =>
      Ops.tnum_forward_raw bvconcat [(w, a); (v, b)] (w + v)%positive =
        tnum_concat w v a b) shifted_concat_fixtures.
  Proof.
    repeat (apply Forall_cons; [vm_compute; reflexivity|]).
    apply Forall_nil.
  Qed.

End OperatorTests.

(** * Backward *)

Module BackwardTests.

  (** A backward addition with a known result and a known operand gives the other operand. *)
  Example backward_add_known_operand :
    Table.wbwd bvadd 8%positive (tnum_const 8%positive 5)
      [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 1)] =
        Some [tnum_const 8%positive 4; tnum_const 8%positive 1].
  Proof. vm_compute. reflexivity. Qed.

End BackwardTests.
