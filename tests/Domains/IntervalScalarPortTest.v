(** * Fixed-width interval operations

    These examples exercise clipping, arithmetic and comparisons.
    For example, clipping at width one retains the interval from zero to one.
    Builds on: IntervalOps IntervalBack BitsLang Tagged Harness WordSig ZLang.

    Groups:
    - [ClipTests] Clipping an interval to a word.
    - [PayloadConstantTests] Constants wrap to the width of their payload.
    - [PayloadLatticeTests] Join, meet, widen and narrow at shared moduli.
    - [ArithmeticTests] Word arithmetic and signed division, remainder and shifts.
    - [ComparisonTests] Unsigned and equality comparisons.
    - [AssumeTests] Refinement of an operand from a result.
    - [BackwardTests] Backward transfers, including malformed inputs.
    - [BitwiseTests] Masks, complements and empty bitwise operands.
    - [WordShiftTests] Left and logical right shifts at two widths.
    - [SignedConstantTests] Signs and signed views of constant ranges.
    - [JoinMeetTests] Join and meet of scalar intervals.
    - [WideningTests] Widening and narrowing with thresholds.
    - [ThresholdTreeTests] Threshold trees and their ranks. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import ValueSig IntervalSig Thresholds ThresholdsSig Interval
  IntervalOps IntervalBack BitsLang Tagged Harness WordSig ZLang.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Scalar := IntervalBaseCode ThresholdsCode.
Module Ops := IntervalOpsCode ThresholdsCode Scalar.
Import Ops.
Module Payload := IntervalPayloadCode WordLanguageCode ThresholdsCode Scalar.
Module PayloadPlain := IntervalPayload WordLanguage Thresholds Scalar.
Module ScalarPlain := Interval ZLang Thresholds.
Module Table := IntervalWordTableCode WordLanguageCode ThresholdsCode Scalar Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.

(** The backward transfer of an operation, read as intervals. *)
Definition interval_back o xs rw q :=
  map (fun a =>
      match a with TBot => IBot | TVal _ p => p | TAny => Payload.ptop rw end)
    (Domain.backward (BOp o) (TVal rw q) (map (fun wp => TVal (fst wp) (snd wp)) xs)).

(** The forward transfer of an operation, read as an interval. *)
Definition interval_fwd o xs rw :=
  match Domain.forward (BOp o) (map (fun wp => TVal (fst wp) (snd wp)) xs) with
  | TBot => IBot | TVal _ p => p | TAny => Payload.ptop rw
  end.

(** * Clipping *)

Module ClipTests.

  (** Clipping an unbounded interval gives the full eight-bit range. *)
  Example unbounded_interval_clips_to_eight_bit_range :
    interval_clip 8%positive (I NegInf PosInf) = I (Fin 0) (Fin 255).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Clipping at width one keeps the interval from zero to one. *)
  Example clip_at_width_one_gives_zero_to_one :
    interval_clip 1%positive (I (Fin (-1)) (Fin 2)) = I (Fin 0) (Fin 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

End ClipTests.

(** * Payload constants *)

Module PayloadConstantTests.

  (** A constant beyond the width wraps once to its residue. *)
  Example constant_beyond_width_wraps_once :
    Payload.pconst 64%positive (2 ^ 64 + 5) = I (Fin 5) (Fin 5).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constant in range is the point interval at that constant. *)
  Example constant_in_range_is_point :
    Payload.pconst 64%positive 5 = I (Fin 5) (Fin 5).
  Proof.
    vm_compute. reflexivity.
  Qed.

End PayloadConstantTests.

(** * Payload lattice *)

Module PayloadLatticeTests.

  (** The first range is not included in the second at either width. *)
  Example shared_modulus_inclusion_fails_at_both_widths :
    map (fun w => Payload.pleb w (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 9)))
      [8%positive; 64%positive] = [false; false].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Join at both widths is the hull of the two ranges. *)
  Example shared_modulus_join_is_hull :
    map (fun w => Payload.pjoin w (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 9)))
      [8%positive; 64%positive] = [I (Fin 1) (Fin 9); I (Fin 1) (Fin 9)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Meet at both widths is the overlap of the two ranges. *)
  Example shared_modulus_meet_is_overlap :
    map (fun w => Payload.pmeet w (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 9)))
      [8%positive; 64%positive] = [I (Fin 2) (Fin 4); I (Fin 2) (Fin 4)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening with thresholds at both widths stops at the next threshold. *)
  Example shared_modulus_widen_stops_at_threshold :
    map (fun w => Payload.pwiden (ThresholdsCode.make [0; 8; 255]) w
      (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 9))) [8%positive; 64%positive] =
      [I (Fin 1) (Fin 255); I (Fin 1) (Fin 255)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing at both widths keeps the first range. *)
  Example shared_modulus_narrow_keeps_first_range :
    map (fun w => Payload.pnarrow w (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 9)))
      [8%positive; 64%positive] = [I (Fin 1) (Fin 4); I (Fin 1) (Fin 4)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End PayloadLatticeTests.

(** * Arithmetic *)

Module ArithmeticTests.

  (** Adding two ranges within the word gives the range of their sums. *)
  Example add_in_range_sums_endpoints :
    interval_add 8%positive (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 5)) =
      I (Fin 3) (Fin 9).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A sum that wraps around the word gives the full word range. *)
  Example add_that_wraps_gives_full_word_range :
    interval_add 8%positive (I (Fin 250) (Fin 255)) (I (Fin 1) (Fin 2)) =
      I (Fin 0) (Fin 255).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An addition with a bottom first operand gives the one-bit range from zero to one. *)
  Example add_with_bottom_operand_gives_zero_to_one :
    interval_add 1%positive IBot (I (Fin 0) (Fin 1)) = I (Fin 0) (Fin 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Unsigned division by a range that contains zero gives the maximum word value. *)
  Example udiv_by_zero_gives_maximum :
    interval_udiv 8%positive (I (Fin 1) (Fin 3)) (I (Fin 0) (Fin 0)) =
      I (Fin 255) (Fin 255).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unsigned remainder of two constants is their constant remainder. *)
  Example urem_of_constants_is_constant :
    interval_urem 4%positive (I (Fin 5) (Fin 5)) (I (Fin 2) (Fin 2)) =
      I (Fin 1) (Fin 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A forward sum clips an unbounded operand to the word range before it adds. *)
  Example forward_add_clips_operand_to_word :
    interval_fwd bvadd [(8%positive, I NegInf (Fin 3));
                        (8%positive, I (Fin 2) (Fin 4))] 8%positive =
      I (Fin 2) (Fin 7).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A forward sum with a bottom operand is bottom. *)
  Example forward_add_with_bottom_operand_is_bottom :
    interval_fwd bvadd [(8%positive, IBot); (8%positive, I NegInf PosInf)] 8%positive = IBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The signed modulus of two constants is their signed remainder. *)
  Example signed_mod_of_singletons :
    interval_fwd bvsmod [(8%positive, I (Fin 251) (Fin 251));
                         (8%positive, I (Fin 3) (Fin 3))] 8%positive = I (Fin 1) (Fin 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The signed modulus with a positive divisor range is bounded by the divisor. *)
  Example signed_mod_with_positive_divisor_is_bounded :
    interval_fwd bvsmod [(8%positive, I (Fin 251) (Fin 252));
                         (8%positive, I (Fin 2) (Fin 3))] 8%positive = I (Fin 0) (Fin 2).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed division by a range containing zero gives the range from 1 to 129. *)
  Example signed_division_by_range_containing_zero :
    interval_fwd bvsdiv [(8%positive, I (Fin 128) (Fin 129));
                         (8%positive, I (Fin 0) (Fin 1))] 8%positive =
      I (Fin 1) (Fin 129).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed division by minus one gives the range from 127 to 128. *)
  Example signed_division_by_minus_one_range :
    interval_fwd bvsdiv [(8%positive, I (Fin 128) (Fin 129));
                         (8%positive, I (Fin 255) (Fin 255))] 8%positive =
      I (Fin 127) (Fin 128).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The signed remainder interval covers both exact results, without being exact. *)
  Example signed_remainder_interval_covers_exact_results :
    interval_fwd bvsrem [(8%positive, I (Fin 5) (Fin 5));
                         (8%positive, I (Fin 2) (Fin 3))] 8%positive = I (Fin 0) (Fin 2).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The exact signed remainder of five by two is one. *)
  Example signed_remainder_of_five_by_two_is_one :
    eval_op bvsrem [(8%positive, 5); (8%positive, 2)] = Some (8%positive, 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The exact signed remainder of five by three is two. *)
  Example signed_remainder_of_five_by_three_is_two :
    eval_op bvsrem [(8%positive, 5); (8%positive, 3)] = Some (8%positive, 2).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Eight-bit arithmetic shifts as ((value range, count range), result). A negative range
      stays negative and saturates at minus one, and a nonnegative range saturates at zero. *)
  Definition arithmetic_shift_cases : list ((itv * itv) * itv) :=
    [((I (Fin 248) (Fin 252), I (Fin 1) (Fin 2)), I (Fin 252) (Fin 255));
     ((I (Fin 248) (Fin 252), I (Fin 7) (Fin 8)), I (Fin 255) (Fin 255));
     ((I (Fin 2) (Fin 4), I (Fin 8) (Fin 9)), I (Fin 0) (Fin 0))].

  (** The forward arithmetic shift gives the result of every case of its table. *)
  Example arithmetic_shift_boundaries :
    map (fun c => interval_fwd bvashr [(8%positive, fst (fst c)); (8%positive, snd (fst c))]
      8%positive) arithmetic_shift_cases = map snd arithmetic_shift_cases.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A forward selection joins the ranges of its two branches. *)
  Example forward_ite_joins_branch_ranges :
    interval_fwd bvite [(1%positive, I (Fin 0) (Fin 1)); (8%positive, I (Fin 2) (Fin 4));
                        (8%positive, I (Fin 11) (Fin 12))] 8%positive = I (Fin 2) (Fin 12).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An addition of operands of mismatched widths gives bottom. *)
  Example add_of_mismatched_widths_is_bottom :
    interval_fwd bvadd [(1%positive, I (Fin 0) (Fin 0)); (4%positive, I (Fin 1) (Fin 1))]
      1%positive = IBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ArithmeticTests.

(** * Comparisons *)

Module ComparisonTests.

  (** An unsigned less-than of disjoint ranges is decided true. *)
  Example ult_of_disjoint_ranges_is_true :
    interval_ult (I (Fin 0) (Fin 3)) (I (Fin 5) (Fin 10)) = I (Fin 1) (Fin 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An unsigned less-than of overlapping ranges is unknown. *)
  Example ult_of_overlapping_ranges_is_unknown :
    interval_ult (I (Fin 0) (Fin 10)) (I (Fin 5) (Fin 10)) = I (Fin 0) (Fin 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Equality of equal singletons is true. *)
  Example eq_of_equal_singletons_is_true :
    interval_eq (I (Fin 1) (Fin 1)) (I (Fin 1) (Fin 1)) = I (Fin 1) (Fin 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A disequality assumption on equal singletons leaves no value for either operand. *)
  Example neq_assume_of_equal_singletons_is_bottom :
    interval_assume_neq (I (Fin 0) (Fin 0)) (I (Fin 0) (Fin 0)) = (IBot, IBot).
  Proof.
    vm_compute. reflexivity.
  Qed.

End ComparisonTests.

(** * Assumptions *)

Module AssumeTests.

  (** A true unsigned less-than lowers the upper bound of the first operand below the second. *)
  Example assume_ult_lowers_first_upper_bound :
    interval_assume_ult (I (Fin 0) (Fin 20)) (I (Fin 5) (Fin 10)) =
      (I (Fin 0) (Fin 9), I (Fin 5) (Fin 10)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An addition result refines its first operand given the second. *)
  Example assume_add_refines_first_operand :
    interval_assume_add 8%positive (I (Fin 0) (Fin 10)) (I (Fin 2) (Fin 2))
      (I (Fin 5) (Fin 7)) = (I (Fin 3) (Fin 5), I (Fin 2) (Fin 2)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A subtraction result refines its first operand given the second. *)
  Example assume_sub_refines_first_operand :
    interval_assume_sub (I (Fin 5) (Fin 10)) (I (Fin 2) (Fin 2))
      (I (Fin 4) (Fin 5)) = (I (Fin 6) (Fin 7), I (Fin 2) (Fin 2)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A rewrap to four bits keeps an operand that already fits in four bits. *)
  Example assume_rewrap_keeps_operand_that_fits :
    interval_assume_rewrap 4%positive (I (Fin 0) (Fin 10)) (I (Fin 3) (Fin 5)) =
      I (Fin 3) (Fin 5).
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssumeTests.

(** * Backward transfers *)

Module BackwardTests.

  (** A false unsigned less-than raises the lower bound of the first operand. *)
  Example false_unsigned_less_than_raises_first_operand :
    interval_back bvult [(8%positive, I (Fin 0) (Fin 20));
                         (8%positive, I (Fin 5) (Fin 10))] 1%positive
      (I (Fin 0) (Fin 0)) = [I (Fin 5) (Fin 20); I (Fin 5) (Fin 10)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A backward truncation keeps an operand that already fits the narrower width. *)
  Example backward_truncation_keeps_operand_that_fits :
    interval_back (bvtrunc 4%positive) [(8%positive, I (Fin 0) (Fin 10))] 4%positive
      (I (Fin 3) (Fin 5)) = [I (Fin 3) (Fin 5)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Operand lists with an empty, unbounded and mismatched-width entry. *)
  Definition malformed_backward_inputs : list (list (width * itv)) :=
    [[]; [(8%positive, I NegInf PosInf)];
     [(1%positive, I NegInf PosInf); (4%positive, I (Fin (-3)) (Fin 20));
      (8%positive, I PosInf PosInf)]].

  (** A backward transfer of malformed operand lists gives the raw operands back. *)
  Example backward_malformed_inputs_keep_raw_intervals :
    map (fun xs => interval_back bvadd xs 1%positive (I (Fin 1) (Fin 1)))
      malformed_backward_inputs =
    [[]; [I NegInf PosInf]; [I NegInf PosInf; I (Fin (-3)) (Fin 20); I PosInf PosInf]].
  Proof.
    vm_compute. reflexivity.
  Qed.

End BackwardTests.

(** * Bitwise operations *)

Module BitwiseTests.

  (** A bitwise and with a low mask keeps only the mask bits. *)
  Example and_with_low_mask_keeps_low_bits :
    interval_and 8%positive (I (Fin 240) (Fin 255)) (I (Fin 15) (Fin 15)) =
      I (Fin 0) (Fin 15).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A bitwise or and exclusive or of small operands stay below the next power of two. *)
  Example or_xor_of_small_ranges_stays_below_eight :
    interval_or_xor 8%positive (I (Fin 1) (Fin 2)) (I (Fin 4) (Fin 4)) =
      I (Fin 0) (Fin 7).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The complement of a high range is a low range. *)
  Example not_of_high_range_is_low_range :
    interval_not 8%positive (I (Fin 250) (Fin 255)) = I (Fin 0) (Fin 5).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A bitwise and with a bottom operand gives the one-bit range from zero to one. *)
  Example and_with_bottom_operand_gives_zero_to_one :
    interval_and 1%positive IBot (I (Fin 1) (Fin 1)) = I (Fin 0) (Fin 1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The population count of a one-bit point is the point of its count. *)
  Example popcount_of_point_is_point :
    interval_fwd bvpopcnt [(1%positive, I (Fin 0) (Fin 0))] 1%positive = I (Fin 0) (Fin 0).
  Proof.
    vm_compute. reflexivity.
  Qed.

End BitwiseTests.

(** * Word shifts *)

Module WordShiftTests.

  (** The two word widths at which the shifts of small ranges agree. *)
  Definition shift_widths : list positive := [8%positive; 64%positive].

  (** Eight-bit left shifts as ((value range, count range), result). A full range stays full,
      and a count range with a negative high end gives reversed bounds. *)
  Definition shl_cases : list ((itv * itv) * itv) :=
    [((I (Fin 0) (Fin 255), I (Fin 0) (Fin 7)), I (Fin 0) (Fin 255));
     ((I (Fin 1) (Fin 4), I (Fin 0) (Fin (-1))), I (Fin 1) (Fin 0))].

  (** Eight-bit logical right shifts as ((value range, count range), result). A full range stays
      full, a count range with a negative high end gives zero to four, and a value range with a
      negative high end gives a negative upper bound. *)
  Definition lshr_cases : list ((itv * itv) * itv) :=
    [((I (Fin 0) (Fin 255), I (Fin 0) (Fin 7)), I (Fin 0) (Fin 255));
     ((I (Fin 1) (Fin 4), I (Fin 0) (Fin (-1))), I (Fin 0) (Fin 4));
     ((I (Fin 1) (Fin (-4)), I (Fin 2) (Fin 3)), I (Fin 0) (Fin (-1)))].

  (** A left shift by two or three gives the same result at widths eight and sixty-four. *)
  Example shl_at_widths_eight_and_sixty_four :
    Forall (fun w => Ops.interval_shl w (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 3)) =
      I (Fin 4) (Fin 32)) shift_widths.
  Proof.
    repeat constructor; vm_compute; reflexivity.
  Qed.

  (** A logical right shift by two or three gives the same result at widths eight and sixty-four. *)
  Example lshr_at_widths_eight_and_sixty_four :
    Forall (fun w => Ops.interval_lshr w (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 3)) =
      I (Fin 0) (Fin 1)) shift_widths.
  Proof.
    repeat constructor; vm_compute; reflexivity.
  Qed.

  (** The left shift gives the result of every case of its table. *)
  Example left_shift_boundaries :
    map (fun c => Ops.interval_shl 8%positive (fst (fst c)) (snd (fst c))) shl_cases =
      map snd shl_cases.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The logical right shift gives the result of every case of its table. *)
  Example logical_right_shift_boundaries :
    map (fun c => Ops.interval_lshr 8%positive (fst (fst c)) (snd (fst c))) lshr_cases =
      map snd lshr_cases.
  Proof.
    vm_compute. reflexivity.
  Qed.

End WordShiftTests.

(** * Signed constants *)

Module SignedConstantTests.

  (** The sign of a constant range is known only when the range does not cross the sign boundary. *)
  Example sign_of_constant_ranges :
    map (interval_sign 8%positive)
      [I (Fin 1) (Fin 4); I (Fin 252) (Fin 255); I (Fin 127) (Fin 128)] =
      [Some false; Some true; None].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The signed view of a range of negative constants is its signed endpoints. *)
  Example signed_view_of_negative_constants :
    interval_signed 8%positive (I (Fin 252) (Fin 255)) = Some (-4, -1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The negation of a range of negative constants gives positive constants. *)
  Example negation_of_negative_constants :
    interval_neg 8%positive (I (Fin 252) (Fin 255)) = I (Fin 1) (Fin 4).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed division of two constants gives the signed quotient. *)
  Example signed_division_of_constants :
    interval_sdiv 8%positive (I (Fin 252) (Fin 252)) (I (Fin 2) (Fin 2)) =
      I (Fin 254) (Fin 254).
  Proof.
    vm_compute. reflexivity.
  Qed.

End SignedConstantTests.

(** * Join and meet *)

Module JoinMeetTests.

  (** The join of two scalar intervals is their hull. *)
  Example scalar_join_is_hull :
    Scalar.interval_join (I (Fin 1) (Fin 3)) (I (Fin 2) (Fin 5)) = I (Fin 1) (Fin 5).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The meet of two disjoint scalar intervals is bottom. *)
  Example scalar_meet_of_disjoint_is_bottom :
    Scalar.interval_meet (I (Fin 1) (Fin 2)) (I (Fin 3) (Fin 4)) = IBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The meet of a point at positive infinity with the full range is bottom. *)
  Example scalar_meet_of_positive_infinity_is_bottom :
    Scalar.interval_meet (I PosInf PosInf) (I NegInf PosInf) = IBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The meet of a point at negative infinity with the full range is bottom. *)
  Example scalar_meet_of_negative_infinity_is_bottom :
    Scalar.interval_meet (I NegInf NegInf) (I NegInf PosInf) = IBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

End JoinMeetTests.

(** * Widening *)

Module WideningTests.

  (** Widening stops at the next threshold above the growing bound. *)
  Example widening_stops_at_next_threshold :
    Scalar.interval_stable_widen (ThresholdsCode.make [0; 10; 20])
      (I (Fin 2) (Fin 4)) (I (Fin 1) (Fin 12)) = I (Fin 0) (Fin 20).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening with unsorted thresholds still stops at the next threshold. *)
  Example widening_with_unsorted_thresholds_stops_at_next :
    Scalar.interval_stable_widen (ThresholdsCode.make [20; 0; 10; 10])
      (I (Fin 8) (Fin 9)) (I (Fin 7) (Fin 11)) = I (Fin 0) (Fin 20).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening past the last threshold gives an infinite bound. *)
  Example widening_past_last_threshold_is_infinite :
    Scalar.interval_stable_widen (ThresholdsCode.make [0; 10])
      (I (Fin 0) (Fin 10)) (I (Fin (-1)) (Fin 11)) = I NegInf PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Narrowing replaces infinite bounds by the finite bounds of the other range. *)
  Example narrow_replaces_infinite_bounds :
    Scalar.interval_narrow (I NegInf PosInf) (I (Fin 0) (Fin 8)) = I (Fin 0) (Fin 8).
  Proof.
    vm_compute. reflexivity.
  Qed.

End WideningTests.

(** * Threshold trees *)

Module ThresholdTreeTests.

  (** Sorted thresholds build a balanced tree with the middle threshold at the root. *)
  Example sorted_thresholds_build_balanced_tree :
    ThresholdsCode.make [1; 2; 3] = TNode (TNode TLeaf 1 TLeaf) 2 (TNode TLeaf 3 TLeaf).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Duplicate thresholds collapse to a single node. *)
  Example duplicate_thresholds_collapse_to_one_node :
    ThresholdsCode.make [10; 10; 10] = TNode TLeaf 10 TLeaf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The payload rank with duplicate thresholds is four. *)
  Example payload_rank_with_duplicate_thresholds_is_four :
    PayloadPlain.pwrank (ThresholdsCode.make [0; 0; 5]) 8%positive
      (I (Fin 1) (Fin 3)) = 4%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The scalar rank counts duplicate nodes of the tree. *)
  Example scalar_rank_counts_duplicate_nodes :
    ScalarPlain.wrank (TNode (TNode TLeaf 0 TLeaf) 0 (TNode TLeaf 5 TLeaf))
      (I (Fin 1) (Fin 3)) = 5%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ThresholdTreeTests.
