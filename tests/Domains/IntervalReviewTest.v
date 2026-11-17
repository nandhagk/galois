(** * Interval review witnesses

    These examples check raw endpoints and word boundary clipping.
    For example, clipping an unbounded interval at width one gives [0, 1].

    Groups:
    - [ClippingTests] Clipping a raw interval to a word keeps or changes its representation.
    - [RankTests] The rank of an interval with an infinite endpoint.
    - [PayloadWideningTests] Widening payloads at word boundaries and thresholds.
    - [PayloadBoundsTests] Raw intervals outside the word range act as bottom.
    - [ShiftTests] Shifts with negative or ordered endpoints.
    Builds on: Interval, IntervalOps, Thresholds and ZLang. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import ValueSig IntervalSig Interval IntervalOps IntervalBack BitsLang
  ThresholdsSig Thresholds ZLang.
Import List.ListNotations.

(** * Fixtures *)

Module Scalar := Interval ZLang Thresholds.
Module ScalarCode := IntervalBaseCode ThresholdsCode.
Module ScalarTransfer := IntervalCode ZLangCode ThresholdsCode.
Module WordIntervals := IntervalOpsCode ThresholdsCode ScalarCode.
Module Payload := IntervalPayload WordLanguage Thresholds ScalarCode.

(** The interval from zero to zero. *)
Definition point_zero := I (Fin 0) (Fin 0).

(** The interval from zero to one. *)
Definition zero_to_one := I (Fin 0) (Fin 1).

(** The interval consisting of one. *)
Definition point_one := I (Fin 1) (Fin 1).

(** The interval from two to three, which lies outside the one-bit range. *)
Definition point_two_three := I (Fin 2) (Fin 3).

(** The threshold tree with the single threshold ten. *)
Definition threshold_ten := Thresholds.make [10%Z].

(** * Clipping *)

Module ClippingTests.

  (** Clipping an unbounded interval is below itself. *)
  Example clipped_unbounded_interval_is_below_itself :
    Scalar.leb (WordIntervals.interval_clip 1%positive (I NegInf PosInf))
      (WordIntervals.interval_clip 1%positive (I NegInf PosInf)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Clipping a stable raw interval changes its representation. *)
  Example widened_clipped_unbounded_interval_changes :
    WordIntervals.interval_clip 1%positive
      (Scalar.widen TLeaf (WordIntervals.interval_clip 1%positive (I NegInf PosInf))
        (WordIntervals.interval_clip 1%positive (I NegInf PosInf))) <> I NegInf PosInf.
  Proof.
    vm_compute. discriminate.
  Qed.

  (** A clipped point is not bottom. *)
  Example clipped_point_is_not_bottom :
    Scalar.is_bot (WordIntervals.interval_clip 1%positive point_zero) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A clipped interval from zero to one is not below the clipped point zero. *)
  Example clipped_zero_to_one_is_not_below_clipped_point :
    Scalar.leb (WordIntervals.interval_clip 1%positive zero_to_one)
      (WordIntervals.interval_clip 1%positive point_zero) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A clipped point has scalar rank two. *)
  Example clipped_point_has_rank_two :
    Scalar.wrank TLeaf (WordIntervals.interval_clip 1%positive point_zero) = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening to a word boundary can keep the clipped scalar rank unchanged. *)
  Example widened_clipped_point_keeps_rank_two :
    Scalar.wrank TLeaf (WordIntervals.interval_clip 1%positive
      (Scalar.widen TLeaf (WordIntervals.interval_clip 1%positive point_zero)
        (WordIntervals.interval_clip 1%positive zero_to_one))) = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ClippingTests.

(** * Rank *)

Module RankTests.

  (** An infinite lower endpoint has rank two below the threshold zero. *)
  Example infinite_lower_endpoint_has_rank_two :
    Scalar.wrank (Thresholds.make [0%Z]) (I PosInf PosInf) = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening the infinite lower endpoint down to zero leaves rank one. *)
  Example widened_lower_endpoint_has_rank_one :
    Scalar.wrank (Thresholds.make [0%Z])
      (Scalar.widen (Thresholds.make [0%Z]) (I PosInf PosInf) (I (Fin 0) PosInf)) = 1%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RankTests.

(** * Payload widening *)

Module PayloadWideningTests.

  (** Guarded widening retains a stable raw unbounded interval exactly. *)
  Example guarded_widen_keeps_stable_raw_interval :
    Payload.pwiden TLeaf 1%positive (I NegInf PosInf) (I NegInf PosInf) = I NegInf PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A point at the upper unsigned boundary has payload rank one. *)
  Example upper_boundary_point_has_rank_one :
    Payload.pwrank TLeaf 1%positive point_zero = 1%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening the upper endpoint to the unsigned boundary gives the second operand. *)
  Example widening_to_upper_boundary_gives_second_operand :
    Payload.pwiden TLeaf 1%positive point_zero zero_to_one = zero_to_one.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening the upper endpoint to the unsigned boundary removes its payload rank. *)
  Example widened_upper_boundary_has_rank_zero :
    Payload.pwrank TLeaf 1%positive (Payload.pwiden TLeaf 1%positive point_zero zero_to_one) =
      0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A point at one has payload rank one. *)
  Example lower_boundary_point_has_rank_one :
    Payload.pwrank TLeaf 1%positive point_one = 1%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening the lower endpoint to zero gives the second operand. *)
  Example widening_from_lower_boundary_gives_second_operand :
    Payload.pwiden TLeaf 1%positive point_one zero_to_one = zero_to_one.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening the lower endpoint to zero removes its payload rank. *)
  Example widened_lower_boundary_has_rank_zero :
    Payload.pwrank TLeaf 1%positive (Payload.pwiden TLeaf 1%positive point_one zero_to_one) =
      0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A point below a threshold of ten has payload rank two at width two. *)
  Example outside_threshold_point_has_rank_two :
    Payload.pwrank threshold_ten 2%positive point_zero = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening past a threshold beyond the word range clips to the word maximum. *)
  Example widening_past_threshold_clips_to_word_maximum :
    Payload.pwiden threshold_ten 2%positive point_zero zero_to_one = I (Fin 0) (Fin 3).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A threshold beyond the word range clips to the boundary and removes the endpoint rank. *)
  Example widened_past_threshold_has_rank_zero :
    Payload.pwrank threshold_ten 2%positive
      (Payload.pwiden threshold_ten 2%positive point_zero zero_to_one) = 0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PayloadWideningTests.

(** * Payload bounds *)

Module PayloadBoundsTests.

  (** Raw intervals outside the unsigned range behave as bottom under payload inclusion. *)
  Example out_of_range_interval_is_payload_bottom :
    Payload.pis_bot 1%positive point_two_three = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An out-of-range raw interval is below the payload bottom. *)
  Example out_of_range_interval_is_below_payload_bottom :
    Payload.pleb 1%positive point_two_three (Payload.pbot 1%positive) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An out-of-range raw interval is below the payload top. *)
  Example out_of_range_interval_is_below_payload_top :
    Payload.pleb 1%positive point_two_three (Payload.ptop 1%positive) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Payload join discards the out-of-range operand. *)
  Example join_drops_out_of_range_operand :
    Payload.pjoin 1%positive point_two_three point_zero = point_zero.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Payload meet discards the out-of-range operand. *)
  Example meet_drops_out_of_range_operand :
    Payload.pmeet 1%positive point_two_three point_zero = IBot.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PayloadBoundsTests.

(** * Shifts *)

Module ShiftTests.

  (** A negative raw upper shift endpoint takes the constant fallback. *)
  Example shl_negative_upper_shift_gives_constant_fallback :
    ScalarTransfer.shl (I (Fin 0) (Fin 0)) (I (Fin 0) (Fin (-8))) = I (Fin 0) PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Ordered shift endpoints below the cutoff keep a finite result. *)
  Example shl_ordered_endpoints_keep_finite_result :
    ScalarTransfer.shl (I (Fin 1) (Fin 2)) (I (Fin 0) (Fin 1)) = I (Fin 1) (Fin 4).
  Proof.
    vm_compute. reflexivity.
  Qed.

End ShiftTests.
