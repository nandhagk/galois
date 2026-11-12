(** * Interval review witnesses

    These examples check raw endpoints and word boundary clipping.
    For example, clipping an unbounded interval at width one gives [0, 1].
    Builds on: Interval, IntervalOps, Thresholds and ZLang. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import ValueSig IntervalSig Interval IntervalOps ThresholdsSig
  Thresholds ZLang.
Import List.ListNotations.

Module Scalar := Interval ZLang Thresholds.
Module WordIntervals := IntervalOpsCode ThresholdsCode.

(** A lower endpoint at positive infinity has room to decrease to a threshold. *)
Example wrong_side_infinity_rank :
  Scalar.wrank (Thresholds.make [0%Z]) (I PosInf PosInf) = 2%nat /\
  Scalar.wrank (Thresholds.make [0%Z])
    (Scalar.widen (Thresholds.make [0%Z]) (I PosInf PosInf) (I (Fin 0) PosInf)) = 1%nat.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Clipping a stable raw interval changes its representation. *)
Example clipped_stable_raw_changes :
  Scalar.leb (WordIntervals.interval_clip 1%positive (I NegInf PosInf))
    (WordIntervals.interval_clip 1%positive (I NegInf PosInf)) = true /\
  WordIntervals.interval_clip 1%positive
    (Scalar.widen TLeaf (WordIntervals.interval_clip 1%positive (I NegInf PosInf))
      (WordIntervals.interval_clip 1%positive (I NegInf PosInf))) <> I NegInf PosInf.
Proof.
  vm_compute. split; [reflexivity | discriminate].
Qed.

(** Widening to a word boundary can keep the clipped scalar rank unchanged. *)
Example clipped_widening_rank_unchanged :
  let a := I (Fin 0) (Fin 0) in
  let b := I (Fin 0) (Fin 1) in
  Scalar.is_bot (WordIntervals.interval_clip 1%positive a) = false /\
  Scalar.leb (WordIntervals.interval_clip 1%positive b) (WordIntervals.interval_clip 1%positive a) = false /\
  Scalar.wrank TLeaf (WordIntervals.interval_clip 1%positive a) = 2%nat /\
  Scalar.wrank TLeaf (WordIntervals.interval_clip 1%positive
    (Scalar.widen TLeaf (WordIntervals.interval_clip 1%positive a)
      (WordIntervals.interval_clip 1%positive b))) = 2%nat.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.
