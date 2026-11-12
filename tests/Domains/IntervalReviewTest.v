(** * Interval review witnesses

    These examples check raw endpoints and word boundary clipping.
    For example, clipping an unbounded interval at width one gives [0, 1].
    Builds on: Interval, IntervalOps, Thresholds and ZLang. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import ValueSig IntervalSig Interval IntervalOps IntervalBack BitsLang
  ThresholdsSig Thresholds ZLang.
Import List.ListNotations.

Module Scalar := Interval ZLang Thresholds.
Module ScalarCode := IntervalBaseCode ThresholdsCode.
Module WordIntervals := IntervalOpsCode ThresholdsCode ScalarCode.
Module Payload := IntervalPayload WordLanguage Thresholds ScalarCode.

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
  Scalar.leb (WordIntervals.interval_clip 1%positive b)
    (WordIntervals.interval_clip 1%positive a) = false /\
  Scalar.wrank TLeaf (WordIntervals.interval_clip 1%positive a) = 2%nat /\
  Scalar.wrank TLeaf (WordIntervals.interval_clip 1%positive
    (Scalar.widen TLeaf (WordIntervals.interval_clip 1%positive a)
      (WordIntervals.interval_clip 1%positive b))) = 2%nat.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Raw intervals outside the unsigned range behave as bottom under payload inclusion. *)
Example payload_out_of_range_bottom :
  let a := I (Fin 2) (Fin 3) in
  Payload.pis_bot 1%positive a = true /\
  Payload.pleb 1%positive a (Payload.pbot 1%positive) = true /\
  Payload.pleb 1%positive a (Payload.ptop 1%positive) = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Guarded widening retains a stable raw unbounded interval exactly. *)
Example payload_raw_stability :
  Payload.pwiden TLeaf 1%positive (I NegInf PosInf) (I NegInf PosInf) = I NegInf PosInf.
Proof.
  vm_compute. reflexivity.
Qed.

(** Widening the upper endpoint to the unsigned boundary removes its payload rank. *)
Example payload_upper_boundary_rank :
  let a := I (Fin 0) (Fin 0) in
  let b := I (Fin 0) (Fin 1) in
  Payload.pwrank TLeaf 1%positive a = 1%nat /\
  Payload.pwiden TLeaf 1%positive a b = b /\
  Payload.pwrank TLeaf 1%positive (Payload.pwiden TLeaf 1%positive a b) = 0%nat.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Widening the lower endpoint to zero removes its payload rank. *)
Example payload_lower_boundary_rank :
  let a := I (Fin 1) (Fin 1) in
  let b := I (Fin 0) (Fin 1) in
  Payload.pwrank TLeaf 1%positive a = 1%nat /\
  Payload.pwiden TLeaf 1%positive a b = b /\
  Payload.pwrank TLeaf 1%positive (Payload.pwiden TLeaf 1%positive a b) = 0%nat.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** A threshold beyond the word range clips to the boundary and removes the endpoint rank. *)
Example payload_outside_threshold_rank :
  let q := Thresholds.make [10%Z] in
  let a := I (Fin 0) (Fin 0) in
  let b := I (Fin 0) (Fin 1) in
  Payload.pwrank q 2%positive a = 2%nat /\
  Payload.pwiden q 2%positive a b = I (Fin 0) (Fin 3) /\
  Payload.pwrank q 2%positive (Payload.pwiden q 2%positive a b) = 0%nat.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Payload join and meet discard the out-of-range part of raw operands. *)
Example payload_clipped_join_meet :
  let a := I (Fin 2) (Fin 3) in
  let b := I (Fin 0) (Fin 0) in
  Payload.pjoin 1%positive a b = b /\ Payload.pmeet 1%positive a b = IBot.
Proof.
  vm_compute. split; reflexivity.
Qed.
