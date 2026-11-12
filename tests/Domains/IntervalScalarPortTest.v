(** * Fixed-width interval operations

    These examples exercise clipping, arithmetic and comparisons.
    For example, clipping at width one retains the interval from zero to one.
    Builds on: IntervalOps IntervalBack BitsLang Tagged Harness WordSig. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import ValueSig IntervalSig Thresholds ThresholdsSig Interval IntervalOps IntervalBack BitsLang Tagged Harness WordSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Scalar := IntervalBaseCode ThresholdsCode.
Module Ops := IntervalOpsCode ThresholdsCode Scalar.
Import Ops.
Module Payload := IntervalPayloadCode WordLanguageCode ThresholdsCode Scalar.
Module PayloadPlain := IntervalPayload WordLanguage Thresholds Scalar.
Module Table := IntervalWordTableCode WordLanguageCode ThresholdsCode Scalar Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.
Definition interval_back o xs rw q :=
  map (fun a => match a with TBot => IBot | TVal _ p => p | TAny => Payload.ptop rw end)
    (Domain.backward (BOp o) (TVal rw q) (map (fun wp => TVal (fst wp) (snd wp)) xs)).
Definition interval_fwd o xs rw :=
  match Domain.forward (BOp o) (map (fun wp => TVal (fst wp) (snd wp)) xs) with
  | TBot => IBot | TVal _ p => p | TAny => Payload.ptop rw
  end.
Example interval_operand_clip :
  interval_clip 8%positive (I NegInf PosInf) = I (Fin 0) (Fin 255).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_one_bit_clip :
  interval_clip 1%positive (I (Fin (-1)) (Fin 2)) = I (Fin 0) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_add_in_range :
  interval_add 8%positive (I (Fin 1) (Fin 4)) (I (Fin 2) (Fin 5)) =
  I (Fin 3) (Fin 9).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_add_wrap_fallback :
  interval_add 8%positive (I (Fin 250) (Fin 255)) (I (Fin 1) (Fin 2)) =
  I (Fin 0) (Fin 255).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_arithmetic_bottom_fallback :
  interval_add 1%positive IBot (I (Fin 0) (Fin 1)) = I (Fin 0) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_comparison :
  interval_assume_ult (I (Fin 0) (Fin 20)) (I (Fin 5) (Fin 10)) =
  (I (Fin 0) (Fin 9), I (Fin 5) (Fin 10)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_comparison_decided :
  interval_ult (I (Fin 0) (Fin 3)) (I (Fin 5) (Fin 10)) = I (Fin 1) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_comparison_overlap :
  interval_ult (I (Fin 0) (Fin 10)) (I (Fin 5) (Fin 10)) = I (Fin 0) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_comparison_equal_singletons :
  interval_eq (I (Fin 1) (Fin 1)) (I (Fin 1) (Fin 1)) = I (Fin 1) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_udiv_zero :
  interval_udiv 8%positive (I (Fin 1) (Fin 3)) (I (Fin 0) (Fin 0)) =
  I (Fin 255) (Fin 255).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_urem_constant_quotient :
  interval_urem 4%positive (I (Fin 5) (Fin 5)) (I (Fin 2) (Fin 2)) =
  I (Fin 1) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_add_inverse :
  interval_assume_add 8%positive (I (Fin 0) (Fin 10)) (I (Fin 2) (Fin 2))
    (I (Fin 5) (Fin 7)) = (I (Fin 3) (Fin 5), I (Fin 2) (Fin 2)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_sub_inverse :
  interval_assume_sub (I (Fin 5) (Fin 10)) (I (Fin 2) (Fin 2))
    (I (Fin 4) (Fin 5)) = (I (Fin 6) (Fin 7), I (Fin 2) (Fin 2)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_resize_operand_width :
  interval_assume_rewrap 4%positive (I (Fin 0) (Fin 10)) (I (Fin 3) (Fin 5)) =
  I (Fin 3) (Fin 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_and_mask :
  interval_and 8%positive (I (Fin 240) (Fin 255)) (I (Fin 15) (Fin 15)) =
  I (Fin 0) (Fin 15).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_or_xor_mask :
  interval_or_xor 8%positive (I (Fin 1) (Fin 2)) (I (Fin 4) (Fin 4)) =
  I (Fin 0) (Fin 7).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_complement :
  interval_not 8%positive (I (Fin 250) (Fin 255)) = I (Fin 0) (Fin 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_bitwise_empty_scalar_fallback :
  interval_and 1%positive IBot (I (Fin 1) (Fin 1)) = I (Fin 0) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_neq_singleton :
  interval_assume_neq (I (Fin 0) (Fin 0)) (I (Fin 0) (Fin 0)) = (IBot, IBot).
Proof.
  vm_compute. reflexivity.
Qed.


Example interval_signed_mod_singletons :
  interval_fwd bvsmod [(8%positive, I (Fin 251) (Fin 251));
                       (8%positive, I (Fin 3) (Fin 3))] 8%positive = I (Fin 1) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_mod_positive_divisor :
  interval_fwd bvsmod [(8%positive, I (Fin 251) (Fin 252));
                       (8%positive, I (Fin 2) (Fin 3))] 8%positive = I (Fin 0) (Fin 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_shift :
  interval_fwd bvashr [(8%positive, I (Fin 248) (Fin 252));
                       (8%positive, I (Fin 1) (Fin 2))] 8%positive =
  I (Fin 252) (Fin 255).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_division_zero_and_minimum :
  (interval_fwd bvsdiv [(8%positive, I (Fin 128) (Fin 129));
                        (8%positive, I (Fin 0) (Fin 1))] 8%positive,
    interval_fwd bvsdiv [(8%positive, I (Fin 128) (Fin 129));
                         (8%positive, I (Fin 255) (Fin 255))] 8%positive) =
  (I (Fin 1) (Fin 129), I (Fin 127) (Fin 128)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_shift_saturation :
  (interval_fwd bvashr [(8%positive, I (Fin 248) (Fin 252));
                        (8%positive, I (Fin 7) (Fin 8))] 8%positive,
    interval_fwd bvashr [(8%positive, I (Fin 2) (Fin 4));
                         (8%positive, I (Fin 8) (Fin 9))] 8%positive) =
  (I (Fin 255) (Fin 255), I (Fin 0) (Fin 0)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_remainder_precision_gap :
  (interval_fwd bvsrem [(8%positive, I (Fin 5) (Fin 5));
                        (8%positive, I (Fin 2) (Fin 3))] 8%positive,
    eval_op bvsrem [(8%positive, 5); (8%positive, 2)],
    eval_op bvsrem [(8%positive, 5); (8%positive, 3)]) =
  (I (Fin 0) (Fin 2), Some (8%positive, 1), Some (8%positive, 2)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_forward_clips_operand :
  interval_fwd bvadd [(8%positive, I NegInf (Fin 3));
                      (8%positive, I (Fin 2) (Fin 4))] 8%positive =
  I (Fin 2) (Fin 7).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_forward_empty :
  interval_fwd bvadd [(8%positive, IBot); (8%positive, I NegInf PosInf)] 8%positive = IBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_unsigned_false :
  interval_back bvult [(8%positive, I (Fin 0) (Fin 20));
                       (8%positive, I (Fin 5) (Fin 10))] 1%positive
    (I (Fin 0) (Fin 0)) = [I (Fin 5) (Fin 20); I (Fin 5) (Fin 10)].
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_popcnt_point :
  interval_fwd bvpopcnt [(1%positive, I (Fin 0) (Fin 0))] 1%positive =
  I (Fin 0) (Fin 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_ite_forward :
  interval_fwd bvite
    [(1%positive, I (Fin 0) (Fin 1)); (8%positive, I (Fin 2) (Fin 4));
     (8%positive, I (Fin 11) (Fin 12))] 8%positive = I (Fin 2) (Fin 12).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_backward_resize_operand_width :
  interval_back (bvtrunc 4%positive) [(8%positive, I (Fin 0) (Fin 10))] 4%positive
    (I (Fin 3) (Fin 5)) = [I (Fin 3) (Fin 5)].
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_invalid_width_point_rejected :
  interval_fwd bvadd [(1%positive, I (Fin 0) (Fin 0));
                      (4%positive, I (Fin 1) (Fin 1))] 1%positive = IBot.
Proof.
  vm_compute. reflexivity.
Qed.


Example interval_hull :
  Scalar.interval_join (I (Fin 1) (Fin 3)) (I (Fin 2) (Fin 5)) = I (Fin 1) (Fin 5).
Proof. vm_compute. reflexivity. Qed.

Example interval_thresholds :
  Scalar.interval_stable_widen (ThresholdsCode.make [0; 10; 20])
    (I (Fin 2) (Fin 4)) (I (Fin 1) (Fin 12)) = I (Fin 0) (Fin 20).
Proof. vm_compute. reflexivity. Qed.

Example interval_narrow_infinities :
  Scalar.interval_narrow (I NegInf PosInf) (I (Fin 0) (Fin 8)) = I (Fin 0) (Fin 8).
Proof. vm_compute. reflexivity. Qed.

Example interval_unsorted_thresholds :
  Scalar.interval_stable_widen (ThresholdsCode.make [20; 0; 10; 10])
    (I (Fin 8) (Fin 9)) (I (Fin 7) (Fin 11)) = I (Fin 0) (Fin 20).
Proof. vm_compute. reflexivity. Qed.

Example interval_sorted_threshold_index :
  ThresholdsCode.make [1; 2; 3] = TNode (TNode TLeaf 1 TLeaf) 2 (TNode TLeaf 3 TLeaf).
Proof. vm_compute. reflexivity. Qed.

Example interval_threshold_infinity :
  Scalar.interval_stable_widen (ThresholdsCode.make [0; 10])
    (I (Fin 0) (Fin 10)) (I (Fin (-1)) (Fin 11)) = I NegInf PosInf.
Proof. vm_compute. reflexivity. Qed.

Example interval_empty_meet :
  Scalar.interval_meet (I (Fin 1) (Fin 2)) (I (Fin 3) (Fin 4)) = IBot.
Proof. vm_compute. reflexivity. Qed.

Example interval_infinite_empty_meet :
  (Scalar.interval_meet (I PosInf PosInf) (I NegInf PosInf),
   Scalar.interval_meet (I NegInf NegInf) (I NegInf PosInf)) = (IBot, IBot).
Proof. vm_compute. reflexivity. Qed.

Example interval_duplicate_threshold_index :
  ThresholdsCode.make [10; 10; 10] = TNode TLeaf 10 TLeaf.
Proof. vm_compute. reflexivity. Qed.

Example interval_rank_prepared_duplicates :
  PayloadPlain.pwrank (ThresholdsCode.make [0; 0; 5]) 8%positive
    (I (Fin 1) (Fin 3)) = 4%nat.
Proof. vm_compute. reflexivity. Qed.

Definition interval_malformed_backward_inputs : list (list (width * itv)) :=
  [[]; [(8%positive, I NegInf PosInf)];
   [(1%positive, I NegInf PosInf); (4%positive, I (Fin (-3)) (Fin 20));
    (8%positive, I PosInf PosInf)]].

(* Old results clip each input as shown below. Current results are
   [([], true, true); ([I NegInf PosInf], true, true);
    ([I NegInf PosInf; I (Fin (-3)) (Fin 20); I PosInf PosInf], true, true)].
Example interval_backward_malformed_fallback_count_and_refinement :
  map (fun xs =>
    let ys := interval_back bvadd xs 1%positive (I (Fin 1) (Fin 1)) in
    (ys, Nat.eqb (length ys) (length xs),
     forallb (fun p => Payload.pleb (fst (fst p)) (snd p) (snd (fst p))) (combine xs ys)))
    interval_malformed_backward_inputs =
  [([], true, true); ([I (Fin 0) (Fin 255)], true, true);
   ([I (Fin 0) (Fin 1); I (Fin 0) (Fin 15); IBot], true, true)].
Proof. vm_compute. reflexivity. Qed.

*)

Example interval_backward_malformed_preserves_raw_inputs :
  map (fun xs => interval_back bvadd xs 1%positive (I (Fin 1) (Fin 1)))
    interval_malformed_backward_inputs =
  [[]; [I NegInf PosInf]; [I NegInf PosInf; I (Fin (-3)) (Fin 20); I PosInf PosInf]].
Proof. vm_compute. reflexivity. Qed.
