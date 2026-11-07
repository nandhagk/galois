(** * Interval lattice boundaries

    These examples exercise hulls, threshold widening, narrowing and empty intersections.
    For example, an outward upper endpoint jumps to the next supplied threshold.
    Builds on: DomainsInterval and DomainsIntervalRank. *)

From Stdlib Require Import ZArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval
  DomainsIntervalRank DomainsIntervalArith DomainsIntervalCompare DomainsIntervalRefine
  DomainsIntervalBitwise DomainsIntervalBack DomainsNumeric.
Import List.ListNotations.
Local Open Scope Z_scope.
Local Abbreviation interval_fwd := (interval_forward ThresholdEmpty).
Local Abbreviation interval_back := (interval_assume ThresholdEmpty).

Example interval_hull :
  join (interval_lattice (threshold_of_list [])) (Itv (Fin 1) (Fin 3))
    (Itv (Fin 2) (Fin 5)) = Itv (Fin 1) (Fin 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_thresholds :
  widen (interval_lattice (threshold_of_list [0; 10; 20])) (Itv (Fin 2) (Fin 4))
    (Itv (Fin 1) (Fin 12)) = Itv (Fin 0) (Fin 20).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_narrow_infinities :
  narrow (interval_lattice (threshold_of_list [])) (Itv NegInf PosInf) (Itv (Fin 0) (Fin 8)) =
  Itv (Fin 0) (Fin 8).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_unsorted_thresholds :
  widen (interval_lattice (threshold_of_list [20; 0; 10; 10])) (Itv (Fin 8) (Fin 9))
    (Itv (Fin 7) (Fin 11)) = Itv (Fin 0) (Fin 20).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_sorted_threshold_index :
  threshold_index [1; 2; 3] =
  ThresholdNode (ThresholdNode ThresholdEmpty 1 ThresholdEmpty) 2
    (ThresholdNode ThresholdEmpty 3 ThresholdEmpty).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_threshold_infinity :
  widen (interval_lattice (threshold_of_list [0; 10])) (Itv (Fin 0) (Fin 10))
    (Itv (Fin (-1)) (Fin 11)) = Itv NegInf PosInf.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_empty_meet :
  interval_meet (Itv (Fin 1) (Fin 2)) (Itv (Fin 3) (Fin 4)) = IBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_infinite_empty_meet :
  (interval_meet (Itv PosInf PosInf) (Itv NegInf PosInf),
    interval_meet (Itv NegInf NegInf) (Itv NegInf PosInf)) = (IBot, IBot).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_rank_counts_duplicates :
  interval_rank [0; 0; 5] (Itv (Fin 1) (Fin 3)) = 5%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_rank_prepared_duplicates :
  wrank (interval_widening_rank_on (threshold_of_list [0; 0; 5]) 8%positive)
    (Itv (Fin 1) (Fin 3)) = 4%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_operand_clip :
  interval_clip 8%positive (Itv NegInf PosInf) = Itv (Fin 0) (Fin 255).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_one_bit_clip :
  interval_clip 1%positive (Itv (Fin (-1)) (Fin 2)) = Itv (Fin 0) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_add_in_range :
  interval_add 8%positive (Itv (Fin 1) (Fin 4)) (Itv (Fin 2) (Fin 5)) =
  Itv (Fin 3) (Fin 9).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_add_wrap_fallback :
  interval_add 8%positive (Itv (Fin 250) (Fin 255)) (Itv (Fin 1) (Fin 2)) =
  Itv (Fin 0) (Fin 255).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_arithmetic_bottom_fallback :
  interval_add 1%positive IBot (Itv (Fin 0) (Fin 1)) = Itv (Fin 0) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_comparison :
  interval_assume_ult (Itv (Fin 0) (Fin 20)) (Itv (Fin 5) (Fin 10)) =
  (Itv (Fin 0) (Fin 9), Itv (Fin 5) (Fin 10)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_comparison_decided :
  interval_ult (Itv (Fin 0) (Fin 3)) (Itv (Fin 5) (Fin 10)) = Itv (Fin 1) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_comparison_overlap :
  interval_ult (Itv (Fin 0) (Fin 10)) (Itv (Fin 5) (Fin 10)) = Itv (Fin 0) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_comparison_equal_singletons :
  interval_eq (Itv (Fin 1) (Fin 1)) (Itv (Fin 1) (Fin 1)) = Itv (Fin 1) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_udiv_zero :
  interval_udiv 8%positive (Itv (Fin 1) (Fin 3)) (Itv (Fin 0) (Fin 0)) =
  Itv (Fin 255) (Fin 255).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_urem_constant_quotient :
  interval_urem 4%positive (Itv (Fin 5) (Fin 5)) (Itv (Fin 2) (Fin 2)) =
  Itv (Fin 1) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_add_inverse :
  interval_assume_add 8%positive (Itv (Fin 0) (Fin 10)) (Itv (Fin 2) (Fin 2))
    (Itv (Fin 5) (Fin 7)) = (Itv (Fin 3) (Fin 5), Itv (Fin 2) (Fin 2)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_sub_inverse :
  interval_assume_sub (Itv (Fin 5) (Fin 10)) (Itv (Fin 2) (Fin 2))
    (Itv (Fin 4) (Fin 5)) = (Itv (Fin 6) (Fin 7), Itv (Fin 2) (Fin 2)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_resize_operand_width :
  interval_assume_rewrap 4%positive (Itv (Fin 0) (Fin 10)) (Itv (Fin 3) (Fin 5)) =
  Itv (Fin 3) (Fin 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_and_mask :
  interval_and 8%positive (Itv (Fin 240) (Fin 255)) (Itv (Fin 15) (Fin 15)) =
  Itv (Fin 0) (Fin 15).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_or_xor_mask :
  interval_or_xor 8%positive (Itv (Fin 1) (Fin 2)) (Itv (Fin 4) (Fin 4)) =
  Itv (Fin 0) (Fin 7).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_complement :
  interval_not 8%positive (Itv (Fin 250) (Fin 255)) = Itv (Fin 0) (Fin 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_bitwise_empty_scalar_fallback :
  interval_and 1%positive IBot (Itv (Fin 1) (Fin 1)) = Itv (Fin 0) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_neq_singleton :
  interval_assume_neq (Itv (Fin 0) (Fin 0)) (Itv (Fin 0) (Fin 0)) = (IBot, IBot).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_lattice_callback_cost :
  Cost.ticks
    (widen_c (interval_lattice (threshold_of_list [0; 10; 20]))
      (Itv (Fin 2) (Fin 4)) (Itv (Fin 1) (Fin 12))) = 1%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_duplicate_threshold_index :
  threshold_index [10; 10; 10] = ThresholdNode ThresholdEmpty 10 ThresholdEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_forward_clips_operand :
  interval_fwd bvadd [(8%positive, Itv NegInf (Fin 3));
                      (8%positive, Itv (Fin 2) (Fin 4))] 8%positive =
  Itv (Fin 2) (Fin 7).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_forward_empty :
  interval_fwd bvadd [(8%positive, IBot); (8%positive, Itv NegInf PosInf)] 8%positive = IBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_assume_unsigned_false :
  interval_back bvult [(8%positive, Itv (Fin 0) (Fin 20));
                       (8%positive, Itv (Fin 5) (Fin 10))] 1%positive
    (Itv (Fin 0) (Fin 0)) = [Itv (Fin 5) (Fin 20); Itv (Fin 5) (Fin 10)].
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_mod_singletons :
  interval_fwd bvsmod [(8%positive, Itv (Fin 251) (Fin 251));
                       (8%positive, Itv (Fin 3) (Fin 3))] 8%positive = Itv (Fin 1) (Fin 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_mod_positive_divisor :
  interval_fwd bvsmod [(8%positive, Itv (Fin 251) (Fin 252));
                       (8%positive, Itv (Fin 2) (Fin 3))] 8%positive = Itv (Fin 0) (Fin 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_shift :
  interval_fwd bvashr [(8%positive, Itv (Fin 248) (Fin 252));
                       (8%positive, Itv (Fin 1) (Fin 2))] 8%positive =
  Itv (Fin 252) (Fin 255).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_division_zero_and_minimum :
  (interval_fwd bvsdiv [(8%positive, Itv (Fin 128) (Fin 129));
                        (8%positive, Itv (Fin 0) (Fin 1))] 8%positive,
    interval_fwd bvsdiv [(8%positive, Itv (Fin 128) (Fin 129));
                         (8%positive, Itv (Fin 255) (Fin 255))] 8%positive) =
  (Itv (Fin 1) (Fin 129), Itv (Fin 127) (Fin 128)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_shift_saturation :
  (interval_fwd bvashr [(8%positive, Itv (Fin 248) (Fin 252));
                        (8%positive, Itv (Fin 7) (Fin 8))] 8%positive,
    interval_fwd bvashr [(8%positive, Itv (Fin 2) (Fin 4));
                         (8%positive, Itv (Fin 8) (Fin 9))] 8%positive) =
  (Itv (Fin 255) (Fin 255), Itv (Fin 0) (Fin 0)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_signed_remainder_precision_gap :
  (interval_fwd bvsrem [(8%positive, Itv (Fin 5) (Fin 5));
                        (8%positive, Itv (Fin 2) (Fin 3))] 8%positive,
    eval_op bvsrem [(8%positive, 5); (8%positive, 2)],
    eval_op bvsrem [(8%positive, 5); (8%positive, 3)]) =
  (Itv (Fin 0) (Fin 2), Some (8%positive, 1), Some (8%positive, 2)).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_popcnt_point :
  interval_fwd bvpopcnt [(1%positive, Itv (Fin 0) (Fin 0))] 1%positive =
  Itv (Fin 0) (Fin 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_ite_uses_prepared_tree :
  pforward (interval_word_domain (threshold_of_list [0; 10; 20])) bvite
    [(1%positive, Itv (Fin 0) (Fin 1)); (8%positive, Itv (Fin 2) (Fin 4));
     (8%positive, Itv (Fin 11) (Fin 12))] 8%positive = Itv (Fin 2) (Fin 12).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_backward_resize_operand_width :
  interval_back (bvtrunc 4%positive) [(8%positive, Itv (Fin 0) (Fin 10))] 4%positive
    (Itv (Fin 3) (Fin 5)) = [Itv (Fin 3) (Fin 5)].
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_invalid_width_point_rejected :
  interval_fwd bvadd [(1%positive, Itv (Fin 0) (Fin 0));
                      (4%positive, Itv (Fin 1) (Fin 1))] 1%positive = IBot.
Proof.
  vm_compute. reflexivity.
Qed.

Local Definition interval_malformed_backward_inputs : list (list (width * interval)) :=
  [[]; [(8%positive, Itv NegInf PosInf)];
   [(1%positive, Itv NegInf PosInf); (4%positive, Itv (Fin (-3)) (Fin 20));
    (8%positive, Itv PosInf PosInf)]].

Example interval_backward_malformed_fallback_count_and_refinement :
  map (fun xs =>
    let ys := interval_back bvadd xs 1%positive (Itv (Fin 1) (Fin 1)) in
    (ys, Nat.eqb (length ys) (length xs),
     forallb (fun p =>
       leb (plat (interval_word_domain ThresholdEmpty) (fst (fst p)))
         (snd p) (snd (fst p))) (combine xs ys)))
    interval_malformed_backward_inputs =
  [([], true, true); ([Itv (Fin 0) (Fin 255)], true, true);
   ([Itv (Fin 0) (Fin 1); Itv (Fin 0) (Fin 15); IBot], true, true)].
Proof.
  vm_compute. reflexivity.
Qed.
