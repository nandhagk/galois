(** * Linear interval traversal envelopes

    A common constant bounds the charged traversals on all finite range lists.
    For example, splitting one range during removal remains linear in the original ranges.
    Builds on: BaseIntervalSet's traversal and output-length theorems. *)

From Stdlib Require Import List ZArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseIntervalSet.

Module IntervalSetCost.

(** This constant covers both differences used by intersection and all derived operations. *)
Definition interval_k : N := 8.

(** Membership is linear in the number of ranges inspected. *)
Theorem mem_cost xs b :
  (Cost.ticks (IntervalSet.mem_c xs b) <= interval_k * (1 + N.of_nat (length xs)))%N.
Proof.
  pose proof (IntervalSet.mem_cost xs b) as Hcost. unfold interval_k. lia.
Qed.

(** Addition includes the singleton and the coalescing traversal. *)
Theorem add_cost r xs :
  (Cost.ticks (IntervalSet.add_c r xs) <= interval_k * (1 + N.of_nat (length xs)))%N.
Proof.
  pose proof (IntervalSet.add_cost r xs) as Hcost. unfold interval_k. lia.
Qed.

(** Removal includes both fragments of a split interval. *)
Theorem remove_cost r xs :
  (Cost.ticks (IntervalSet.remove_c r xs) <= interval_k * (1 + N.of_nat (length xs)))%N.
Proof.
  pose proof (IntervalSet.remove_cost r xs) as Hcost. unfold interval_k. lia.
Qed.

(** Union's merge and coalescing passes are linear in the two input lengths. *)
Theorem union_cost xs ys :
  (Cost.ticks (IntervalSet.union_c xs ys) <=
    interval_k * (1 + N.of_nat (length xs) + N.of_nat (length ys)))%N.
Proof.
  pose proof (IntervalSet.union_cost xs ys) as Hcost.
  rewrite Nat2N.inj_add in Hcost. unfold interval_k. lia.
Qed.

(** Intersection's intermediate split output remains bounded by the original input lengths. *)
Theorem inter_cost xs ys :
  (Cost.ticks (IntervalSet.inter_c xs ys) <=
    interval_k * (1 + N.of_nat (length xs) + N.of_nat (length ys)))%N.
Proof.
  pose proof (IntervalSet.inter_cost xs ys) as Hcost. unfold interval_k. lia.
Qed.

(** Difference charges left-range visits and consumed right ranges without restarting a stream. *)
Theorem diff_cost xs ys :
  (Cost.ticks (IntervalSet.diff_c xs ys) <=
    interval_k * (1 + N.of_nat (length xs) + N.of_nat (length ys)))%N.
Proof.
  pose proof (IntervalSet.diff_cost xs ys) as Hcost. unfold interval_k. lia.
Qed.

(** Subset includes the final emptiness observation. *)
Theorem subset_cost xs ys :
  (Cost.ticks (IntervalSet.subset_c xs ys) <=
    interval_k * (1 + N.of_nat (length xs) + N.of_nat (length ys)))%N.
Proof.
  pose proof (IntervalSet.subset_cost xs ys) as Hcost. unfold interval_k. lia.
Qed.

(** Coverage is linear even for empty or inverted query intervals. *)
Theorem covers_cost xs r :
  (Cost.ticks (IntervalSet.covers_c xs r) <= interval_k * (1 + N.of_nat (length xs)))%N.
Proof.
  pose proof (IntervalSet.covers_cost xs r) as Hcost. unfold interval_k. lia.
Qed.

(** Intersection queries have the same linear envelope as coverage queries. *)
Theorem intersects_cost xs r :
  (Cost.ticks (IntervalSet.intersects_c xs r) <= interval_k * (1 + N.of_nat (length xs)))%N.
Proof.
  pose proof (IntervalSet.intersects_cost xs r) as Hcost. unfold interval_k. lia.
Qed.

End IntervalSetCost.
