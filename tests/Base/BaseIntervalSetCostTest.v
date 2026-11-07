(** * Interval traversal cost fixtures

    These counts exercise coalescing, splits, rejected membership and empty inputs.
    For example, removing a middle range keeps both boundary fragments.
    Builds on: BaseIntervalSetCost. *)

From Stdlib Require Import List ZArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseIntervalSet BaseIntervalSetCost.
Import List.ListNotations.
Local Open Scope Z_scope.

Example interval_coalescing_ticks :
  (IntervalSet.add (2, 4) [(0, 2); (4, 6)],
    Cost.ticks (IntervalSet.add_c (2, 4) [(0, 2); (4, 6)])) = ([(0, 6)], 5%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_split_ticks :
  (IntervalSet.remove (2, 4) [(0, 6)],
    Cost.ticks (IntervalSet.remove_c (2, 4) [(0, 6)])) = ([(0, 2); (4, 6)], 2%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_miss_ticks :
  (IntervalSet.mem [(0, 2); (4, 6)] 3,
    Cost.ticks (IntervalSet.mem_c [(0, 2); (4, 6)] 3)) = (false, 2%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_empty_ticks :
  (Cost.ticks (IntervalSet.union_c [] []), Cost.ticks (IntervalSet.diff_c [] []),
    Cost.ticks (IntervalSet.inter_c [] []), Cost.ticks (IntervalSet.subset_c [] []),
    Cost.ticks (IntervalSet.covers_c [] (4, 2))) = (0, 0, 0, 0, 0)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_derived_ticks :
  (Cost.ticks (IntervalSet.inter_c [(0, 6)] [(2, 4)]),
    Cost.ticks (IntervalSet.subset_c [(0, 6)] [(2, 4)]),
    Cost.ticks (IntervalSet.covers_c [(0, 6)] (2, 4))) = (5, 3, 2)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example interval_intersects_ticks :
  (Cost.ticks (IntervalSet.intersects_c [(0, 6)] (2, 4)),
    Cost.ticks (IntervalSet.intersects_c [] (4, 2))) = (4, 0)%N.
Proof.
  vm_compute. reflexivity.
Qed.
