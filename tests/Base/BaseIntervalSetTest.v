(** * Integer interval set examples

    These examples exercise the interval set observations.
    For example, a range includes its lower endpoint and excludes its upper endpoint.
    Builds on: BaseIntervalSet and Cost. *)

From Stdlib Require Import ZArith List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseIntervalSet.
Import List.ListNotations.

Local Open Scope Z_scope.

Example singleton_negative :
  IntervalSet.singleton (-3, 2) = [(-3, 2)].
Proof. vm_compute. reflexivity. Qed.

Example singleton_reversed :
  IntervalSet.singleton (2, -3) = [].
Proof. vm_compute. reflexivity. Qed.

Example singleton_empty :
  IntervalSet.singleton (2, 2) = [].
Proof. vm_compute. reflexivity. Qed.

Example mem_lower_endpoint :
  IntervalSet.mem [(-3, 2)] (-3) = true.
Proof. vm_compute. reflexivity. Qed.

Example mem_upper_endpoint :
  IntervalSet.mem [(-3, 2)] 2 = false.
Proof. vm_compute. reflexivity. Qed.

Example mem_gap :
  IntervalSet.mem [(-3, 2); (4, 6)] 3 = false.
Proof. vm_compute. reflexivity. Qed.

Example mem_second_cost :
  Cost.ticks (IntervalSet.mem_c [(-3, 2); (4, 6)] 4) = 2%N.
Proof. vm_compute. reflexivity. Qed.

Example empty_observation : IntervalSet.is_empty IntervalSet.empty = true.
Proof. vm_compute. reflexivity. Qed.

Example nonempty_cost :
  Cost.ticks (IntervalSet.is_empty_c [(1, 3)]) = 1%N.
Proof. vm_compute. reflexivity. Qed.

Example union_adjacent :
  IntervalSet.union [(0, 2)] [(2, 4)] = [(0, 4)].
Proof. vm_compute. reflexivity. Qed.

Example union_overlap_negative :
  IntervalSet.union [(-8, -2); (4, 7)] [(-4, 5)] = [(-8, 7)].
Proof. vm_compute. reflexivity. Qed.

Example union_gap :
  IntervalSet.union [(-5, -2)] [(0, 2)] = [(-5, -2); (0, 2)].
Proof. vm_compute. reflexivity. Qed.

Example union_empty_left :
  IntervalSet.union [] [(1, 3)] = [(1, 3)].
Proof. vm_compute. reflexivity. Qed.

Example union_empty_right :
  IntervalSet.union [(1, 3)] [] = [(1, 3)].
Proof. vm_compute. reflexivity. Qed.

Example union_cost :
  Cost.ticks (IntervalSet.union_c [(0, 2)] [(2, 4)]) = 3%N.
Proof. vm_compute. reflexivity. Qed.

Example add_bridges :
  IntervalSet.add (2, 4) [(0, 2); (4, 6)] = [(0, 6)].
Proof. vm_compute. reflexivity. Qed.

Example add_reversed :
  IntervalSet.add (5, -5) [(0, 2)] = [(0, 2)].
Proof. vm_compute. reflexivity. Qed.

Example diff_split :
  IntervalSet.diff [(0, 8)] [(3, 5)] = [(0, 3); (5, 8)].
Proof. vm_compute. reflexivity. Qed.

Example diff_split_cost :
  Cost.ticks (IntervalSet.diff_c [(0, 8)] [(3, 5)]) = 2%N.
Proof. vm_compute. reflexivity. Qed.

Example diff_across_ranges :
  IntervalSet.diff [(-5, 0); (2, 8)] [(-3, 4)] = [(-5, -3); (4, 8)].
Proof. vm_compute. reflexivity. Qed.

Example diff_empty :
  IntervalSet.diff [] [(0, 1)] = [].
Proof. vm_compute. reflexivity. Qed.

Example diff_remove_all :
  IntervalSet.diff [(-2, 3)] [(-5, 5)] = [].
Proof. vm_compute. reflexivity. Qed.

Example remove_split :
  IntervalSet.remove (0, 2) [(-2, 4)] = [(-2, 0); (2, 4)].
Proof. vm_compute. reflexivity. Qed.

Example remove_empty :
  IntervalSet.remove (1, 1) [(-2, 4)] = [(-2, 4)].
Proof. vm_compute. reflexivity. Qed.

Example inter_overlap :
  IntervalSet.inter [(-4, 2); (5, 9)] [(-2, 7)] = [(-2, 2); (5, 7)].
Proof. vm_compute. reflexivity. Qed.

Example inter_adjacent :
  IntervalSet.inter [(0, 2)] [(2, 4)] = [].
Proof. vm_compute. reflexivity. Qed.

Example subset_true :
  IntervalSet.subset [(0, 2); (4, 5)] [(-1, 6)] = true.
Proof. vm_compute. reflexivity. Qed.

Example subset_false :
  IntervalSet.subset [(0, 3)] [(0, 2)] = false.
Proof. vm_compute. reflexivity. Qed.

Example subset_empty :
  IntervalSet.subset [] [] = true.
Proof. vm_compute. reflexivity. Qed.

Example covers_true :
  IntervalSet.covers [(-4, 3)] (-2, 3) = true.
Proof. vm_compute. reflexivity. Qed.

Example covers_gap :
  IntervalSet.covers [(0, 2); (3, 5)] (1, 4) = false.
Proof. vm_compute. reflexivity. Qed.

Example covers_reversed :
  IntervalSet.covers [] (3, -1) = true.
Proof. vm_compute. reflexivity. Qed.

Example intersects_true :
  IntervalSet.intersects [(-4, 3)] (2, 5) = true.
Proof. vm_compute. reflexivity. Qed.

Example intersects_at_exclusive_end :
  IntervalSet.intersects [(0, 2)] (2, 4) = false.
Proof. vm_compute. reflexivity. Qed.

Example intersects_reversed :
  IntervalSet.intersects [(0, 5)] (3, 1) = false.
Proof. vm_compute. reflexivity. Qed.

Example elements_order :
  IntervalSet.elements [(-4, -1); (2, 6)] = [(-4, -1); (2, 6)].
Proof. vm_compute. reflexivity. Qed.
