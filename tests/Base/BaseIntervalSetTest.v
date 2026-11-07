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
