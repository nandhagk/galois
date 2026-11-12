(** * Reduced product fixtures

    These examples check a reducer that clears the second boolean slot.
    For example, reducing [(false, true)] produces [(false, false)].
    Builds on: Reduced and Simple. *)

From Stdlib Require Import Bool.
From Galois.Lattice Require Import Reduced Simple.

Module ClearSecond.
  Definition reduce (x : bool * bool) := (fst x, andb (fst x) (snd x)).
End ClearSecond.
Module ClearTwice.
  Definition step (x : bool * bool) := (andb (fst x) (snd x), false).
  Definition reduce (x : bool * bool) := step (step x).
End ClearTwice.
Module ReducedBool := ReducedCode BoolLatCode BoolLatCode ClearSecond.

Example reduce_positive :
  (ClearSecond.reduce (false, true), ClearTwice.reduce (true, true)) =
    ((false, false), (false, false)).
Proof. vm_compute. reflexivity. Qed.
Example reduce_negative :
  (ReducedBool.leb (false, true) (false, false),
    ReducedBool.leb (true, true) (false, false)) = (true, false).
Proof. vm_compute. reflexivity. Qed.
Example reduced_join_is_not_an_exact_slot :
  (snd (ReducedBool.join (false, true) (false, false)), BoolLatCode.join true false) =
    (false, true).
Proof. vm_compute. reflexivity. Qed.
Example reduced_join_needs_compatibility :
  (ReducedBool.leb (true, false) (true, false),
    ReducedBool.leb (false, true) (true, false),
    ReducedBool.leb (ReducedBool.join (true, false) (false, true)) (true, false)) =
    (true, true, false).
Proof. vm_compute. reflexivity. Qed.

(* Round counts, height, cost and symbolic law examples are in LatticeReducedTest.v at 87192fe. *)
