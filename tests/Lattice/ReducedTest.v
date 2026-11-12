(** * Reduced product fixtures

    These examples check a reducer that clears the second boolean slot.
    For example, reducing [(false, true)] produces [(false, false)].
    Builds on: Reduced and Simple. *)

From Stdlib Require Import Bool.
From Galois.Lattice Require Import Reduced Simple JoinWidening.

Module ClearSecond.
  Definition reduce (x : bool * bool) := (fst x, andb (fst x) (snd x)).
End ClearSecond.
Module ClearTwice.
  Definition step (x : bool * bool) := (andb (fst x) (snd x), false).
  Definition reduce (x : bool * bool) := step (step x).
End ClearTwice.
Module ReducedBool := ReducedCode BoolLatCode BoolLatCode ClearSecond.
Module ReducedWide := JoinWideningCode ReducedBool.

Example reduce_positive :
  (ClearSecond.reduce (false, true), ClearTwice.reduce (true, true)) =
    ((false, false), (false, false)).
Proof. vm_compute. reflexivity. Qed.
Example reduce_negative :
  (ReducedBool.leb (false, true) (false, false),
    ReducedBool.leb (true, true) (false, false)) = (true, false).
Proof. vm_compute. reflexivity. Qed.
Example reduced_narrow :
  ReducedWide.narrow (true, true) (false, true) = (true, true).
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

(* The old reduced widening of (false, true) and (false, false) returned (false, true).
   JoinWideningCode widens by ReducedBool.join and returns (false, false).
   The reducer interface has no round count. The old reduced height ranked (false, true)
   and (true, true) as 0 and 2. No reduced height combinator is exported. *)
