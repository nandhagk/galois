(** * Disjunction fixtures

    Capped joins combine flat alternatives.
    For example, cap one collapses incomparable values to top.
    Builds on: Disjunction, Flat and Key. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import Disjunction Flat Simple.
Import List.ListNotations.

Module FlatBool := FlatCode BoolKeyCode.
Module Cap0. Definition k := 0. End Cap0.
Module Cap1. Definition k := 1. End Cap1.
Module Cap2. Definition k := 2. End Cap2.
Module D0 := DisjunctionCode FlatBool Cap0.
Module D1 := DisjunctionCode FlatBool Cap1.
Module D2 := DisjunctionCode FlatBool Cap2.
Module BoolDisjunction := DisjunctionCode BoolLatCode Cap1.

Example disjunction_cap_one : D1.join [FVal false] [FVal true; FBot] = [FTop].
Proof. vm_compute. reflexivity. Qed.
Example disjunction_cap_two : D2.join [FVal false] [FVal true; FBot] = [FVal false; FVal true].
Proof. vm_compute. reflexivity. Qed.
Example disjunction_nonleast_counterexample :
  (D1.leb [FVal false] [FVal false; FVal true],
   D1.leb [FVal true] [FVal false; FVal true],
   D1.leb (D1.join [FVal false] [FVal true]) [FVal false; FVal true]) = (true, true, false).
Proof. vm_compute. reflexivity. Qed.
Example disjunction_negative : D2.leb [FVal true] [FVal false] = false.
Proof. vm_compute. reflexivity. Qed.
Example disjunction_empty : (D0.join [] [], D0.leb [] []) = ([], true).
Proof. vm_compute. reflexivity. Qed.
Example disjunction_cap_zero : D0.join [FVal false] [] = [FVal false].
Proof. vm_compute. reflexivity. Qed.
Example disjunction_empty_right : D1.leb [FBot] [] = false.
Proof. vm_compute. reflexivity. Qed.
(* The old raw-list widening examples are deferred to the D1 state-disjunction
   component. Their prior expected values were [FTop] for
   D2.widen tt [FVal false] [FVal true] and [FTop; FVal true] for
   D2.widen tt [FTop; FVal true] [FVal false]. The empty case expected
   D0.widen tt [] [] = []. *)

Example selective_leastness :
  BoolDisjunction.leb (BoolDisjunction.join [false] [true]) [false; true] = true.
Proof.
  vm_compute. reflexivity.
Qed.

(* LatticeDisjunctionTest.disjunction_measure_client expects (3, 3, 0) from
   disjunction_wrank on [false; false] and its widening by [true]. DisjunctionCode
   exports operations without a rank or bound, and there is no public disjunction
   height or widening-rank adapter. The old invariant-guarded wrank dictionary
   has no counterpart in this interface.
   disjunction_empty_costs, disjunction_leb_ticks, disjunction_join_ticks,
   fixed_cap_long_tail and widening_callback_ticks retire with Cost.ticks.
   bool_join_selective and selective_disjunction_client are proof clients of the
   retired lub_laws dictionary. The concrete selective_leastness is checked above. *)

Example disjunction_bottom_test : (D1.is_bot [], D1.is_bot [FBot]) = (true, false).
Proof. vm_compute. reflexivity. Qed.
