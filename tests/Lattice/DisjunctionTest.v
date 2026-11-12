(** * Disjunction fixtures

    Capped joins combine flat alternatives.
    For example, cap one collapses incomparable values to top.
    Builds on: Disjunction, Flat and Key. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import Disjunction Flat.
Import List.ListNotations.

Module FlatBool := FlatCode BoolKeyCode.
Module FlatWide.
  Include FlatBool.
  Definition wparam := unit.
  Definition widen (_ : wparam) := join.
  Definition narrow (x _ : t) := x.
End FlatWide.
Module Cap0. Definition k := 0. End Cap0.
Module Cap1. Definition k := 1. End Cap1.
Module Cap2. Definition k := 2. End Cap2.
Module D0 := DisjunctionCode FlatWide Cap0.
Module D1 := DisjunctionCode FlatWide Cap1.
Module D2 := DisjunctionCode FlatWide Cap2.

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
Example disjunction_empty : (D0.join [] [], D0.leb [] [], D0.widen tt [] []) = ([], true, []).
Proof. vm_compute. reflexivity. Qed.
Example disjunction_cap_zero : D0.join [FVal false] [] = [FVal false].
Proof. vm_compute. reflexivity. Qed.
Example disjunction_empty_right : D1.leb [FBot] [] = false.
Proof. vm_compute. reflexivity. Qed.
Example disjunction_collapse : D2.widen tt [FVal false] [FVal true] = [FTop].
Proof. vm_compute. reflexivity. Qed.
Example disjunction_covered : D2.widen tt [FTop; FVal true] [FVal false] = [FTop; FVal true].
Proof. vm_compute. reflexivity. Qed.

(* Cost, height and symbolic law examples are in LatticeDisjunctionTest.v at 87192fe. *)

Example disjunction_bottom_test : (D1.is_bot [], D1.is_bot [FBot]) = (true, false).
Proof. vm_compute. reflexivity. Qed.
