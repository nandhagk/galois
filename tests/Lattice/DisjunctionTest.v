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

Example disjunction_cap_one :
  proj1_sig (D1.join (D1.clip [FVal false]) (D1.clip [FVal true; FBot])) = [FTop].
Proof. vm_compute. reflexivity. Qed.
Example disjunction_cap_two :
  proj1_sig (D2.join (D2.clip [FVal false]) (D2.clip [FVal true; FBot])) =
    [FVal false; FVal true].
Proof. vm_compute. reflexivity. Qed.
Example disjunction_negative : D2.leb (D2.clip [FVal true]) (D2.clip [FVal false]) = false.
Proof. vm_compute. reflexivity. Qed.
Example disjunction_empty : (proj1_sig (D0.join D0.bot D0.bot), D0.leb D0.bot D0.bot) =
  ([], true).
Proof. vm_compute. reflexivity. Qed.
Example disjunction_cap_zero : proj1_sig (D0.clip [FVal false]) = [].
Proof. vm_compute. reflexivity. Qed.
Example disjunction_empty_right : D1.leb (D1.clip [FBot]) D1.bot = false.
Proof. vm_compute. reflexivity. Qed.
Example selective_leastness :
  BoolDisjunction.leb (BoolDisjunction.join (BoolDisjunction.clip [false])
    (BoolDisjunction.clip [true])) (BoolDisjunction.clip [false; true]) = true.
Proof. vm_compute. reflexivity. Qed.
Example disjunction_bottom_test : (D1.is_bot D1.bot, D1.is_bot (D1.clip [FBot])) =
  (true, false).
Proof. vm_compute. reflexivity. Qed.

(* At cap zero the old raw join [FVal false] [] returned [FVal false].
   That input is outside the bounded carrier, and clipping it now returns [].
   The old cap-one nonleast counterexample used a two-element right operand,
   which also lies outside the carrier. The old raw widening examples belong
   to the D1 state-disjunction component. Cost.ticks examples are retired. *)
