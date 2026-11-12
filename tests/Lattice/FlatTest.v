(** * Flat fixtures

    Flat booleans distinguish two incomparable known values.
    For example, their join is top even though neither covers the other.
    Builds on: Flat. *)

From Stdlib Require Import Bool NArith.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import Flat.

Module FlatBool := FlatCode BoolKeyCode.

Example flat_positive : FlatBool.join (FVal true) (FVal true) = FVal true.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_negative : FlatBool.leb (FVal true) (FVal false) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_bottom : FlatBool.join FBot FBot = FBot.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_top_absorbs : FlatBool.join (FVal false) FTop = FTop.
Proof.
  vm_compute; reflexivity.
Qed.

(* Cost and height examples are in LatticeFlatTest.v at 87192fe. *)
