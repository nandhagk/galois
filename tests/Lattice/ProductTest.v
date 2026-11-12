(** * Product fixtures

    These clients exercise a flat boolean value paired with a boolean fact.
    For example, joining unequal known values produces a flat top coordinate.
    Builds on: Product, Flat and Simple. *)

From Stdlib Require Import Bool NArith.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import Product Flat Simple.

Module FlatBool := FlatCode BoolKeyCode.
Module PairFixture := ProductCode FlatBool BoolLatCode.

Example product_positive :
  PairFixture.join (FVal false, false) (FVal true, true) = (FTop, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example product_negative :
  PairFixture.leb (FVal false, true) (FVal true, true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_bottom :
  PairFixture.join (FBot, false) (FVal true, false) = (FVal true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example product_top :
  PairFixture.leb (FTop, true) (FTop, true) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(* Cost and height examples are in LatticeProductTest.v at 87192fe. *)
