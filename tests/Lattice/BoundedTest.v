(** * Bounded collection fixtures

    Finite support supplies collection ranks.
    For example, the three-key chain reaches the universe size.
    Builds on: Bounded, TrieSet and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key TrieSet.
From Galois.Lattice Require Import Bounded.
Import List.ListNotations.

Module PosSet := TrieSetCode PosKeyCode.
Module Bound := BoundedCode PosKeyCode PosSet.
Definition b0 := PosSet.empty.
Definition b1 := PosSet.add 1%positive b0.
Definition b12 := PosSet.add 2%positive b1.
Definition b123 := PosSet.add 3%positive b12.

Example bounded_chain_reaches_bound :
  (List.map Bound.rank [b0; b1; b12; b123], Bound.height b123) = ([0; 1; 2; 3], 3).
Proof. vm_compute. reflexivity. Qed.
Example bounded_empty_universe_height : Bound.height b0 = 0.
Proof. vm_compute. reflexivity. Qed.

(* Subtype, bounded environment and cost examples are in LatticeBoundedTest.v at 87192fe. *)
