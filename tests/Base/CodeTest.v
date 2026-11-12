(** * Composite key tests

    These examples check equality of composite encoded keys.
    For example, reversing distinct pair components changes their keys.
    Builds on: Key and Code. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Code.

Module PosPair := PairKeyCode PosKeyCode PosKeyCode.
Module PosSum := SumKeyCode PosKeyCode PosKeyCode.

Example encoding_only_pair_negative :
  Pos.eqb (PosPair.encode (1%positive, 2%positive))
    (PosPair.encode (2%positive, 1%positive)) = false.
Proof. vm_compute. reflexivity. Qed.

Example encoding_only_sum_negative :
  Pos.eqb (PosSum.encode (inl 1%positive)) (PosSum.encode (inr 1%positive)) = false.
Proof. vm_compute. reflexivity. Qed.

(* Decoder, symbolic law and cost examples are in BaseCodeTest.v at 87192fe. *)
