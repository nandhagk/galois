(** * Composite key tests

    These examples check equality of composite encoded keys.
    For example, reversing distinct pair components changes their keys.

    Groups:
    - [PairTests] Codes of pairs, which change when the components are reversed.
    - [SumTests] Codes of sums, which change with the tag of the value.

    Builds on: Key and Code. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Code.

(** * Fixtures *)

(** Pairs of positive keys, encoded componentwise. *)
Module PosPair := PairKeyCode PosKeyCode PosKeyCode.

(** Sums of positive keys, tagged left or right. *)
Module PosSum := SumKeyCode PosKeyCode PosKeyCode.

(** * Pair codes *)

Module PairTests.

  (** Reversing the components of a pair gives a different code. *)
  Example reversed_pair_codes_differ :
    Pos.eqb (PosPair.encode (1%positive, 2%positive))
      (PosPair.encode (2%positive, 1%positive)) = false.
  Proof. vm_compute. reflexivity. Qed.

End PairTests.

(** * Sum codes *)

Module SumTests.

  (** The left and right tags of the same value give different codes. *)
  Example left_and_right_tags_differ :
    Pos.eqb (PosSum.encode (inl 1%positive)) (PosSum.encode (inr 1%positive)) = false.
  Proof. vm_compute. reflexivity. Qed.

End SumTests.
