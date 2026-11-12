(** * Bounded collections

    Supported collection values carry total heights through invariant restriction.
    For example, a bounded may set adds at most the number of universe keys.
    Builds on: LatticeSig, Sets and MapLattice. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time.
From Galois.Base Require Import KeySig MapSig SetSig.
From Galois.Lattice Require Import LatticeSig Sets MapLattice.

Module BoundedCode (K : KEY_OPS) (S : SET_OPS K).
  Definition rank (s : S.t) : nat := length (S.elements s).
  Definition height (universe : S.t) : nat := length (S.elements universe).
End BoundedCode.
