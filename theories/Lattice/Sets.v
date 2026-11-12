(** * Set lattices

    May and must collections model finite sets and finite conjunctions.
    For example, a must join retains facts shared by both inputs.
    Builds on: LatticeSig, SetSig and MapSig. *)

From Stdlib Require Import Bool List Arith NArith Lia Sorting.Sorted Sorting.Permutation.
From Argent Require Import Time.
From Galois.Base Require Import KeySig MapSig SetSig.
From Galois.Lattice Require Import LatticeSig Simple WithBot.

Module MaySetCode (K : KEY_OPS) (S : SET_OPS K) <: LATTICE_OPS.
  Definition t := S.t.
  Definition leb := S.subset.
  Definition bot := S.empty.
  Definition is_bot (x : t) := S.subset x S.empty.
  Definition join := S.union.
End MaySetCode.

Module MustSetCode (K : KEY_OPS) (S : SET_OPS K) <: LATTICE_OPS.
  Definition t := option S.t.
  Definition leb (x y : t) : bool :=
    match x, y with
    | None, _ => true
    | Some _, None => false
    | Some a, Some b => S.subset b a
    end.
  Definition bot : t := None.
  Definition is_bot (x : t) := match x with None => true | Some _ => false end.
  Definition join (x y : t) : t :=
    match x, y with
    | None, _ => y
    | _, None => x
    | Some a, Some b => Some (S.inter a b)
    end.
End MustSetCode.
