(** * Map lattices

    Sparse environments use explicit defaults for absent keys.
    For example, joining top-default maps drops a binding present on one side.
    Builds on: LatticeSig and MapSig. *)

From Stdlib Require Import Bool List Arith NArith Lia.
From Argent Require Import Time.
From Galois.Base Require Import KeySig MapSig.
From Galois.Lattice Require Import LatticeSig.

Module MapLatticeCode (K : KEY_OPS) (M : MAP_OPS K) (L : LATTICE_OPS)
    <: LATTICE_OPS.
  Definition t := M.t L.t.
  Definition default (x : option L.t) : L.t :=
    match x with Some a => a | None => L.bot end.
  Definition leb (x y : t) : bool :=
    M.forall2b (fun a b => L.leb (default a) (default b)) x y.
  Definition bot : t := M.empty.
  Definition is_bot (x : t) : bool := negb (M.existsb (fun a => negb (L.is_bot a)) x).
  Definition join (x y : t) : t :=
    M.merge (fun a b =>
      match a, b with
      | None, None => None
      | Some a, None => Some a
      | None, Some b => Some b
      | Some a, Some b => Some (L.join a b)
      end) x y.
End MapLatticeCode.
