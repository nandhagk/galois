(** * Product lattices

    Products apply lattice operations to each coordinate independently.
    For example, a pair of booleans joins by disjoining each coordinate.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool NArith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.

Module ProductCode (A B : LATTICE_OPS) <: LATTICE_OPS.
  Definition t := (A.t * B.t)%type.
  Definition leb (x y : t) := andb (A.leb (fst x) (fst y)) (B.leb (snd x) (snd y)).
  Definition bot : t := (A.bot, B.bot).
  Definition is_bot (x : t) := andb (A.is_bot (fst x)) (B.is_bot (snd x)).
  Definition join (x y : t) : t := (A.join (fst x) (fst y), B.join (snd x) (snd y)).
End ProductCode.
