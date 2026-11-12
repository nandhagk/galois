(** * Dual lattices

    A dual reverses an order and uses a supplied meet as its join.
    For example, boolean conjunction joins in reverse implication order.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Arith NArith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
Module DualCode (L : BLATTICE_OPS) <: BLATTICE_OPS.
  Definition t := L.t.
  Definition leb (a b : t) : bool := L.leb b a.
  Definition bot : t := L.top.
  Definition is_bot (a : t) : bool := L.leb L.top a.
  Definition join (a b : t) : t := L.meet a b.
  Definition top : t := L.bot.
  Definition meet (a b : t) : t := L.join a b.
End DualCode.
