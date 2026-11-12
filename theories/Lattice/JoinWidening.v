(** * Join-derived widening

    This file defines the widening obtained from a lattice join.
    For example, widening two values may return their join.
    Builds on: LatticeSig. *)

From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.

Module JoinWideningCode (L : LATTICE_OPS) <: WIDENING_OPS L.
  Definition wparam := unit.
  Definition widen (_ : wparam) (a b : L.t) : L.t :=
    if L.leb b a then a else L.join a b.
  Definition narrow (a _ : L.t) : L.t := a.
End JoinWideningCode.
