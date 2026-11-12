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

Module JoinWidening (L : LATTICE) (H : HEIGHT L) <: WIDENING L.
  Include JoinWideningCode L.
  Definition wrank (_ : wparam) (a : L.t) := H.height - H.rank a.
  Lemma widen_ub_l : forall p a b, L.leb a (widen p a b) = true.
  Proof. Admitted.
  Lemma widen_ub_r : forall p a b, L.leb b (widen p a b) = true.
  Proof. Admitted.
  Lemma widen_stable : forall p a b, L.leb b a = true -> widen p a b = a.
  Proof. Admitted.
  Lemma wrank_widen : forall p a b, L.is_bot a = false -> L.leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted.
  Lemma wrank_widen_le : forall p a b, L.is_bot a = false ->
    wrank p (widen p a b) <= wrank p a.
  Proof. Admitted.
  Lemma narrow_between : forall a b, L.leb b a = true ->
    L.leb b (narrow a b) = true /\ L.leb (narrow a b) a = true.
  Proof. Admitted.
End JoinWidening.
