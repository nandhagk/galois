(** * Join-derived widening

    This file defines the widening obtained from a lattice join.
    For example, widening two values may return their join.
    Builds on: LatticeSig. *)

From Stdlib Require Import NArith Lia.
From Argent Require Import Time Tactics Std.
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
  Proof. intros p a b; unfold widen; destruct (L.leb b a); auto using L.leb_refl, L.join_ub_l. Qed.
  Lemma widen_ub_r : forall p a b, L.leb b (widen p a b) = true.
  Proof. intros p a b; unfold widen; destruct (L.leb b a) eqn:Hab; auto using L.join_ub_r. Qed.
  Lemma widen_stable : forall p a b, L.leb b a = true -> widen p a b = a.
  Proof. intros p a b Hab; unfold widen; rewrite Hab; reflexivity. Qed.
  Lemma wrank_widen : forall p a b, L.is_bot a = false -> L.leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p a b Hbot Hab. unfold widen; rewrite Hab. unfold wrank.
    assert (Hback : L.leb (L.join a b) a = false).
    { destruct (L.leb (L.join a b) a) eqn:Hjoin; auto.
      pose proof (L.leb_trans b (L.join a b) a (L.join_ub_r a b) Hjoin). congruence. }
    pose proof (H.rank_strict a (L.join a b) (L.join_ub_l a b) Hback).
    pose proof (H.rank_le (L.join a b)). lia.
  Qed.
  Lemma wrank_widen_le : forall p a b, L.is_bot a = false ->
    wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot. unfold wrank.
    pose proof (H.rank_mono a (widen p a b) (widen_ub_l p a b)). lia.
  Qed.
  Lemma narrow_between : forall a b, L.leb b a = true ->
    L.leb b (narrow a b) = true /\ L.leb (narrow a b) a = true.
  Proof. intros a b Hab; split; cbn [narrow]; auto using L.leb_refl. Qed.
End JoinWidening.

Module JoinWideningT (L : LATTICE_T) (H : HEIGHT L) <: WIDENING_T L.
  Include JoinWidening L H.

  TimeFun widen.
  TimeFun narrow.

  Definition wsize (_ : wparam) : nat := 3.
  Definition wunits (a : L.t) : nat := L.size a + 1.

  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= L.c_lat *
      N.of_nat ((wunits a + wunits b) * wsize p +
        (L.size a + L.size b + wsize p + 1)))%N.
  Proof.
    intros p a b.
    pose proof (L.T_leb_le b a) as Hcompare.
    pose proof (L.T_join_le a b) as Hjoin.
    pose proof L.c_lat_pos as Hpositive.
    unfold wunits, wsize. time_unfold @T_widen.
    destruct (L.leb b a); time_cbn.
    all: repeat rewrite Nat2N.inj_mul in *;
      repeat rewrite Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= L.c_lat * N.of_nat (L.size a + L.size b + 1))%N.
  Proof.
    intros a b. pose proof L.c_lat_pos as Hpositive.
    time_unfold @T_narrow. repeat rewrite Nat2N.inj_add. nia.
  Qed.
End JoinWideningT.
