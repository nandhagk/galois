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

Module Dual (L : BLATTICE) <: BLATTICE.
  Include DualCode L.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro a; apply L.leb_refl. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. unfold leb; intros a b c Hab Hbc; eapply L.leb_trans; eassumption. Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intro a; apply L.top_greatest. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. apply L.leb_refl. Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. unfold is_bot, leb; intros a b H; eapply L.leb_trans; [apply L.top_greatest|exact H]. Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros a b; apply L.meet_lb_l. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros a b; apply L.meet_lb_r. Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. intro a; apply L.bot_least. Qed.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. intros a b; apply L.join_ub_l. Qed.
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. intros a b; apply L.join_ub_r. Qed.
End Dual.

Module DualT (L : BLATTICE_T) <: BLATTICE_T.
  Include Dual L.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun meet.

  Definition size (x : t) : nat := L.size x.
  Definition c_lat : nat := 1. (* STUB *)

  Lemma T_leb_le : forall a b, T_leb a b <= c_lat * (size a + size b + 1).
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b, T_join a b <= c_lat * (size a + size b + 1).
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a, T_is_bot a <= c_lat * (size a + 1).
  Proof. Admitted. (* STUB *)
  Lemma T_meet_le : forall a b, T_meet a b <= c_lat * (size a + size b + 1).
  Proof. Admitted. (* STUB *)
End DualT.
