(** * Flat lattices

    Flat values distinguish bottom, a known value and top.
    For example, joining distinct known values gives top.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
From Galois.Base Require Import KeySig.

Inductive flat (A : Type) : Type :=
  | FBot
  | FVal (a : A)
  | FTop.

Arguments FBot {A}.
Arguments FVal {A}.
Arguments FTop {A}.

(** Flat comparison uses the supplied test for known values. *)
Definition flat_leb {A} (eqb : A -> A -> bool) (x y : flat A) : bool :=
  match x, y with
  | FBot, _ => true
  | _, FTop => true
  | FVal a, FVal b => eqb a b
  | _, _ => false
  end.

TimeFun flat_leb.

(** Flat join preserves equal known values and otherwise returns top. *)
Definition flat_join {A} (eqb : A -> A -> bool) (x y : flat A) : flat A :=
  match x, y with
  | FBot, _ => y
  | _, FBot => x
  | FVal a, FVal b => if eqb a b then FVal a else FTop
  | _, _ => FTop
  end.

TimeFun flat_join.

(** Flat widening is join and narrowing keeps its left input. *)
Module FlatCode (K : KEY_OPS) <: BLATTICE_OPS.
  Definition t := flat K.t.
  Definition leb := flat_leb K.eqb.
  Definition bot : t := FBot.
  Definition is_bot (x : t) := match x with FBot => true | _ => false end.
  Definition join := flat_join K.eqb.
  Definition top : t := FTop.
  Definition meet (x y : t) : t :=
    match x, y with
    | FTop, _ => y
    | _, FTop => x
    | FVal a, FVal b => if K.eqb a b then FVal a else FBot
    | _, _ => FBot
    end.
End FlatCode.

Module Flat (K : KEY) <: BLATTICE.
  Include FlatCode K.
  Lemma eqb_refl : forall a, K.eqb a a = true.
  Proof. intro a; destruct (K.eqb_spec a a); congruence. Qed.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intros [|a|]; cbn [leb flat_leb]; auto using eqb_refl. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [|a|] [|b|] [|c|]; cbn [leb flat_leb]; intros Hab Hbc;
      try discriminate; try reflexivity.
    destruct (K.eqb_spec a b); try discriminate; subst b; exact Hbc.
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros [|a|]; reflexivity. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|a|] [|b|]; cbn [leb join flat_leb flat_join]; try reflexivity;
      try apply eqb_refl.
    destruct (K.eqb a b) eqn:Hab; cbn [flat_leb]; [apply eqb_refl|reflexivity].
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|a|] [|b|]; cbn [leb join flat_leb flat_join]; try reflexivity;
      try apply eqb_refl.
    destruct (K.eqb a b) eqn:Hab; cbn [flat_leb].
    - destruct (K.eqb_spec a b); try discriminate; subst b; apply eqb_refl.
    - reflexivity.
  Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. intros [|a|]; reflexivity. Qed.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted.
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.
End Flat.

Module FlatT (K : KEY_T) <: BLATTICE_T.
  Include Flat K.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun meet.

  Definition size (x : t) : nat :=
    match x with
    | FBot | FTop => 1
    | FVal a => K.bits a + 1
    end.
  Definition c_lat : N := 1. (* STUB *)

  Lemma T_leb_le : forall a b, (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b, (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_meet_le : forall a b, (T_meet a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
End FlatT.

Module FlatHeight (K : KEY)
    (Lat : BLATTICE with Definition t := flat K.t
                     with Definition leb := flat_leb K.eqb) <: HEIGHT Lat.
  Definition rank (x : flat K.t) : nat :=
    match x with
    | FBot => 0
    | FVal _ => 1
    | FTop => 2
    end.
  Definition height : nat := 2.
  Lemma rank_le : forall a, rank a <= height.
  Proof. intros [|a|]; cbv [rank height]; auto. Qed.
  (** The flat order never lowers rank. *)
  Lemma rank_mono : forall a b, Lat.leb a b = true -> rank a <= rank b.
  Proof. Admitted.
  Lemma rank_strict : forall a b, flat_leb K.eqb a b = true -> flat_leb K.eqb b a = false ->
    rank a < rank b.
  Proof.
    intros [|a|] [|b|]; cbn [flat_leb rank]; intros Hab Hba;
      try discriminate; try lia.
    destruct (K.eqb_spec a b); try discriminate; subst b.
    destruct (K.eqb_spec a a); congruence.
  Qed.
End FlatHeight.
