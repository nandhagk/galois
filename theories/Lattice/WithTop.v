(** * Top lifts

    A top lift adds a fresh value above an existing lattice.
    For example, joining Unknown with any element gives Unknown.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time Std.
From Galois.Lattice Require Import LatticeSig.
Inductive lift_top (A : Type) : Type :=
  | Elem (a : A)
  | Unknown.

Arguments Elem {A}.
Arguments Unknown {A}.

Module Type TOP_LATTICE_OPS := LATTICE_OPS <+ HAS_TOP_OPS.

Module WithTopCode (L : LATTICE_OPS) <: TOP_LATTICE_OPS.
  Definition t := lift_top L.t.
  Definition leb (x y : t) : bool :=
    match x, y with
    | _, Unknown => true
    | Elem a, Elem b => L.leb a b
    | Unknown, Elem _ => false
    end.
  Definition bot : t := Elem L.bot.
  Definition is_bot (x : t) : bool :=
    match x with
    | Elem a => L.is_bot a
    | Unknown => false
    end.
  Definition join (x y : t) : t :=
    match x, y with
    | Elem a, Elem b => Elem (L.join a b)
    | _, _ => Unknown
    end.
  Definition top : t := Unknown.
End WithTopCode.

Module Type TOP_LATTICE := LATTICE <+ HAS_TOP_OPS <+ HAS_TOP_LAWS.

Module Type TOP_LATTICE_T := TOP_LATTICE <+ LATTICE_TIME.

Module WithTop (L : LATTICE) <: TOP_LATTICE.
  Include WithTopCode L.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intros [a|]; cbn; try reflexivity; apply L.leb_refl. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [a|] [b|] [c|]; cbn; intros Hab Hbc;
      try discriminate; try reflexivity; eapply L.leb_trans; eassumption.
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros [a|]; cbn; try reflexivity; apply L.bot_least. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros [a|] [b|]; cbn; try reflexivity; apply L.join_ub_l. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros [a|] [b|]; cbn; try reflexivity; apply L.join_ub_r. Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. intros [a|]; reflexivity. Qed.
End WithTop.

Module WithTopT (L : LATTICE_T) <: TOP_LATTICE_T.
  Include WithTop L.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (x : t) : nat :=
    match x with
    | Elem a => L.size a + 1
    | Unknown => 1
    end.
  Definition c_lat : N := 1. (* STUB *)

  Lemma T_leb_le : forall a b, (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b, (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End WithTopT.

Module WithTopHeight (L : LATTICE) (H : HEIGHT L)
    (Lat : TOP_LATTICE with Definition t := lift_top L.t
                        with Definition leb :=
                          (fun x y => match x, y with
                                      | _, Unknown => true
                                      | Elem a, Elem b => L.leb a b
                                      | Unknown, Elem _ => false
                                      end)) <: HEIGHT Lat.
  Definition rank (x : lift_top L.t) := match x with Elem a => H.rank a | Unknown => S H.height end.
  Definition height := S H.height.
  Lemma rank_le : forall a, rank a <= height.
  Proof. intros [a|]; cbv [rank height]; [pose proof (H.rank_le a); lia|reflexivity]. Qed.
  Lemma rank_strict : forall a b, Lat.leb a b = true -> Lat.leb b a = false ->
    rank a < rank b.
  Proof.
    intros [a|] [b|]; cbn [Lat.leb rank]; intros Hab Hba;
      try discriminate; try (pose proof (H.rank_le a); lia).
    apply H.rank_strict; assumption.
  Qed.
End WithTopHeight.
