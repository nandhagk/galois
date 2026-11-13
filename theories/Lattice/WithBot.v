(** * Bottom lifts

    Option adds a fresh bottom while retaining reached values.
    For example, joining None and Some a returns Some a.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Lattice Require Import LatticeSig.

Module WithBotCode (L : LATTICE_OPS) <: LATTICE_OPS.
  Definition t := option L.t.
  Definition leb (x y : t) : bool :=
    match x, y with
    | None, _ => true
    | Some a, Some b => L.leb a b
    | Some _, None => false
    end.
  Definition bot : t := None.
  Definition is_bot (x : t) : bool :=
    match x with
    | None => true
    | Some _ => false
    end.
  Definition join (x y : t) : t :=
    match x, y with
    | None, _ => y
    | _, None => x
    | Some a, Some b => Some (L.join a b)
    end.
End WithBotCode.

Module WithBot (L : LATTICE) <: LATTICE.
  Include WithBotCode L.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intros [a|]; cbn; try reflexivity; apply L.leb_refl. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [a|] [b|] [c|]; cbn; intros Hab Hbc;
      try discriminate; try reflexivity; eapply L.leb_trans; eassumption.
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros [a|]; reflexivity. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [a|] b Hbot; cbn in *; try discriminate; reflexivity.
  Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros [a|] [b|]; cbn; try reflexivity; try apply L.leb_refl; apply L.join_ub_l. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros [a|] [b|]; cbn; try reflexivity; try apply L.leb_refl; apply L.join_ub_r. Qed.
End WithBot.

Module WithBotT (L : LATTICE_T) <: LATTICE_T.
  Include WithBot L.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (x : t) : nat :=
    match x with
    | None => 1
    | Some a => L.size a + 1
    end.
  Definition c_lat : N := (4 * (L.c_lat + 1))%N.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. lia.
  Qed.

  Lemma T_leb_le : forall a b, (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a|] [b|]; time_unfold @T_leb; cbn [size]; unfold c_lat;
      time_pose; rewrite ?Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_join_le : forall a b, (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a|] [b|]; time_unfold @T_join; cbn [size]; unfold c_lat;
      time_pose; rewrite ?Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intros [a|]; time_unfold @T_is_bot; cbn [size]; unfold c_lat;
      rewrite ?Nat2N.inj_add; nia.
  Qed.
End WithBotT.

Module WithBotHeight (L : LATTICE) (H : HEIGHT L)
    (Lat : LATTICE with Definition t := option L.t
                    with Definition leb :=
                      (fun x y => match x, y with
                                  | None, _ => true
                                  | Some a, Some b => L.leb a b
                                  | Some _, None => false
                                  end)) <: HEIGHT Lat.
  Definition rank (x : option L.t) := match x with None => 0 | Some a => S (H.rank a) end.
  Definition height := S H.height.
  Lemma rank_le : forall a, rank a <= height.
  Proof. intros [a|]; cbv [rank height]; try (apply le_n_S; apply H.rank_le); try lia. Qed.
  (** The lifted order never lowers rank. *)
  Lemma rank_mono : forall a b, Lat.leb a b = true -> rank a <= rank b.
  Proof.
    intros [a|] [b|]; cbn [Lat.leb rank]; intro Hab; try discriminate; try lia.
    pose proof (H.rank_mono a b Hab). lia.
  Qed.
  Lemma rank_strict : forall a b, Lat.leb a b = true -> Lat.leb b a = false ->
    rank a < rank b.
  Proof.
    intros [a|] [b|]; cbn [Lat.leb rank]; intros Hab Hba;
      try discriminate; try lia.
    pose proof (H.rank_strict a b Hab Hba); lia.
  Qed.
End WithBotHeight.
