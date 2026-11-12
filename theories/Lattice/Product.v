(** * Product lattices

    Products apply lattice operations to each coordinate independently.
    For example, a pair of booleans joins by disjoining each coordinate.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool NArith Lia.
From Argent Require Import Time Std.
From Galois.Lattice Require Import LatticeSig.

Module ProductCode (A B : LATTICE_OPS) <: LATTICE_OPS.
  Definition t := (A.t * B.t)%type.
  Definition leb (x y : t) := andb (A.leb (fst x) (fst y)) (B.leb (snd x) (snd y)).
  Definition bot : t := (A.bot, B.bot).
  Definition is_bot (x : t) := andb (A.is_bot (fst x)) (B.is_bot (snd x)).
  Definition join (x y : t) : t := (A.join (fst x) (fst y), B.join (snd x) (snd y)).
End ProductCode.

Module Product (A B : LATTICE) <: LATTICE.
  Include ProductCode A B.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro x; unfold leb; apply andb_true_iff; split; [apply A.leb_refl|apply B.leb_refl]. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros x y z Hxy Hyz; unfold leb in *.
    apply andb_true_iff in Hxy; apply andb_true_iff in Hyz.
    destruct Hxy as [Hxy1 Hxy2], Hyz as [Hyz1 Hyz2].
    apply andb_true_iff; split; [eapply A.leb_trans|eapply B.leb_trans]; eassumption.
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intro x; unfold leb, bot; cbn; rewrite A.bot_least, B.bot_least; reflexivity. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros x y; unfold leb, join; cbn; rewrite A.join_ub_l, B.join_ub_l; reflexivity. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros x y; unfold leb, join; cbn; rewrite A.join_ub_r, B.join_ub_r; reflexivity. Qed.
End Product.

Module ProductT (A B : LATTICE_T) <: LATTICE_T.
  Include Product A B.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (x : t) : nat := A.size (fst x) + B.size (snd x) + 1.
  Definition c_lat : N := 1. (* STUB *)
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_leb_le : forall a b, (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b, (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End ProductT.

Module ProductHeight (A B : LATTICE) (HA : HEIGHT A) (HB : HEIGHT B)
    (Lat : LATTICE with Definition t := (A.t * B.t)%type
                  with Definition leb :=
                    (fun x y => andb (A.leb (fst x) (fst y)) (B.leb (snd x) (snd y))))
    <: HEIGHT Lat.
  Definition rank (x : Lat.t) : nat := HA.rank (fst x) + HB.rank (snd x).
  Definition height : nat := HA.height + HB.height.

  (** The sum of component ranks is bounded by the sum of their heights. *)
  Lemma rank_le : forall a, rank a <= height.
  Proof. Admitted.
  (** Componentwise inclusion never lowers the rank sum. *)
  Lemma rank_mono : forall a b, Lat.leb a b = true -> rank a <= rank b.
  Proof. Admitted.
  (** A strict product step increases at least one component rank. *)
  Lemma rank_strict : forall a b, Lat.leb a b = true -> Lat.leb b a = false ->
    rank a < rank b.
  Proof. Admitted.
End ProductHeight.
