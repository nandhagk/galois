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
  Proof. unfold is_bot, bot; cbn; rewrite A.is_bot_bot, B.is_bot_bot; reflexivity. Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros x y H; unfold is_bot in H; apply andb_true_iff in H.
    destruct H as [H1 H2]; unfold leb; apply andb_true_iff; split;
      [eapply A.is_bot_least|eapply B.is_bot_least]; eassumption.
  Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros x y; unfold leb, join; cbn; rewrite A.join_ub_l, B.join_ub_l; reflexivity. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros x y; unfold leb, join; cbn; rewrite A.join_ub_r, B.join_ub_r; reflexivity. Qed.
End Product.
