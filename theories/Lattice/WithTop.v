(** * Top lifts

    A top lift adds a fresh value above an existing lattice.
    For example, joining Unknown with any element gives Unknown.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time.
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
