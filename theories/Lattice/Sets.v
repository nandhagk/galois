(** * Set lattices

    May and must collections model finite sets and finite conjunctions.
    For example, a must join retains facts shared by both inputs.
    Builds on: LatticeSig, SetSig and MapSig. *)

From Stdlib Require Import Bool List Arith NArith Lia Sorting.Sorted Sorting.Permutation.
From Argent Require Import Time.
From Galois.Base Require Import KeySig MapSig SetSig.
From Galois.Lattice Require Import LatticeSig Simple WithBot.

Module MaySetCode (K : KEY_OPS) (S : SET_OPS K) <: LATTICE_OPS.
  Definition t := S.t.
  Definition leb := S.subset.
  Definition bot := S.empty.
  Definition is_bot (x : t) := S.subset x S.empty.
  Definition join := S.union.
End MaySetCode.

Module MustSetCode (K : KEY_OPS) (S : SET_OPS K) <: LATTICE_OPS.
  Definition t := option S.t.
  Definition leb (x y : t) : bool :=
    match x, y with
    | None, _ => true
    | Some _, None => false
    | Some a, Some b => S.subset b a
    end.
  Definition bot : t := None.
  Definition is_bot (x : t) := match x with None => true | Some _ => false end.
  Definition join (x y : t) : t :=
    match x, y with
    | None, _ => y
    | _, None => x
    | Some a, Some b => Some (S.inter a b)
    end.
End MustSetCode.

Module MaySet (K : KEY) (S : SET K) <: LATTICE.
  Include MaySetCode K S.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro a; apply S.subset_spec; intros k H; exact H. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc; unfold leb in Hab, Hbc; pose proof (proj1 (S.subset_spec a b) Hab) as Hab1; pose proof (proj1 (S.subset_spec b c) Hbc) as Hbc1.
    apply S.subset_spec; intros k Hk; apply Hbc1, Hab1, Hk.
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intro a; apply S.subset_spec; intros k Hk; rewrite S.mem_empty in Hk; discriminate. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. apply leb_refl. Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. intros a b H; eapply leb_trans; [exact H|apply bot_least]. Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros a b; apply S.subset_spec; intros k Hk; rewrite S.mem_union, Hk; reflexivity.
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros a b; apply S.subset_spec; intros k Hk; rewrite S.mem_union, Hk, orb_true_r; reflexivity.
  Qed.
End MaySet.

Module MustSet (K : KEY) (S : SET K) <: LATTICE.
  Include MustSetCode K S.
  Module May := MaySet K S.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intros [s|]; cbn [leb]; try reflexivity; apply May.leb_refl. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [leb]; intros Hab Hbc;
      try discriminate; try reflexivity; eapply May.leb_trans; eassumption.
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros [a|]; reflexivity. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. reflexivity. Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. intros [a|] [b|]; cbn [is_bot leb]; intro H; try discriminate; reflexivity. Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [leb join]; try reflexivity; try apply May.leb_refl.
    apply S.subset_spec; intros k Hk; rewrite S.mem_inter in Hk.
    apply andb_true_iff in Hk; tauto.
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [leb join]; try reflexivity; try apply May.leb_refl.
    apply S.subset_spec; intros k Hk; rewrite S.mem_inter in Hk.
    apply andb_true_iff in Hk; tauto.
  Qed.
End MustSet.
