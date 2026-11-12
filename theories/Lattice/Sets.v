(** * Set lattices

    May and must collections model finite sets and finite conjunctions.
    For example, a must join retains facts shared by both inputs.
    Builds on: LatticeSig, SetSig and MapSig. *)

From Stdlib Require Import Bool List Arith NArith Lia Sorting.Sorted Sorting.Permutation.
From Argent Require Import Time Std.
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
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
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
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
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

Module MaySetT (K : KEY_T) (S : SET_T K) <: LATTICE_T.
  Include MaySet K S.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (s : t) : nat := S.weight s.
  Definition c_lat : N := 1. (* STUB *)

  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End MaySetT.

Module MustSetT (K : KEY_T) (S : SET_T K) <: LATTICE_T.
  Include MustSet K S.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (s : t) : nat :=
    match s with None => 1 | Some members => S.weight members + 1 end.
  Definition c_lat : N := 1. (* STUB *)

  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End MustSetT.
