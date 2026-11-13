(** * Bounded collections

    Supported collection values carry total heights through invariant restriction.
    For example, a bounded may set adds at most the number of universe keys.
    Builds on: LatticeSig, Sets and MapLattice. *)

From Stdlib Require Import List NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig MapSig SetSig.
From Galois.Lattice Require Import LatticeSig Sets MapLattice.

Module Specif.
  TimeFun proj1_sig.
End Specif.

Module BoundedCode (K : KEY_OPS) (S : SET_OPS K).
  Definition rank (s : S.t) : nat := length (S.elements s).
  Definition height (universe : S.t) : nat := length (S.elements universe).
End BoundedCode.

(** * Sets restricted to a universe *)

Module BoundedSetCode (K : KEY) (S : SET K) (U : UNIVERSE K S) <: LATTICE_OPS.
  Definition t := {s : S.t | S.subset s U.u = true}.

  (** Empty support lies inside the universe. *)
  Lemma bot_inside : S.subset S.empty U.u = true.
  Proof. apply S.subset_spec; intros k Hk; rewrite S.has_empty in Hk; discriminate. Qed.

  (** Union preserves the restriction to the universe. *)
  Lemma union_inside (a b : t) :
    S.subset (S.union (proj1_sig a) (proj1_sig b)) U.u = true.
  Proof.
    destruct a as [a Ha], b as [b Hb]. pose proof (proj1 (S.subset_spec a U.u) Ha) as Ha1; pose proof (proj1 (S.subset_spec b U.u) Hb) as Hb1.
    apply S.subset_spec; intros k Hk; cbn in *. rewrite S.has_union in Hk.
    apply Bool.orb_true_iff in Hk. destruct Hk; auto.
  Qed.

  (** Intersection clips any raw set to the universe. *)
  Lemma inter_inside (s : S.t) : S.subset (S.inter s U.u) U.u = true.
  Proof.
    apply S.subset_spec; intros k Hk. rewrite S.has_inter in Hk.
    apply Bool.andb_true_iff in Hk. tauto.
  Qed.

  Definition leb (a b : t) : bool := S.subset (proj1_sig a) (proj1_sig b).
  Definition bot : t := exist _ S.empty bot_inside.
  Definition is_bot (a : t) : bool := S.subset (proj1_sig a) S.empty.
  Definition join (a b : t) : t :=
    exist _ (S.union (proj1_sig a) (proj1_sig b)) (union_inside a b).
  Definition clip (s : S.t) : t := exist _ (S.inter s U.u) (inter_inside s).
End BoundedSetCode.

Module BoundedSet (K : KEY) (S : SET K) (U : UNIVERSE K S) <: LATTICE.
  Include BoundedSetCode K S U.
  Module May := MaySet K S.

  (** Restricted inclusion is reflexive. *)
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro a; apply May.leb_refl. Qed.
  (** Restricted inclusion composes. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. intros a b c; apply May.leb_trans. Qed.
  (** The empty restricted set is least. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intro a; apply May.bot_least. Qed.
  (** The bottom test recognizes the empty restricted set. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. apply May.is_bot_bot. Qed.
  (** Every recognized empty support is least. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. intros a b; apply May.is_bot_least. Qed.
  (** Union contains its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros a b; apply May.join_ub_l. Qed.
  (** Union contains its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros a b; apply May.join_ub_r. Qed.
End BoundedSet.

Module BoundedSetT (K : KEY_T) (S : SET_T K) (U : UNIVERSE K S) <: LATTICE_T.
  Include BoundedSet K S U.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun clip.

  Definition size (a : t) : nat := S.nodes (proj1_sig a) + S.weight (proj1_sig a) + 1.
  Definition c_lat : N := (S.c_set + 8)%N.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. unfold c_lat; lia. Qed.

  (** Restricted inclusion has the time bound of the underlying set operation. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a Ha] [b Hb]. pose proof (S.T_subset_le a b) as Hsubset.
    time_unfold @T_leb. unfold size, c_lat. cbn [proj1_sig]. time_simpl.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.
  (** Restricted union has the time bound of the underlying set operation. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a Ha] [b Hb]. pose proof (S.T_union_le a b) as Hunion.
    time_unfold @T_join. unfold size, c_lat. cbn [proj1_sig]. time_simpl.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.
  (** Bottom testing charges the restricted support. *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intros [a Ha]. pose proof (S.T_subset_le a S.empty) as Hsubset.
    rewrite S.nodes_empty in Hsubset.
    time_unfold @T_is_bot. unfold size, c_lat. cbn [proj1_sig]. time_simpl.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.
End BoundedSetT.

Module BoundedHeight (K : KEY) (S : SET K) (U : UNIVERSE K S)
    (Lat : LATTICE with Definition t := {s : S.t | S.subset s U.u = true}
                  with Definition leb :=
                    (fun (a b : {s : S.t | S.subset s U.u = true}) =>
                      S.subset (proj1_sig a) (proj1_sig b))) <: HEIGHT Lat.
  Definition rank (a : Lat.t) : nat :=
    length (filter (fun k => S.mem k (proj1_sig a)) (S.elements U.u)).
  Definition height : nat := length (S.elements U.u).

  Local Lemma filter_count_order (f g : K.t -> bool) xs :
    (forall x, In x xs -> f x = true -> g x = true) ->
    length (filter f xs) <= length (filter g xs) /\
    (length (filter f xs) = length (filter g xs) ->
      forall x, In x xs -> g x = true -> f x = true).
  Proof.
    induction xs as [|x xs IH]; intro Horder; cbn.
    - split; [lia|intros _ y Hin; contradiction].
    - assert (Htail : forall y, In y xs -> f y = true -> g y = true).
      { intros y Hin Hy; apply Horder; [right; exact Hin|exact Hy]. }
      destruct (IH Htail) as [Hle Heq].
      destruct (f x) eqn:Hf, (g x) eqn:Hg; cbn.
      + split; [lia|]. intros Hlen y [<-|Hin] Hy; [exact Hf|].
        apply Heq; [lia|assumption|assumption].
      + exfalso. specialize (Horder x (or_introl eq_refl) Hf). congruence.
      + split; [lia|]. intros Hlen. lia.
      + split; [lia|]. intros Hlen y [<-|Hin] Hy; [congruence|].
        apply Heq; assumption.
  Qed.

  (** The restricted support contains at most all universe keys. *)
  Lemma rank_le : forall a, rank a <= height.
  Proof. intro a; unfold rank, height; apply filter_length_le. Qed.
  (** Inclusion never removes a universe key. *)
  Lemma rank_mono : forall a b, Lat.leb a b = true -> rank a <= rank b.
  Proof.
    intros a b Hab. unfold rank.
    assert (Horder : forall k, In k (S.elements U.u) ->
      S.mem k (proj1_sig a) = true -> S.mem k (proj1_sig b) = true).
    { intros k Hin Hmem. rewrite !S.mem_has in *.
      apply (proj1 (S.subset_spec _ _) Hab); exact Hmem. }
    exact (proj1 (filter_count_order _ _ _ Horder)).
  Qed.
  (** Strict inclusion adds a universe key. *)
  Lemma rank_strict : forall a b, Lat.leb a b = true -> Lat.leb b a = false ->
    rank a < rank b.
  Proof.
    intros a b Hab Hba.
    assert (Horder : forall k, In k (S.elements U.u) ->
      S.mem k (proj1_sig a) = true -> S.mem k (proj1_sig b) = true).
    { intros k Hin Hmem. rewrite !S.mem_has in *.
      apply (proj1 (S.subset_spec _ _) Hab); exact Hmem. }
    destruct (filter_count_order _ _ _ Horder) as [Hle Heq].
    unfold rank. assert (Hne : length (filter (fun k => S.mem k (proj1_sig a)) (S.elements U.u)) <>
      length (filter (fun k => S.mem k (proj1_sig b)) (S.elements U.u))).
    { intro Hlen. assert (Hback : Lat.leb b a = true).
      { apply S.subset_spec. intros p Hp.
        pose proof (proj1 (S.subset_spec _ _) (proj2_sig b) p Hp) as Hu.
        destruct (S.wf_has U.u p U.u_wf Hu) as [k Hk]. subst p.
        rewrite <- S.mem_has. apply (Heq Hlen k).
        - apply (proj2 (S.elements_spec U.u k U.u_wf)). rewrite S.mem_has. exact Hu.
        - rewrite S.mem_has. exact Hp. }
      congruence. }
    lia.
  Qed.
End BoundedHeight.
