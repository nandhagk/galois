(** * Threshold trees

    Threshold trees store sorted distinct integers and search for nearby bounds.
    For example, the least threshold above four in [0; 8] is eight.
    Builds on: ThresholdsSig. *)

From Stdlib Require Import List ZArith NArith Arith Lia Sorting.Sorted Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Domains Require Import ThresholdsSig.
Import List.ListNotations.

Module Nat.
  TimeFun Stdlib.Arith.PeanoNat.Nat.divmod.
  TimeFun Stdlib.Arith.PeanoNat.Nat.div.
End Nat.

Module ListDef.
  TimeFun Corelib.Lists.ListDef.firstn.
  TimeFun Corelib.Lists.ListDef.skipn.
End ListDef.

Module ThresholdsCode <: THRESHOLDS_OPS.
  Fixpoint merge (fuel : nat) (xs ys : list Z) : list Z :=
    match fuel with
    | 0 => []
    | S fuel =>
      match xs, ys with
      | [], _ => ys
      | _, [] => xs
      | x :: xt, y :: yt =>
        if Z.leb x y then x :: merge fuel xt ys else y :: merge fuel xs yt
      end
    end.

  Fixpoint sort_fuel (fuel : nat) (xs : list Z) : list Z :=
    match fuel with
    | 0 => xs
    | S fuel =>
      match xs with
      | [] | [_] => xs
      | _ =>
        let middle := length xs / 2 in
        let lhs := sort_fuel fuel (firstn middle xs) in
        let rhs := sort_fuel fuel (skipn middle xs) in
        merge (length xs) lhs rhs
      end
    end.

  Definition msort (xs : list Z) := sort_fuel (length xs) xs.

  Fixpoint dedup_sorted (xs : list Z) : list Z :=
    match xs with
    | [] => []
    | x :: rest =>
      match rest with
      | [] => [x]
      | y :: _ => if Z.eqb x y then dedup_sorted rest else x :: dedup_sorted rest
      end
    end.

  Fixpoint build (fuel : nat) (xs : list Z) : ttree :=
    match fuel with
    | 0 => TLeaf
    | S fuel =>
      let middle := length xs / 2 in
      match skipn middle xs with
      | [] => TLeaf
      | x :: rhs => TNode (build fuel (firstn middle xs)) x (build fuel rhs)
      end
    end.

  Definition make (xs : list Z) : ttree :=
    let sorted := dedup_sorted (msort xs) in build (length sorted) sorted.

  Fixpoint below_reference (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if Z.leb value z then
        match below_reference rhs z with
        | Some x => Some (Z.max value x)
        | None => Some value
        end
      else below_reference lhs z
    end.

  Fixpoint above_reference (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if negb (Z.ltb value z) then
        match above_reference lhs z with
        | Some x => Some (Z.min value x)
        | None => Some value
        end
      else above_reference rhs z
    end.

  Fixpoint below (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if Z.leb value z then
        match below rhs z with
        | Some x => Some x
        | None => Some value
        end
      else below lhs z
    end.

  Fixpoint above (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if negb (Z.ltb value z) then
        match above lhs z with
        | Some x => Some x
        | None => Some value
        end
      else above rhs z
    end.
End ThresholdsCode.

Module Thresholds <: THRESHOLDS.
  Include ThresholdsCode.
  Include THRESHOLDS_SPEC.

  (** Sufficient merge fuel preserves both input multisets. *)
  Lemma merge_perm : forall fuel xs ys, length xs + length ys <= fuel ->
    Permutation (xs ++ ys) (merge fuel xs ys).
  Proof.
    induction fuel as [|fuel IH]; intros xs ys Hfuel.
    - destruct xs, ys; cbn in *; try lia; constructor.
    - destruct xs as [|x xs], ys as [|y ys]; cbn [merge];
        try rewrite app_nil_r; try apply Permutation_refl.
      destruct (Z.leb x y).
      + apply perm_skip, IH. cbn in Hfuel |- *. lia.
      + eapply Permutation_trans.
        * apply Permutation_sym, Permutation_middle.
        * apply perm_skip, IH. cbn in Hfuel |- *. lia.
  Qed.

  (** Every recursive sorting pass preserves the input multiset. *)
  Lemma sort_fuel_perm : forall fuel xs, Permutation xs (sort_fuel fuel xs).
  Proof.
    induction fuel as [|fuel IH]; intros xs; [apply Permutation_refl|].
    destruct xs as [|x [|y ys]]; cbn [sort_fuel]; try apply Permutation_refl.
    set (zs := x :: y :: ys).
    pose proof (IH (firstn (length zs / 2) zs)) as Hleft.
    pose proof (IH (skipn (length zs / 2) zs)) as Hright.
    change (Permutation zs (merge (length zs)
      (sort_fuel fuel (firstn (length zs / 2) zs))
      (sort_fuel fuel (skipn (length zs / 2) zs)))).
    eapply Permutation_trans with (l' :=
      sort_fuel fuel (firstn (length zs / 2) zs) ++
      sort_fuel fuel (skipn (length zs / 2) zs)).
    - rewrite <- (firstn_skipn (length zs / 2) zs) at 1.
      apply Permutation_app; [exact Hleft|exact Hright].
    - apply merge_perm.
      rewrite <- (Permutation_length Hleft), <- (Permutation_length Hright).
      rewrite <- length_app, firstn_skipn. lia.
  Qed.

  (** Merging retains every property shared by all input elements. *)
  Lemma merge_forall : forall fuel xs ys (P : Z -> Prop),
    Forall P xs -> Forall P ys -> Forall P (merge fuel xs ys).
  Proof.
    induction fuel as [|fuel IH]; intros xs ys P Hxs Hys; [constructor|].
    destruct xs as [|x xs], ys as [|y ys]; cbn [merge]; try assumption.
    pose proof (Forall_inv Hxs) as Hx.
    pose proof (Forall_inv_tail Hxs) as Htailx.
    pose proof (Forall_inv Hys) as Hy.
    pose proof (Forall_inv_tail Hys) as Htaily.
    destruct (Z.leb x y); constructor; auto.
  Qed.

  (** A merge of two ordered lists is ordered at every fuel. *)
  Lemma merge_sorted : forall fuel xs ys,
    StronglySorted Z.le xs -> StronglySorted Z.le ys ->
    StronglySorted Z.le (merge fuel xs ys).
  Proof.
    induction fuel as [|fuel IH]; intros xs ys Hxs Hys; [constructor|].
    destruct xs as [|x xs], ys as [|y ys]; cbn [merge]; try assumption.
    destruct (StronglySorted_inv Hxs) as [Htailx Hallx].
    destruct (StronglySorted_inv Hys) as [Htaily Hally].
    destruct (Z.leb x y) eqn:Hxy.
    - apply Z.leb_le in Hxy. constructor.
      + apply IH; assumption.
      + apply merge_forall; [exact Hallx|]. constructor; [exact Hxy|].
        eapply Forall_impl; [|exact Hally]. intros z Hyz. lia.
    - apply Z.leb_gt in Hxy. constructor.
      + apply IH; assumption.
      + apply merge_forall; [|exact Hally]. constructor; [lia|].
        eapply Forall_impl; [|exact Hallx]. intros z Hxz. lia.
  Qed.

  (** Sufficient sorting fuel orders the input. *)
  Lemma sort_fuel_sorted : forall fuel xs, length xs <= fuel ->
    StronglySorted Z.le (sort_fuel fuel xs).
  Proof.
    induction fuel as [|fuel IH]; intros xs Hfuel.
    - destruct xs; cbn in *; [constructor|lia].
    - destruct xs as [|x [|y ys]]; [constructor|repeat constructor|].
      set (zs := x :: y :: ys).
      assert (Hpositive : 0 < length zs) by (unfold zs; cbn; lia).
      pose proof (Nat.div_lt (length zs) 2 Hpositive ltac:(lia)) as Hhalf.
      pose proof (Nat.div_mod (length zs) 2 ltac:(lia)) as Hdiv.
      pose proof (Nat.mod_upper_bound (length zs) 2 ltac:(lia)) as Hmod.
      assert (Htwo : 2 <= length zs) by (unfold zs; cbn; lia).
      change (StronglySorted Z.le (merge (length zs)
        (sort_fuel fuel (firstn (length zs / 2) zs))
        (sort_fuel fuel (skipn (length zs / 2) zs)))).
      apply merge_sorted; apply IH.
      + rewrite length_firstn, Nat.min_l by lia. change (length zs <= S fuel) in Hfuel.
        lia.
      + rewrite length_skipn. change (length zs <= S fuel) in Hfuel. lia.
  Qed.

  (** Deduplication changes multiplicity but never membership. *)
  Lemma dedup_vals_aux : forall zs x, In x (dedup_sorted zs) <-> In x zs.
  Proof.
    induction zs as [|a zs IH]; intro x; [reflexivity|].
    destruct zs as [|b zs]; [reflexivity|].
    change (In x (if Z.eqb a b then dedup_sorted (b :: zs)
      else a :: dedup_sorted (b :: zs)) <-> In x (a :: b :: zs)).
    destruct (Z.eqb a b) eqn:Heq.
    - apply Z.eqb_eq in Heq. subst a. rewrite IH. cbn. tauto.
    - cbn [In]. rewrite IH. reflexivity.
  Qed.

  (** Deduplicating a weakly ordered list makes its order strict. *)
  Lemma dedup_ordered_aux : forall zs, StronglySorted Z.le zs ->
    StronglySorted Z.lt (dedup_sorted zs).
  Proof.
    induction zs as [|a zs IH]; intro Hsort; [constructor|].
    destruct zs as [|b zs]; [repeat constructor|].
    destruct (StronglySorted_inv Hsort) as [Htail Hall].
    destruct (StronglySorted_inv Htail) as [Hrest Hallb].
    change (StronglySorted Z.lt (if Z.eqb a b then dedup_sorted (b :: zs)
      else a :: dedup_sorted (b :: zs))).
    destruct (Z.eqb a b) eqn:Heq; [now apply IH|].
    apply Z.eqb_neq in Heq.
    pose proof (Forall_inv Hall) as Hab.
    assert (Hlt : (a < b)%Z) by lia.
    constructor; [now apply IH|].
    apply Forall_forall. intros z Hin.
    apply (proj1 (dedup_vals_aux (b :: zs) z)) in Hin.
    destruct Hin as [<-|Hin]; [exact Hlt|].
    rewrite Forall_forall in Hallb. specialize (Hallb z Hin). lia.
  Qed.

  (** Strictly ordered integer lists contain no duplicate values. *)
  Lemma ordered_nodup : forall zs, StronglySorted Z.lt zs -> NoDup zs.
  Proof.
    intros zs Hsort. induction Hsort as [|z zs Hsort IH Hall]; constructor.
    - intro Hin. rewrite Forall_forall in Hall. specialize (Hall z Hin). lia.
    - exact IH.
  Qed.

  (** Sorting and deduplication never increase the original list length. *)
  Lemma prepared_length : forall zs, length (dedup_sorted (msort zs)) <= length zs.
  Proof.
    intro zs. apply NoDup_incl_length.
    - apply ordered_nodup, dedup_ordered_aux, sort_fuel_sorted. lia.
    - intros z Hin. apply (proj1 (dedup_vals_aux (msort zs) z)) in Hin.
      eapply Permutation_in; [apply Permutation_sym, sort_fuel_perm|exact Hin].
  Qed.

  (** The median splits a nonempty list into balanced smaller pieces. *)
  Lemma median_split (xs : list Z) : xs <> [] ->
    exists x rhs, skipn (length xs / 2) xs = x :: rhs /\
      length (firstn (length xs / 2) xs) = length xs / 2 /\
      length xs = S (length xs / 2 + length rhs) /\
      length rhs <= length xs / 2 <= S (length rhs).
  Proof.
    intro Hnonempty.
    assert (Hpositive : 0 < length xs) by (destruct xs; cbn in *; congruence || lia).
    pose proof (Nat.div_mod (length xs) 2 ltac:(lia)) as Hdiv.
    pose proof (Nat.mod_upper_bound (length xs) 2 ltac:(lia)) as Hmod.
    pose proof (Nat.div_lt (length xs) 2 Hpositive ltac:(lia)) as Hhalf.
    destruct (skipn (length xs / 2) xs) as [|x rhs] eqn:Hskip.
    - pose proof (length_skipn (length xs / 2) xs) as Hlen.
      rewrite Hskip in Hlen. change (0 = length xs - length xs / 2) in Hlen. lia.
    - exists x, rhs. split; [reflexivity|].
      rewrite length_firstn, Nat.min_l by lia.
      pose proof (length_skipn (length xs / 2) xs) as Hlen.
      rewrite Hskip in Hlen.
      change (S (length rhs) = length xs - length xs / 2) in Hlen. lia.
  Qed.

  (** Sufficient fuel preserves the list as the tree's inorder traversal. *)
  Lemma build_vals_aux : forall fuel zs, length zs <= fuel -> vals (build fuel zs) = zs.
  Proof.
    induction fuel as [|fuel IH]; intros zs Hfuel.
    - destruct zs; cbn in *; [reflexivity|lia].
    - destruct zs as [|z zs]; [reflexivity|].
      destruct (median_split (z :: zs) ltac:(discriminate))
        as [pivot [rhs [Hskip [Hleft [Hlength Hbalance]]]]].
      cbn [build]. rewrite Hskip. cbn [vals].
      rewrite !IH by lia.
      pose proof (firstn_skipn (length (z :: zs) / 2) (z :: zs)) as Hsplit.
      now rewrite Hskip in Hsplit.
  Qed.

  (** A list below a power-of-two capacity yields at most that many tree levels. *)
  Lemma build_capacity : forall fuel zs h, length zs < 2 ^ h ->
    depth (build fuel zs) <= h.
  Proof.
    induction fuel as [|fuel IH]; intros zs h Hcapacity; [cbn; lia|].
    destruct zs as [|z zs]; [cbn; lia|].
    destruct h as [|h]; [cbn in Hcapacity; lia|].
    destruct (median_split (z :: zs) ltac:(discriminate))
      as [pivot [rhs [Hskip [Hleft [Hlength Hbalance]]]]].
    cbn [build]. rewrite Hskip. cbn [depth].
    change (length (z :: zs) < 2 * 2 ^ h) in Hcapacity.
    apply le_n_S, Nat.max_lub; apply IH; nia.
  Qed.

  (** Median construction has logarithmic depth, even when fuel is truncated. *)
  Lemma build_depth_aux : forall fuel zs,
    depth (build fuel zs) <= Nat.log2 (length zs) + 1.
  Proof.
    intros fuel zs. destruct zs as [|z zs].
    - destruct fuel; reflexivity || cbn; lia.
    - replace (Nat.log2 (length (z :: zs)) + 1)
        with (S (Nat.log2 (length (z :: zs)))) by lia.
      apply build_capacity.
      apply (proj2 (Nat.log2_spec (length (z :: zs)) ltac:(cbn; lia))).
  Qed.

  (** All fuel values covering the list produce the same median tree. *)
  Lemma build_fuel_eq : forall fuel fuel' zs, length zs <= fuel -> length zs <= fuel' ->
    build fuel zs = build fuel' zs.
  Proof.
    induction fuel as [|fuel IH]; intros fuel' zs Hfuel Hfuel'; destruct fuel'.
    - reflexivity.
    - destruct zs; [reflexivity|cbn in Hfuel; lia].
    - destruct zs; [reflexivity|cbn in Hfuel'; lia].
    - destruct zs as [|z zs]; [reflexivity|].
      destruct (median_split (z :: zs) ltac:(discriminate))
        as [pivot [rhs [Hskip [Hleft [Hlength Hbalance]]]]].
      cbn [build]. rewrite Hskip. f_equal; apply IH; lia.
  Qed.

  (** Construction retains precisely the supplied thresholds. *)
  Lemma make_vals : forall zs x, In x (vals (make zs)) <-> In x zs.
  Proof.
    intros zs x. unfold make. rewrite build_vals_aux by lia. rewrite dedup_vals_aux.
    split; intro Hin; eapply Permutation_in; [|exact Hin| |exact Hin].
    - apply Permutation_sym, sort_fuel_perm.
    - apply sort_fuel_perm.
  Qed.
  (** Construction orders and deduplicates thresholds. *)
  Lemma make_ordered : forall zs, ordered (make zs).
  Proof.
    intro zs. unfold ordered, make. rewrite build_vals_aux by lia.
    apply dedup_ordered_aux, sort_fuel_sorted. lia.
  Qed.
  (** Construction produces a logarithmic-depth tree. *)
  Lemma make_depth : forall zs, depth (make zs) <= Nat.log2 (length zs) + 1.
  Proof.
    intro zs. unfold make. eapply Nat.le_trans; [apply build_depth_aux|].
    apply Nat.add_le_mono_r, Nat.log2_le_mono, prepared_length.
  Qed.

  (** Inorder membership splits into the root and the two children. *)
  Lemma node_vals : forall lhs value rhs x,
    In x (vals (TNode lhs value rhs)) <->
      value = x \/ In x (vals lhs) \/ In x (vals rhs).
  Proof.
    intros lhs value rhs x. cbn [vals]. rewrite in_app_iff. cbn [In]. tauto.
  Qed.

  (** A strict list split orders both pieces and separates them at the pivot. *)
  Lemma sorted_split : forall lhs x rhs, StronglySorted Z.lt (lhs ++ x :: rhs) ->
    StronglySorted Z.lt lhs /\ StronglySorted Z.lt rhs /\
    (forall y, In y lhs -> (y < x)%Z) /\ (forall y, In y rhs -> (x < y)%Z).
  Proof.
    induction lhs as [|a lhs IH]; intros x rhs Hsort; cbn in Hsort.
    - destruct (StronglySorted_inv Hsort) as [Htail Hall].
      repeat split; try constructor; try assumption; try contradiction.
      now rewrite <- Forall_forall.
    - destruct (StronglySorted_inv Hsort) as [Htail Hall].
      destruct (IH x rhs Htail) as [Hl [Hr [Hbelow Habove]]].
      rewrite Forall_forall in Hall.
      repeat split; try assumption.
      + constructor; [exact Hl|]. rewrite Forall_forall.
        intros y Hy. apply Hall. apply in_app_iff. now left.
      + intros y [<-|Hy].
        * apply Hall. apply in_app_iff. right. now left.
        * now apply Hbelow.
  Qed.

  (** An ordered node has ordered children separated by its root value. *)
  Lemma ordered_node : forall lhs value rhs, ordered (TNode lhs value rhs) ->
    ordered lhs /\ ordered rhs /\
    (forall x, In x (vals lhs) -> (x < value)%Z) /\
    (forall x, In x (vals rhs) -> (value < x)%Z).
  Proof.
    intros lhs value rhs Hordered. unfold ordered in *. apply sorted_split, Hordered.
  Qed.

  (** Upper search returns the least eligible threshold or proves none exists. *)
  Lemma above_spec : forall t z, ordered t ->
    match above t z with
    | Some u => In u (vals t) /\ (z <= u)%Z /\
      forall v, In v (vals t) -> (z <= v)%Z -> (u <= v)%Z
    | None => forall v, In v (vals t) -> (v < z)%Z
    end.
  Proof.
    induction t as [|lhs IHleft value rhs IHright]; intros z Hordered;
      [cbn; tauto|].
    destruct (ordered_node lhs value rhs Hordered) as [Hleft [Hright [Hbelow Habove]]].
    specialize (IHleft z Hleft). specialize (IHright z Hright).
    cbn [above]. destruct (Z.ltb value z) eqn:Htest; cbn.
    - apply Z.ltb_lt in Htest. destruct (above rhs z) as [u|] eqn:Hsearch.
      + destruct IHright as [Hin [Hbound Hleast]].
        split; [apply node_vals; now right; right|]. split; [exact Hbound|].
        intros v Hv Hzv. apply node_vals in Hv as [<-|[Hv|Hv]].
        * lia.
        * specialize (Hbelow v Hv). lia.
        * now apply Hleast.
      + intros v Hv. apply node_vals in Hv as [<-|[Hv|Hv]].
        * exact Htest.
        * specialize (Hbelow v Hv). lia.
        * now apply IHright.
    - apply Z.ltb_ge in Htest. destruct (above lhs z) as [u|] eqn:Hsearch.
      + destruct IHleft as [Hin [Hbound Hleast]].
        pose proof (Hbelow u Hin) as Hroot.
        split; [apply node_vals; right; now left|]. split; [exact Hbound|].
        intros v Hv Hzv. apply node_vals in Hv as [<-|[Hv|Hv]].
        * lia.
        * now apply Hleast.
        * specialize (Habove v Hv). lia.
      + split; [apply node_vals; now left|]. split; [exact Htest|].
        intros v Hv Hzv. apply node_vals in Hv as [<-|[Hv|Hv]].
        * lia.
        * specialize (IHleft v Hv). lia.
        * specialize (Habove v Hv). lia.
  Qed.
  (** Lower search returns the greatest eligible threshold or proves none exists. *)
  Lemma below_spec : forall t z, ordered t ->
    match below t z with
    | Some u => In u (vals t) /\ (u <= z)%Z /\
      forall v, In v (vals t) -> (v <= z)%Z -> (v <= u)%Z
    | None => forall v, In v (vals t) -> (z < v)%Z
    end.
  Proof.
    induction t as [|lhs IHleft value rhs IHright]; intros z Hordered;
      [cbn; tauto|].
    destruct (ordered_node lhs value rhs Hordered) as [Hleft [Hright [Hbelow Habove]]].
    specialize (IHleft z Hleft). specialize (IHright z Hright).
    cbn [below]. destruct (Z.leb value z) eqn:Htest.
    - apply Z.leb_le in Htest. destruct (below rhs z) as [u|] eqn:Hsearch.
      + destruct IHright as [Hin [Hbound Hgreatest]].
        pose proof (Habove u Hin) as Hroot.
        split; [apply node_vals; right; now right|]. split; [exact Hbound|].
        intros v Hv Hvz. apply node_vals in Hv as [<-|[Hv|Hv]].
        * lia.
        * specialize (Hbelow v Hv). lia.
        * now apply Hgreatest.
      + split; [apply node_vals; now left|]. split; [exact Htest|].
        intros v Hv Hvz. apply node_vals in Hv as [<-|[Hv|Hv]].
        * lia.
        * specialize (Hbelow v Hv). lia.
        * specialize (IHright v Hv). lia.
    - apply Z.leb_gt in Htest. destruct (below lhs z) as [u|] eqn:Hsearch.
      + destruct IHleft as [Hin [Hbound Hgreatest]].
        split; [apply node_vals; right; now left|]. split; [exact Hbound|].
        intros v Hv Hvz. apply node_vals in Hv as [<-|[Hv|Hv]].
        * lia.
        * now apply Hgreatest.
        * specialize (Habove v Hv). lia.
      + intros v Hv. apply node_vals in Hv as [<-|[Hv|Hv]].
        * exact Htest.
        * now apply IHleft.
        * specialize (Habove v Hv). lia.
  Qed.
  (** Upper search is sound even when the tree is unordered. *)
  Lemma above_sound : forall t z u,
    above t z = Some u -> In u (vals t) /\ (z <= u)%Z.
  Proof.
    induction t as [|lhs IHleft value rhs IHright]; intros z u Hresult;
      cbn [above] in Hresult; [discriminate|].
    cbn [vals]. rewrite in_app_iff.
    destruct (Z.ltb value z) eqn:Htest; cbn in Hresult.
    - destruct (IHright z u Hresult) as [Hin Hbound]. split; [right; now right|assumption].
    - apply Z.ltb_ge in Htest.
      destruct (above lhs z) as [v|] eqn:Hleft.
      + injection Hresult as <-. destruct (IHleft z v Hleft) as [Hin Hbound].
        split; [now left|exact Hbound].
      + injection Hresult as <-. split; [right; now left|assumption].
  Qed.
  (** Lower search is sound even when the tree is unordered. *)
  Lemma below_sound : forall t z u,
    below t z = Some u -> In u (vals t) /\ (u <= z)%Z.
  Proof.
    induction t as [|lhs IHleft value rhs IHright]; intros z u Hresult;
      cbn [below] in Hresult; [discriminate|].
    cbn [vals]. rewrite in_app_iff.
    destruct (Z.leb value z) eqn:Htest.
    - apply Z.leb_le in Htest.
      destruct (below rhs z) as [v|] eqn:Hright.
      + injection Hresult as <-. destruct (IHright z v Hright) as [Hin Hbound].
        split; [right; now right|exact Hbound].
      + injection Hresult as <-. split; [right; now left|assumption].
    - destruct (IHleft z u Hresult) as [Hin Hbound]. split; [now left|assumption].
  Qed.

  (** An ordered lower search agrees with the comparison-based reference. *)
  Lemma below_agrees : forall tree z, ordered tree ->
    below tree z = below_reference tree z.
  Proof.
    induction tree as [|lhs IHleft value rhs IHright]; intros z Hordered.
    - reflexivity.
    - destruct (ordered_node lhs value rhs Hordered)
        as [Hleft [Hright [Hbelow Habove]]].
      cbn [below below_reference].
      rewrite <- (IHleft z Hleft), <- (IHright z Hright).
      destruct (Z.leb value z); [|reflexivity].
      destruct (below rhs z) as [u|] eqn:Hsearch; [|reflexivity].
      destruct (below_sound rhs z u Hsearch) as [Hin Hbound].
      specialize (Habove u Hin). rewrite Z.max_r by lia. reflexivity.
  Qed.

  (** An ordered upper search agrees with the comparison-based reference. *)
  Lemma above_agrees : forall tree z, ordered tree ->
    above tree z = above_reference tree z.
  Proof.
    induction tree as [|lhs IHleft value rhs IHright]; intros z Hordered.
    - reflexivity.
    - destruct (ordered_node lhs value rhs Hordered)
        as [Hleft [Hright [Hbelow Habove]]].
      cbn [above above_reference].
      rewrite <- (IHleft z Hleft), <- (IHright z Hright).
      destruct (negb (Z.ltb value z)); [|reflexivity].
      destruct (above lhs z) as [u|] eqn:Hsearch; [|reflexivity].
      destruct (above_sound lhs z u Hsearch) as [Hin Hbound].
      specialize (Hbelow u Hin). rewrite Z.min_r by lia. reflexivity.
  Qed.
End Thresholds.

Module ThresholdsT <: THRESHOLDS_ALL.
  Include Thresholds.

  TimeFun merge.
  TimeFun sort_fuel.
  TimeFun msort.
  TimeFun dedup_sorted.
  TimeFun build.
  TimeFun make.
  TimeFun below.
  TimeFun above.

  Local Open Scope nat_scope.

  (** Unary division traverses its numerator once, independently of the accumulators. *)
  Lemma divmod_time : forall x y q u,
    Nat.T_divmod x y q u = (N.of_nat x + 1)%N.
  Proof.
    induction x as [|x IH]; intros y q u; time_unfold Nat.T_divmod.
    - reflexivity.
    - destruct u; rewrite IH; lia.
  Qed.

  (** Division adds only a wrapper and the quotient projection to the numerator pass. *)
  Lemma div_time : forall x y, (Nat.T_div x y <= N.of_nat x + 3)%N.
  Proof.
    intros x [|y]; time_unfold Nat.T_div; [lia|].
    rewrite divmod_time. pose proof (Std.Datatypes.T_fst_le (Nat.divmod x y 0 y)). lia.
  Qed.

  (** Prefix extraction visits no more than the requested number of list cells. *)
  Lemma firstn_time : forall n (xs : list Z),
    (ListDef.T_firstn n xs <= N.of_nat n + 1)%N.
  Proof.
    induction n as [|n IH]; intros [|x xs]; time_unfold ListDef.T_firstn; try lia.
    specialize (IH xs). lia.
  Qed.

  (** Prefix removal visits no more than the requested number of list cells. *)
  Lemma skipn_time : forall n (xs : list Z),
    (ListDef.T_skipn n xs <= N.of_nat n + 1)%N.
  Proof.
    induction n as [|n IH]; intros [|x xs]; time_unfold ListDef.T_skipn; try lia.
    specialize (IH xs). lia.
  Qed.

  (** The list bit envelope bounds exactly the bit size of each stored integer. *)
  Lemma zb_spec : forall xs bound,
    zb xs <= bound <-> Forall (fun x => zbits x <= bound) xs.
  Proof.
    induction xs as [|x xs IH]; intro bound; cbn [zb map fold_right].
    - split; intro H; [constructor|lia].
    - rewrite Forall_cons_iff, <- IH.
      change (Nat.max (zbits x) (zb xs) <= bound <->
        zbits x <= bound /\ zb xs <= bound). lia.
  Qed.

  (** Reordering a list preserves every common bit bound. *)
  Lemma sort_bits : forall fuel xs bound,
    Forall (fun x => zbits x <= bound) xs ->
    Forall (fun x => zbits x <= bound) (sort_fuel fuel xs).
  Proof.
    intros fuel xs bound Hbits. rewrite Forall_forall in Hbits |- *.
    intros x Hin. apply Hbits. eapply Permutation_in; [|exact Hin].
    apply Permutation_sym, sort_fuel_perm.
  Qed.

  (** Merge consumes at most its fuel, with each comparison charged to a stored value. *)
  Lemma merge_time : forall fuel xs ys bound,
    Forall (fun x => zbits x <= bound) xs ->
    Forall (fun x => zbits x <= bound) ys ->
    (T_merge fuel xs ys <= N.of_nat (fuel + 1) * N.of_nat (bound + 5))%N.
  Proof.
    induction fuel as [|fuel IH]; intros xs ys bound Hxs Hys; [time_unfold T_merge; nia|].
    destruct xs as [|x xs]; [time_unfold T_merge; nia|].
    destruct ys as [|y ys]; [time_unfold T_merge; nia|].
    time_unfold T_merge.
    inversion Hxs as [|x' xs' Hx Htailx]; subst.
    inversion Hys as [|y' ys' Hy Htaily]; subst.
    pose proof (Std.Z.T_leb_le x y) as Hcompare.
    change (Z.size_nat x <= bound) in Hx.
    destruct (Z.leb x y).
    - pose proof (IH xs (y :: ys) bound Htailx Hys). nia.
    - pose proof (IH (x :: xs) ys bound Hxs Htaily). nia.
  Qed.

  (** Halving a list at capacity two-to-the-next-level fits both halves at the lower level. *)
  Lemma split_capacity : forall n h, n <= 2 ^ S h ->
    n / 2 <= 2 ^ h /\ n - n / 2 <= 2 ^ h.
  Proof.
    intros n h Hcapacity. change (n <= 2 * 2 ^ h) in Hcapacity.
    pose proof (Nat.div_mod n 2 ltac:(lia)) as Hdiv.
    pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hmod. lia.
  Qed.

  (** The two recursive sorting budgets combine using preservation of the total length. *)
  Lemma sort_children_budget : forall n middle h bound, middle <= n ->
    (64 * N.of_nat (middle * (h + 1) + 1) * N.of_nat (bound + 1) +
      64 * N.of_nat ((n - middle) * (h + 1) + 1) * N.of_nat (bound + 1) =
      64 * N.of_nat (n * (h + 1) + 2) * N.of_nat (bound + 1))%N.
  Proof.
    intros n middle h bound Hmiddle.
    rewrite <- N.mul_add_distr_r, <- N.mul_add_distr_l, <- Nat2N.inj_add.
    replace (middle * (h + 1) + 1 + ((n - middle) * (h + 1) + 1))
      with (n * (h + 1) + 2) by nia. reflexivity.
  Qed.

  (** The next sorting level reserves a linear budget beyond its recursive children. *)
  Lemma sort_parent_budget : forall n h bound, 1 <= n ->
    (64 * N.of_nat (n * (S h + 1) + 1) * N.of_nat (bound + 1) =
      64 * N.of_nat (n * (h + 1) + 2) * N.of_nat (bound + 1) +
      64 * N.of_nat (n - 1) * N.of_nat (bound + 1))%N.
  Proof.
    intros n h bound Hpositive.
    replace (n * (S h + 1) + 1) with (n * (h + 1) + 2 + (n - 1)) by nia.
    rewrite Nat2N.inj_add, N.mul_add_distr_l, N.mul_add_distr_r. reflexivity.
  Qed.

  (** A capacity of two to the height pays for all sorting levels at a shared bit bound. *)
  Lemma sort_capacity_time : forall h fuel xs bound,
    length xs <= 2 ^ h -> Forall (fun x => zbits x <= bound) xs ->
    (T_sort_fuel fuel xs <=
      64 * N.of_nat (length xs * (h + 1) + 1) * N.of_nat (bound + 1))%N.
  Proof.
    induction h as [|h IH]; intros fuel xs bound Hcapacity Hbits.
    - destruct xs as [|x [|y ys]]; cbn [length Nat.pow] in Hcapacity; try lia;
        destruct fuel; time_unfold T_sort_fuel; cbn [length]; nia.
    - destruct fuel as [|fuel]; [time_unfold T_sort_fuel; nia|].
      destruct xs as [|x [|y ys]];
        [time_unfold T_sort_fuel; cbn [length]; nia|
         time_unfold T_sort_fuel; cbn [length]; nia|].
      set (input := x :: y :: ys) in *.
      assert (Htwo : 2 <= length input) by (unfold input; cbn; lia).
      pose proof (Nat.div_lt (length input) 2 ltac:(lia) ltac:(lia)) as Hhalf.
      destruct (split_capacity (length input) h Hcapacity) as [Hleftcap Hrightcap].
      assert (Hleftlength : length (firstn (length input / 2) input) = length input / 2).
      { rewrite length_firstn, Nat.min_l by lia. reflexivity. }
      assert (Hparts : Forall (fun x => zbits x <= bound) (firstn (length input / 2) input) /\
        Forall (fun x => zbits x <= bound) (skipn (length input / 2) input)).
      { rewrite <- Forall_app, firstn_skipn. exact Hbits. }
      destruct Hparts as [Hleftbits Hrightbits].
      pose proof (IH fuel (firstn (length input / 2) input) bound
        ltac:(rewrite Hleftlength; exact Hleftcap) Hleftbits) as Hleft.
      pose proof (IH fuel (skipn (length input / 2) input) bound
        ltac:(rewrite length_skipn; exact Hrightcap) Hrightbits) as Hright.
      pose proof (merge_time (length input)
        (sort_fuel fuel (firstn (length input / 2) input))
        (sort_fuel fuel (skipn (length input / 2) input)) bound
        (sort_bits fuel _ bound Hleftbits) (sort_bits fuel _ bound Hrightbits)) as Hmerge.
      pose proof (Std.Datatypes.T_length_le input) as Hlength.
      pose proof (div_time (length input) 2) as Hdiv.
      pose proof (firstn_time (length input / 2) input) as Hfirstn.
      pose proof (skipn_time (length input / 2) input) as Hskipn.
      rewrite Hleftlength in Hleft. rewrite length_skipn in Hright.
      pose proof (N.add_le_mono _ _ _ _ Hleft Hright) as Hchildren.
      rewrite (sort_children_budget (length input) (length input / 2) h bound ltac:(lia))
        in Hchildren.
      change (T_sort_fuel (S fuel) (x :: y :: ys) <=
        64 * N.of_nat (length input * (S h + 1) + 1) * N.of_nat (bound + 1))%N.
      time_unfold T_sort_fuel. fold input. rewrite sort_parent_budget by lia.
      clear Hleft Hright IH Hcapacity Hleftcap Hrightcap Hleftlength.
      remember (64 * N.of_nat (length input * (h + 1) + 2) * N.of_nat (bound + 1))%N
        as children_budget. clear Heqchildren_budget. nia.
  Qed.

  (** Every list length fits the power-of-two capacity just above its binary logarithm. *)
  Lemma log_capacity : forall n, n < 2 ^ (Nat.log2 n + 1).
  Proof.
    intros [|n]; [cbn; lia|].
    replace (Nat.log2 (S n) + 1) with (S (Nat.log2 (S n))) by lia.
    exact (proj2 (Nat.log2_spec (S n) ltac:(lia))).
  Qed.

  (** The public sorting wrapper adds only the initial length scan. *)
  Lemma msort_time : forall xs,
    (T_msort xs <= 256 * N.of_nat (length xs * (Nat.log2 (length xs) + 1) + 1) *
      N.of_nat (zb xs + 1))%N.
  Proof.
    intro xs.
    pose proof (sort_capacity_time (Nat.log2 (length xs) + 1) (length xs) xs (zb xs)
      ltac:(pose proof (log_capacity (length xs)); lia)
      (proj1 (zb_spec xs (zb xs)) (Nat.le_refl _))) as Hsort.
    pose proof (Std.Datatypes.T_length_le xs) as Hlength.
    time_unfold T_msort. nia.
  Qed.

  (** Adjacent deduplication charges one bounded integer comparison per visited cell. *)
  Lemma dedup_time : forall xs bound, Forall (fun x => zbits x <= bound) xs ->
    (T_dedup_sorted xs <= 4 * N.of_nat (length xs + 1) * N.of_nat (bound + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intros bound Hbits.
    - time_unfold T_dedup_sorted. cbn [length]. nia.
    - destruct xs as [|y ys]; [time_unfold T_dedup_sorted; cbn [length]; nia|].
      inversion Hbits as [|x' xs' Hx Htail]; subst.
      specialize (IH bound Htail). change (Z.size_nat x <= bound) in Hx.
      pose proof (Std.Z.T_eqb_le x y) as Hcompare.
      time_unfold T_dedup_sorted. destruct (Z.eqb x y); cbn [length] in *; nia.
  Qed.

  (** An empty construction call has a fixed cost even when unused fuel remains. *)
  Lemma build_empty_time : forall fuel, (T_build fuel nil <= 6)%N.
  Proof.
    intros [|fuel]; [change (1 <= 6)%N|change (6 <= 6)%N]; lia.
  Qed.

  (** Each construction level charges a linear split of its nonempty input. *)
  Lemma build_capacity_time : forall h fuel xs, length xs < 2 ^ h ->
    (T_build fuel xs <= 32 * N.of_nat (length xs * (h + 1) + 1))%N.
  Proof.
    induction h as [|h IH]; intros fuel xs Hcapacity.
    - destruct xs as [|x xs]; cbn [length Nat.pow] in Hcapacity; [|lia].
      pose proof (build_empty_time fuel). cbn [length]. nia.
    - destruct fuel as [|fuel]; [time_unfold T_build; nia|].
      destruct xs as [|x xs];
        [pose proof (build_empty_time (S fuel)); cbn [length]; nia|].
      set (input := x :: xs) in *.
      destruct (median_split input ltac:(unfold input; discriminate))
        as [pivot [rhs [Hskip [Hleftlength [Hlengths Hbalance]]]]].
      change (length input < 2 * 2 ^ h) in Hcapacity.
      pose proof (IH fuel (firstn (length input / 2) input)
        ltac:(rewrite Hleftlength; nia)) as Hleft.
      pose proof (IH fuel rhs ltac:(nia)) as Hright.
      pose proof (Std.Datatypes.T_length_le input) as Hlength.
      pose proof (div_time (length input) 2) as Hdiv.
      pose proof (firstn_time (length input / 2) input) as Hfirstn.
      pose proof (skipn_time (length input / 2) input) as Hskipn.
      rewrite Hleftlength in Hleft.
      time_unfold T_build. rewrite Hskip. nia.
  Qed.

  (** Sufficient construction fuel absorbs the extra logarithmic-capacity level. *)
  Lemma build_time : forall fuel xs, length xs <= fuel ->
    (T_build fuel xs <= 64 * N.of_nat
      (length xs * (Nat.log2 (length xs) + 1) + fuel + 1))%N.
  Proof.
    intros fuel xs Hfuel.
    pose proof (build_capacity_time (Nat.log2 (length xs) + 1) fuel xs
      (log_capacity (length xs))). nia.
  Qed.

  (** Lower search spends bounded comparison work along one path. *)
  Lemma below_time : forall tree bound z,
    Forall (fun x => zbits x <= bound) (vals tree) ->
    (T_below tree z <= 16 * N.of_nat (depth tree + 1) * N.of_nat (bound + 1))%N.
  Proof.
    induction tree as [|lhs IHleft value rhs IHright]; intros bound z Hbits.
    - time_unfold T_below. cbn [depth]. nia.
    - change (Forall (fun x => zbits x <= bound) (vals lhs ++ value :: vals rhs)) in Hbits.
      rewrite Forall_app in Hbits. destruct Hbits as [Hleft Hright].
      inversion Hright as [|v vs Hvalue Htail]; subst.
      specialize (IHleft bound z Hleft). specialize (IHright bound z Htail).
      change (Z.size_nat value <= bound) in Hvalue.
      pose proof (Std.Z.T_leb_le value z) as Hcompare.
      pose proof (Nat.le_max_l (depth lhs) (depth rhs)) as Hdepthleft.
      pose proof (Nat.le_max_r (depth lhs) (depth rhs)) as Hdepthright.
      time_unfold T_below. cbn [depth]. destruct (Z.leb value z).
      + destruct (below rhs z); nia.
      + nia.
  Qed.

  (** Upper search spends bounded comparison work along one path. *)
  Lemma above_time : forall tree bound z,
    Forall (fun x => zbits x <= bound) (vals tree) ->
    (T_above tree z <= 16 * N.of_nat (depth tree + 1) * N.of_nat (bound + 1))%N.
  Proof.
    induction tree as [|lhs IHleft value rhs IHright]; intros bound z Hbits.
    - time_unfold T_above. cbn [depth]. nia.
    - change (Forall (fun x => zbits x <= bound) (vals lhs ++ value :: vals rhs)) in Hbits.
      rewrite Forall_app in Hbits. destruct Hbits as [Hleft Hright].
      inversion Hright as [|v vs Hvalue Htail]; subst.
      specialize (IHleft bound z Hleft). specialize (IHright bound z Htail).
      change (Z.size_nat value <= bound) in Hvalue.
      pose proof (Std.Z.T_ltb_le value z) as Hcompare.
      pose proof (Std.Datatypes.T_negb_le (Z.ltb value z)) as Hnegate.
      pose proof (Nat.le_max_l (depth lhs) (depth rhs)) as Hdepthleft.
      pose proof (Nat.le_max_r (depth lhs) (depth rhs)) as Hdepthright.
      time_unfold T_above. cbn [depth]. destruct (Z.ltb value z); cbn [negb].
      + nia.
      + destruct (above lhs z); nia.
  Qed.
  (** Construction combines sorting, deduplication, and median splitting within one envelope. *)
  Lemma make_time : forall xs,
    (T_make xs <= 1024 * N.of_nat (length xs * (Nat.log2 (length xs) + 1) + 1) *
      N.of_nat (zb xs + 1))%N.
  Proof.
    intro xs. set (prepared := dedup_sorted (msort xs)).
    pose proof (msort_time xs) as Hsort.
    assert (Hsortedlength : length (msort xs) = length xs).
    { symmetry. apply Permutation_length, sort_fuel_perm. }
    pose proof (dedup_time (msort xs) (zb xs)
      (sort_bits (length xs) xs (zb xs)
        (proj1 (zb_spec xs (zb xs)) (Nat.le_refl _)))) as Hdedup.
    rewrite Hsortedlength in Hdedup.
    pose proof (build_time (length prepared) prepared (Nat.le_refl _)) as Hbuild.
    pose proof (Std.Datatypes.T_length_le prepared) as Hlength.
    pose proof (prepared_length xs) as Hprepared. fold prepared in Hprepared.
    pose proof (Nat.log2_le_mono (length prepared) (length xs) Hprepared) as Hlog.
    assert (Hsmall : (N.of_nat (length xs + 1) <=
      N.of_nat (length xs * (Nat.log2 (length xs) + 1) + 1))%N) by nia.
    assert (Hbuildsize : (N.of_nat (length prepared * (Nat.log2 (length prepared) + 1) +
      length prepared + 1) <=
      2 * N.of_nat (length xs * (Nat.log2 (length xs) + 1) + 1))%N) by nia.
    time_unfold T_make. fold prepared.
    remember (N.of_nat (length xs * (Nat.log2 (length xs) + 1) + 1)) as budget.
    clear Heqbudget Hlog Hsortedlength. nia.
  Qed.

  Definition c_thresholds : N := 1024%N.
  Definition k_sort : N := 256%N.
  Definition k_dedup : N := 4%N.
  Definition k_build : N := 64%N.
  Definition k_search : N := 16%N.

  (** Preparation charges comparison sorting and the largest stored integer. *)
  Lemma T_make_le : forall zs,
    (T_make zs <= c_thresholds * N.of_nat (length zs *
      (Nat.log2 (length zs) + 1) + 1) * N.of_nat (zb zs + 1))%N.
  Proof.
    unfold c_thresholds. apply make_time.
  Qed.

  (** Upper lookup charges a path and the stored thresholds' bit sizes. *)
  Lemma T_above_le : forall t z,
    (T_above t z <= c_thresholds * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof.
    intros t z. unfold c_thresholds.
    pose proof (above_time t (tree_bits t) z
      (proj1 (zb_spec (vals t) (tree_bits t)) (Nat.le_refl _))) as Htime. nia.
  Qed.

  (** Lower lookup charges a path and the stored thresholds' bit sizes. *)
  Lemma T_below_le : forall t z,
    (T_below t z <= c_thresholds * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof.
    intros t z. unfold c_thresholds.
    pose proof (below_time t (tree_bits t) z
      (proj1 (zb_spec (vals t) (tree_bits t)) (Nat.le_refl _))) as Htime. nia.
  Qed.

  (** Threshold preparation has the published comparison-sort complexity. *)
  Lemma make_complexity : (bigO (fun _ => True)
    (fun zs => N.of_nat
      (((length zs * (Nat.log2 (length zs) + 1) + 1) * (zb zs + 1))%nat)) T_make)%N.
  Proof.
    unfold bigO. exists c_thresholds. intros zs _. rewrite Nat2N.inj_mul.
    pose proof (T_make_le zs). nia.
  Qed.

  (** Upper search has the published path-times-bits class. *)
  Lemma above_complexity : bigO (X := ttree * Z) (fun _ => True)
    (fun x => N.of_nat (((depth (fst x) + 1) * (tree_bits (fst x) + 1))%nat))
    (fun x => T_above (fst x) (snd x)).
  Proof.
    exists c_thresholds. intros [tree z] _. cbn [fst snd].
    rewrite Nat2N.inj_mul. pose proof (T_above_le tree z) as Htime. nia.
  Qed.

  (** Lower search has the published path-times-bits class. *)
  Lemma below_complexity : bigO (X := ttree * Z) (fun _ => True)
    (fun x => N.of_nat (((depth (fst x) + 1) * (tree_bits (fst x) + 1))%nat))
    (fun x => T_below (fst x) (snd x)).
  Proof.
    exists c_thresholds. intros [tree z] _. cbn [fst snd].
    rewrite Nat2N.inj_mul. pose proof (T_below_le tree z) as Htime. nia.
  Qed.

  (** Merge sort orders every input list. *)
  Lemma msort_sorted : forall zs, Sorted Z.le (msort zs).
  Proof.
    intro zs. apply StronglySorted_Sorted, sort_fuel_sorted. lia.
  Qed.

  (** Merge sort keeps the input multiset. *)
  Lemma msort_perm : forall zs, Permutation zs (msort zs).
  Proof.
    intro zs. apply sort_fuel_perm.
  Qed.

  (** Deduplication keeps exactly the input values. *)
  Lemma dedup_vals : forall zs x, In x (dedup_sorted zs) <-> In x zs.
  Proof.
    apply dedup_vals_aux.
  Qed.

  (** Deduplication strengthens weak sortedness to strict sortedness. *)
  Lemma dedup_ordered : forall zs, Sorted Z.le zs ->
    StronglySorted Z.lt (dedup_sorted zs).
  Proof.
    intros zs Hsorted. apply dedup_ordered_aux, Sorted_StronglySorted; [|exact Hsorted].
    intros x y z Hxy Hyz. lia.
  Qed.

  (** Sufficient construction fuel preserves the inorder traversal. *)
  Lemma build_vals : forall fuel zs, length zs <= fuel ->
    vals (build fuel zs) = zs.
  Proof.
    apply build_vals_aux.
  Qed.

  (** Median construction has logarithmic depth. *)
  Lemma build_depth : forall fuel zs, length zs <= fuel ->
    depth (build fuel zs) <= Nat.log2 (length zs) + 1.
  Proof.
    intros fuel zs Hfuel. apply build_depth_aux.
  Qed.

  (** Increasing fuel to the original list length preserves the constructed tree. *)
  Lemma make_def : forall zs,
    make zs = build (length zs) (dedup_sorted (msort zs)).
  Proof.
    intro zs. unfold make. apply build_fuel_eq; [lia|apply prepared_length].
  Qed.

  (** Merge sort fits the declared logarithmic sorting envelope. *)
  Lemma T_msort_le : forall zs,
    (T_msort zs <= k_sort * N.of_nat
      (length zs * (Nat.log2 (length zs) + 1) + 1) *
      N.of_nat (zb zs + 1))%N.
  Proof.
    unfold k_sort. apply msort_time.
  Qed.

  (** Deduplication fits one pass of stored integer comparisons. *)
  Lemma T_dedup_sorted_le : forall zs,
    (T_dedup_sorted zs <= k_dedup * N.of_nat ((length zs + 1)%nat) *
      N.of_nat ((zb zs + 1)%nat))%N.
  Proof.
    intro zs. unfold k_dedup. apply dedup_time.
    apply (proj1 (zb_spec zs (zb zs))). reflexivity.
  Qed.

  (** Median construction fits the logarithmic splitting envelope. *)
  Lemma T_build_le : forall fuel zs, length zs <= fuel ->
    (T_build fuel zs <= k_build * N.of_nat
      ((length zs * (Nat.log2 (length zs) + 1) + fuel + 1)%nat))%N.
  Proof.
    unfold k_build. apply build_time.
  Qed.

  (** Upper lookup pays for one path of bounded comparisons. *)
  Lemma T_above_plan_le : forall t z,
    (T_above t z <= k_search * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof.
    intros t z. unfold k_search. apply above_time.
    apply (proj1 (zb_spec (vals t) (tree_bits t))). reflexivity.
  Qed.

  (** Lower lookup pays for one path of bounded comparisons. *)
  Lemma T_below_plan_le : forall t z,
    (T_below t z <= k_search * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof.
    intros t z. unfold k_search. apply below_time.
    apply (proj1 (zb_spec (vals t) (tree_bits t))). reflexivity.
  Qed.
End ThresholdsT.
