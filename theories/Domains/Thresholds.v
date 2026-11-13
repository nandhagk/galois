(** * Threshold trees

    Threshold trees store sorted distinct integers and search for nearby bounds.
    For example, the least threshold above four in [0; 8] is eight.
    Builds on: ThresholdsSig. *)

From Stdlib Require Import List ZArith Arith Lia Sorting.Sorted Sorting.Permutation.
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

  Fixpoint below (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if Z.leb value z then
        match below rhs z with
        | Some x => Some (Z.max value x)
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
        | Some x => Some (Z.min value x)
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
  Lemma dedup_vals : forall zs x, In x (dedup_sorted zs) <-> In x zs.
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
  Lemma dedup_ordered : forall zs, StronglySorted Z.le zs ->
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
    apply (proj1 (dedup_vals (b :: zs) z)) in Hin.
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
    - apply ordered_nodup, dedup_ordered, sort_fuel_sorted. lia.
    - intros z Hin. apply (proj1 (dedup_vals (msort zs) z)) in Hin.
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
  Lemma build_vals : forall fuel zs, length zs <= fuel -> vals (build fuel zs) = zs.
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
  Lemma build_depth : forall fuel zs,
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
    intros zs x. unfold make. rewrite build_vals by lia. rewrite dedup_vals.
    split; intro Hin; eapply Permutation_in; [|exact Hin| |exact Hin].
    - apply Permutation_sym, sort_fuel_perm.
    - apply sort_fuel_perm.
  Qed.
  (** Construction orders and deduplicates thresholds. *)
  Lemma make_ordered : forall zs, ordered (make zs).
  Proof.
    intro zs. unfold ordered, make. rewrite build_vals by lia.
    apply dedup_ordered, sort_fuel_sorted. lia.
  Qed.
  (** Construction produces a logarithmic-depth tree. *)
  Lemma make_depth : forall zs, depth (make zs) <= Nat.log2 (length zs) + 1.
  Proof.
    intro zs. unfold make. eapply Nat.le_trans; [apply build_depth|].
    apply Nat.add_le_mono_r, Nat.log2_le_mono, prepared_length.
  Qed.
  (** Upper search returns the least eligible threshold or proves none exists. *)
  Lemma above_spec : forall t z, ordered t ->
    match above t z with
    | Some u => In u (vals t) /\ (z <= u)%Z /\
      forall v, In v (vals t) -> (z <= v)%Z -> (u <= v)%Z
    | None => forall v, In v (vals t) -> (v < z)%Z
    end.
  Proof. Admitted. (* CONVERT: upper_threshold_least: No product even after head-reduction. *)
  (** Lower search returns the greatest eligible threshold or proves none exists. *)
  Lemma below_spec : forall t z, ordered t ->
    match below t z with
    | Some u => In u (vals t) /\ (u <= z)%Z /\
      forall v, In v (vals t) -> (v <= z)%Z -> (v <= u)%Z
    | None => forall v, In v (vals t) -> (z < v)%Z
    end.
  Proof. Admitted. (* CONVERT: lower_threshold_greatest: No product even after head-reduction. *)
  (** Upper search is sound even when the tree is unordered. *)
  Lemma above_sound : forall t z u,
    above t z = Some u -> In u (vals t) /\ (z <= u)%Z.
  Proof. Admitted. (* CONVERT: upper_threshold_member: In environment *)
  (** Lower search is sound even when the tree is unordered. *)
  Lemma below_sound : forall t z u,
    below t z = Some u -> In u (vals t) /\ (u <= z)%Z.
  Proof. Admitted. (* CONVERT: lower_threshold_member: In environment *)
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

  Definition c_thresholds : N := 1%N. (* STUB *)
  Definition k_sort : N := 1%N. (* STUB *)
  Definition k_dedup : N := 1%N. (* STUB *)
  Definition k_build : N := 1%N. (* STUB *)
  Definition k_search : N := 1%N. (* STUB *)

  Lemma T_make_le : forall zs,
    (T_make zs <= c_thresholds * N.of_nat (length zs *
      (Nat.log2 (length zs) + 1) + 1) * N.of_nat (zb zs + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_above_le : forall t z,
    (T_above t z <= c_thresholds * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_below_le : forall t z,
    (T_below t z <= c_thresholds * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma make_bigO : (bigO (fun _ => True)
    (fun zs => N.of_nat
      (((length zs * (Nat.log2 (length zs) + 1) + 1) * (zb zs + 1))%nat)) T_make)%N.
  Proof. Admitted. (* STUB *)

  Lemma F1_msort_sorted : forall zs, Sorted Z.le (msort zs).
  Proof. Admitted. (* STUB *)

  Lemma F2_msort_perm : forall zs, Permutation zs (msort zs).
  Proof. Admitted. (* STUB *)

  Lemma F3_dedup_vals : forall zs x, In x (dedup_sorted zs) <-> In x zs.
  Proof. Admitted. (* STUB *)

  Lemma F4_dedup_ordered : forall zs, Sorted Z.le zs ->
    StronglySorted Z.lt (dedup_sorted zs).
  Proof. Admitted. (* STUB *)

  Lemma F5_build_vals : forall fuel zs, length zs <= fuel ->
    vals (build fuel zs) = zs.
  Proof. Admitted. (* STUB *)

  Lemma F6_build_depth : forall fuel zs, length zs <= fuel ->
    depth (build fuel zs) <= Nat.log2 (length zs) + 1.
  Proof. Admitted. (* STUB *)

  Lemma F7_make_eq : forall zs,
    make zs = build (length zs) (dedup_sorted (msort zs)).
  Proof. Admitted. (* STUB *)

  Lemma T1_msort : forall zs,
    (T_msort zs <= k_sort * N.of_nat
      (length zs * (Nat.log2 (length zs) + 1) + 1) *
      N.of_nat (zb zs + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_dedup : forall zs,
    (T_dedup_sorted zs <= k_dedup * N.of_nat ((length zs + 1)%nat) *
      N.of_nat ((zb zs + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_build : forall fuel zs, length zs <= fuel ->
    (T_build fuel zs <= k_build * N.of_nat
      ((length zs * (Nat.log2 (length zs) + 1) + fuel + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_above : forall t z,
    (T_above t z <= k_search * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_below : forall t z,
    (T_below t z <= k_search * N.of_nat ((depth t + 1)%nat) *
      N.of_nat ((tree_bits t + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
End ThresholdsT.
