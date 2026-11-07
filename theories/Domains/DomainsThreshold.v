(** * Balanced widening thresholds

    Preparation sorts and removes duplicate integers before splitting at each median.
    Each search follows one branch and charges one tick per visited node or empty leaf.
    For example, sorted input of a thousand thresholds has depth ten.
    Builds on: DomainsBound and CostMonad. *)

From Stdlib Require Import ZArith List Arith Lia Sorting.Sorted.
From Galois.Cost Require Import CostMonad.
From Galois.Domains Require Import DomainsBound.
Import List.ListNotations Cost.Notations.

Inductive threshold_tree : Type :=
  | ThresholdEmpty
  | ThresholdNode (left : threshold_tree) (value : Z) (right : threshold_tree).

Fixpoint threshold_values (tree : threshold_tree) : list Z :=
  match tree with
  | ThresholdEmpty => []
  | ThresholdNode lhs value rhs => value :: threshold_values lhs ++ threshold_values rhs
  end.

Fixpoint threshold_size (tree : threshold_tree) : nat :=
  match tree with
  | ThresholdEmpty => 0
  | ThresholdNode lhs _ rhs => S (threshold_size lhs + threshold_size rhs)
  end.

Fixpoint threshold_depth (tree : threshold_tree) : nat :=
  match tree with
  | ThresholdEmpty => 0
  | ThresholdNode lhs _ rhs => S (Nat.max (threshold_depth lhs) (threshold_depth rhs))
  end.

(** Ordering is strict, so each threshold has one node. *)
Fixpoint threshold_ordered (tree : threshold_tree) : Prop :=
  match tree with
  | ThresholdEmpty => True
  | ThresholdNode lhs value rhs =>
    threshold_ordered lhs /\ threshold_ordered rhs /\
    (forall x, In x (threshold_values lhs) -> (x < value)%Z) /\
    (forall x, In x (threshold_values rhs) -> (value < x)%Z)
  end.

(** Median balance requires child sizes to differ by at most one at every node. *)
Fixpoint threshold_balanced (tree : threshold_tree) : Prop :=
  match tree with
  | ThresholdEmpty => True
  | ThresholdNode lhs _ rhs =>
    threshold_balanced lhs /\ threshold_balanced rhs /\
    threshold_size rhs <= threshold_size lhs <= S (threshold_size rhs)
  end.

Fixpoint threshold_insert_list (z : Z) (xs : list Z) : list Z :=
  match xs with
  | [] => [z]
  | x :: rest =>
    if Z.eqb z x then xs
    else if Z.ltb z x then z :: xs else x :: threshold_insert_list z rest
  end.

(** The sorted reference contains every distinct input threshold. *)
Fixpoint threshold_list_ref (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest => threshold_insert_list x (threshold_list_ref rest)
  end.

Local Lemma insert_membership xs z x :
  In x (threshold_insert_list z xs) <-> x = z \/ In x xs.
Proof.
  induction xs as [|y ys IH]; cbn.
  - intuition congruence.
  - destruct (Z.eqb z y) eqn:Heq.
    + apply Z.eqb_eq in Heq. cbn. intuition congruence.
    + destruct (Z.ltb z y); cbn; rewrite ?IH; intuition congruence.
Qed.

Local Lemma insert_length xs z : length (threshold_insert_list z xs) <= S (length xs).
Proof.
  induction xs as [|x xs IH]; cbn; [lia|].
  destruct (Z.eqb z x), (Z.ltb z x); cbn; lia.
Qed.

Local Lemma insert_sorted xs z :
  StronglySorted Z.lt xs -> StronglySorted Z.lt (threshold_insert_list z xs).
Proof.
  intro Hsort. induction Hsort as [|x xs Hsort IH Hall]; cbn.
  - repeat constructor.
  - destruct (Z.eqb z x) eqn:Heq; [now constructor|].
    destruct (Z.ltb z x) eqn:Hlt.
    + apply Z.ltb_lt in Hlt. constructor; [now constructor|].
      constructor; [exact Hlt|]. rewrite Forall_forall in Hall |- *.
      intros y Hy. specialize (Hall y Hy). lia.
    + constructor; [exact IH|]. rewrite Forall_forall in Hall |- *.
      intros y Hy. apply insert_membership in Hy as [->|Hy].
      * apply Z.eqb_neq in Heq. apply Z.ltb_ge in Hlt. lia.
      * exact (Hall y Hy).
Qed.

(** Preparation preserves membership independently of input order and multiplicity. *)
Theorem threshold_list_ref_spec xs x : In x (threshold_list_ref xs) <-> In x xs.
Proof.
  induction xs as [|y ys IH]; cbn; [tauto|].
  rewrite insert_membership, IH. intuition congruence.
Qed.

Local Lemma list_ref_sorted xs : StronglySorted Z.lt (threshold_list_ref xs).
Proof.
  induction xs; cbn; [constructor|now apply insert_sorted].
Qed.

Local Lemma list_ref_length xs : length (threshold_list_ref xs) <= length xs.
Proof.
  induction xs as [|x xs IH]; cbn; [lia|].
  pose proof (insert_length (threshold_list_ref xs) x). lia.
Qed.

(** Fuel bounds recursion structurally and is initialized to the prepared list length. *)
Fixpoint threshold_build (fuel : nat) (xs : list Z) : threshold_tree :=
  match fuel with
  | 0 => ThresholdEmpty
  | S fuel =>
    let middle := length xs / 2 in
    match skipn middle xs with
    | [] => ThresholdEmpty
    | x :: rhs =>
      ThresholdNode (threshold_build fuel (firstn middle xs)) x (threshold_build fuel rhs)
    end
  end.

Definition threshold_of_list (xs : list Z) : threshold_tree :=
  let sorted := threshold_list_ref xs in threshold_build (length sorted) sorted.

Definition threshold_index := threshold_of_list.

Local Lemma median_split (xs : list Z) :
  xs <> [] ->
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

Local Lemma build_membership fuel xs :
  length xs <= fuel -> forall x, In x (threshold_values (threshold_build fuel xs)) <-> In x xs.
Proof.
  revert xs. induction fuel as [|fuel IH]; intros xs Hfuel x.
  - destruct xs; cbn in *; [tauto|lia].
  - destruct xs as [|y ys]; [cbn; tauto|].
    destruct (median_split (y :: ys) ltac:(discriminate))
      as [pivot [rhs [Hskip [Hleft [Hlength Hbalance]]]]].
    cbn [threshold_build]. rewrite Hskip. cbn [threshold_values In].
    rewrite in_app_iff, !IH by lia.
    pose proof (firstn_skipn (length (y :: ys) / 2) (y :: ys)) as Hsplit.
    rewrite Hskip in Hsplit.
    assert (Hin : In x (y :: ys) <->
      In x (firstn (length (y :: ys) / 2) (y :: ys)) \/ pivot = x \/ In x rhs).
    { rewrite <- Hsplit at 1. rewrite in_app_iff. reflexivity. }
    rewrite Hin. tauto.
Qed.

Local Lemma build_size fuel xs : length xs <= fuel ->
  threshold_size (threshold_build fuel xs) = length xs.
Proof.
  revert xs. induction fuel as [|fuel IH]; intros xs Hfuel.
  - destruct xs; cbn in *; lia.
  - destruct xs as [|y ys]; [reflexivity|].
    destruct (median_split (y :: ys) ltac:(discriminate))
      as [pivot [rhs [Hskip [Hleft [Hlength Hbalance]]]]].
    cbn [threshold_build]. rewrite Hskip. cbn [threshold_size].
    rewrite !IH by lia. lia.
Qed.

Local Lemma sorted_split lhs x rhs :
  StronglySorted Z.lt (lhs ++ x :: rhs) ->
  StronglySorted Z.lt lhs /\ StronglySorted Z.lt rhs /\
  (forall y, In y lhs -> (y < x)%Z) /\ (forall y, In y rhs -> (x < y)%Z).
Proof.
  induction lhs as [|a lhs IH]; cbn; intro Hsort.
  - inversion Hsort as [|a tail Htail Hall]; subst.
    repeat split; try constructor; try assumption; try contradiction.
    now rewrite <- Forall_forall.
  - inversion Hsort as [|a' tail Htail Hall]; subst.
    destruct (IH Htail) as [Hl [Hr [Hbelow Habove]]].
    rewrite Forall_forall in Hall.
    repeat split; try assumption.
    + constructor; [exact Hl|]. rewrite Forall_forall.
      intros y Hy. apply Hall. apply in_app_iff. now left.
    + intros y [<-|Hy].
      * apply Hall. apply in_app_iff. right. now left.
      * now apply Hbelow.
Qed.

Local Lemma build_wf fuel xs :
  length xs <= fuel -> StronglySorted Z.lt xs ->
  threshold_ordered (threshold_build fuel xs) /\ threshold_balanced (threshold_build fuel xs).
Proof.
  revert xs. induction fuel as [|fuel IH]; intros xs Hfuel Hsort.
  - destruct xs; cbn in *; tauto || lia.
  - destruct xs as [|y ys]; [cbn; tauto|].
    destruct (median_split (y :: ys) ltac:(discriminate))
      as [pivot [rhs [Hskip [Hleft [Hlength Hbalance]]]]].
    pose proof (firstn_skipn (length (y :: ys) / 2) (y :: ys)) as Hsplit.
    rewrite Hskip in Hsplit.
    rewrite <- Hsplit in Hsort.
    destruct (sorted_split _ _ _ Hsort) as [Hl [Hr [Hbelow Habove]]].
    destruct (IH (firstn (length (y :: ys) / 2) (y :: ys)) ltac:(lia) Hl) as [Hlo Hlb].
    destruct (IH rhs ltac:(lia) Hr) as [Hro Hrb].
    cbn [threshold_build]. rewrite Hskip. cbn [threshold_ordered threshold_balanced].
    split.
    + repeat split; try assumption.
      * intros x Hx. apply Hbelow.
        now apply (build_membership fuel (firstn (length (y :: ys) / 2) (y :: ys)) ltac:(lia)).
      * intros x Hx. apply Habove. now apply (build_membership fuel rhs ltac:(lia)).
    + repeat split; try assumption; rewrite !build_size by lia; lia.
Qed.

(** Prepared trees are strictly ordered and median balanced. *)
Theorem threshold_of_list_wf xs :
  threshold_ordered (threshold_of_list xs) /\ threshold_balanced (threshold_of_list xs).
Proof.
  apply build_wf; [lia|apply list_ref_sorted].
Qed.

(** Tree membership agrees with membership in the original list. *)
Theorem threshold_index_membership xs x :
  In x (threshold_values (threshold_index xs)) <-> In x xs.
Proof.
  unfold threshold_index, threshold_of_list.
  rewrite build_membership by lia. apply threshold_list_ref_spec.
Qed.

(** Preparation establishes the search invariant. *)
Theorem threshold_index_ordered xs : threshold_ordered (threshold_index xs).
Proof.
  apply threshold_of_list_wf.
Qed.

(** Every stored threshold came from the input. *)
Theorem threshold_index_values xs x :
  In x (threshold_values (threshold_index xs)) -> In x xs.
Proof.
  apply threshold_index_membership.
Qed.

(** Every input threshold is stored. *)
Theorem threshold_index_complete xs x :
  In x xs -> In x (threshold_values (threshold_index xs)).
Proof.
  apply threshold_index_membership.
Qed.

Local Lemma build_depth fuel xs h :
  length xs < 2 ^ h -> threshold_depth (threshold_build fuel xs) <= h.
Proof.
  revert xs h. induction fuel as [|fuel IH]; intros xs h Hcapacity; [cbn; lia|].
  destruct xs as [|y ys]; [cbn; lia|].
  destruct h as [|h]; [cbn in Hcapacity; lia|].
  destruct (median_split (y :: ys) ltac:(discriminate))
    as [pivot [rhs [Hskip [Hleft [Hlength Hbalance]]]]].
  cbn [threshold_build]. rewrite Hskip. cbn [threshold_depth].
  change (length (y :: ys) < 2 * 2 ^ h) in Hcapacity.
  apply le_n_S, Nat.max_lub; apply IH; nia.
Qed.

(** The depth is at most the ceiling of log2 of the input length plus one. *)
Theorem threshold_depth_bound xs :
  threshold_depth (threshold_of_list xs) <= Nat.log2_up (S (length xs)).
Proof.
  unfold threshold_of_list. apply build_depth.
  pose proof (list_ref_length xs).
  pose proof (Nat.log2_log2_up_spec (S (length xs)) ltac:(lia)).
  lia.
Qed.

(** A lower lookup follows one branch and combines its result with the visited threshold. *)
Fixpoint lower_threshold_c (tree : threshold_tree) (z : Z) : Cost.t bound :=
  Cost.step ;;
  match tree with
  | ThresholdEmpty => Cost.ret NegInf
  | ThresholdNode lhs value rhs =>
    if Z.leb value z
    then Cost.map (bound_max (Fin value)) (lower_threshold_c rhs z)
    else lower_threshold_c lhs z
  end.

Definition lower_threshold tree z := Cost.value (lower_threshold_c tree z).

(** An upper lookup follows one branch and combines its result with the visited threshold. *)
Fixpoint upper_threshold_c (tree : threshold_tree) (z : Z) : Cost.t bound :=
  Cost.step ;;
  match tree with
  | ThresholdEmpty => Cost.ret PosInf
  | ThresholdNode lhs value rhs =>
    if Z.leb z value
    then Cost.map (bound_min (Fin value)) (upper_threshold_c lhs z)
    else upper_threshold_c rhs z
  end.

Definition upper_threshold tree z := Cost.value (upper_threshold_c tree z).

(** The pure predecessor obeys the binary search equation. *)
Theorem lower_threshold_equation tree z :
  lower_threshold tree z =
  match tree with
  | ThresholdEmpty => NegInf
  | ThresholdNode lhs value rhs =>
    if Z.leb value z then bound_max (Fin value) (lower_threshold rhs z)
    else lower_threshold lhs z
  end.
Proof.
  unfold lower_threshold at 1.
  destruct tree; cbn [lower_threshold_c]; autorewrite with galois_cost;
    [reflexivity|].
  destruct (Z.leb value z); reflexivity.
Qed.

(** The pure successor obeys the binary search equation. *)
Theorem upper_threshold_equation tree z :
  upper_threshold tree z =
  match tree with
  | ThresholdEmpty => PosInf
  | ThresholdNode lhs value rhs =>
    if Z.leb z value then bound_min (Fin value) (upper_threshold lhs z)
    else upper_threshold rhs z
  end.
Proof.
  unfold upper_threshold at 1.
  destruct tree; cbn [upper_threshold_c]; autorewrite with galois_cost;
    [reflexivity|].
  destruct (Z.leb z value); reflexivity.
Qed.

(** Either lookup charges at most one tick for each level and the terminating empty leaf. *)
Theorem threshold_lookup_cost tree z :
  (Cost.ticks (lower_threshold_c tree z) <= N.of_nat (S (threshold_depth tree)))%N /\
  (Cost.ticks (upper_threshold_c tree z) <= N.of_nat (S (threshold_depth tree)))%N.
Proof.
  induction tree as [|lhs [Hll Hlu] value rhs [Hrl Hru]]; cbn [threshold_depth].
  - split; reflexivity.
  - cbn [lower_threshold_c upper_threshold_c]; autorewrite with galois_cost.
    destruct (Z.leb value z), (Z.leb z value); autorewrite with galois_cost;
      pose proof (Nat.le_max_l (threshold_depth lhs) (threshold_depth rhs));
      pose proof (Nat.le_max_r (threshold_depth lhs) (threshold_depth rhs)); lia.
Qed.

(** Prepared lookups charge at most one plus the ceiling logarithm of the input size plus one. *)
Theorem threshold_lookup_log_cost xs z :
  (Cost.ticks (lower_threshold_c (threshold_of_list xs) z) <=
    N.of_nat (S (Nat.log2_up (S (length xs)))))%N /\
  (Cost.ticks (upper_threshold_c (threshold_of_list xs) z) <=
    N.of_nat (S (Nat.log2_up (S (length xs)))))%N.
Proof.
  pose proof (threshold_lookup_cost (threshold_of_list xs) z) as [Hl Hu].
  pose proof (threshold_depth_bound xs). split; lia.
Qed.

Local Lemma threshold_node_values lhs value rhs x :
  In x (threshold_values (ThresholdNode lhs value rhs)) <->
  x = value \/ In x (threshold_values lhs) \/ In x (threshold_values rhs).
Proof.
  cbn. rewrite in_app_iff. intuition congruence.
Qed.

(** A finite predecessor is a stored threshold and a predecessor is never plus infinity. *)
Theorem lower_threshold_member : forall tree z,
  match lower_threshold tree z with
  | NegInf => True
  | Fin x => In x (threshold_values tree)
  | PosInf => False
  end.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intro z;
    rewrite lower_threshold_equation; cbn [threshold_values]; [exact I|].
  destruct (Z.leb value z).
  - specialize (IHright z). destruct (lower_threshold rhs z) as [|x|] eqn:Hresult;
      cbn [bound_max bound_leb] in *; try contradiction.
    + now left.
    + unfold bound_max, bound_leb. destruct (Z.leb value x); cbn;
        [right; apply in_app_iff; now right|now left].
  - specialize (IHleft z). destruct (lower_threshold lhs z); cbn in *; try contradiction;
      [exact I|right; apply in_app_iff; now left].
Qed.

(** A finite successor is a stored threshold and a successor is never minus infinity. *)
Theorem upper_threshold_member : forall tree z,
  match upper_threshold tree z with
  | NegInf => False
  | Fin x => In x (threshold_values tree)
  | PosInf => True
  end.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intro z;
    rewrite upper_threshold_equation; cbn [threshold_values]; [exact I|].
  destruct (Z.leb z value).
  - specialize (IHleft z). destruct (upper_threshold lhs z) as [|x|] eqn:Hresult;
      cbn [bound_min bound_leb] in *; try contradiction.
    + unfold bound_min, bound_leb. destruct (Z.leb value x); cbn;
        [now left|right; apply in_app_iff; now left].
    + now left.
  - specialize (IHright z). destruct (upper_threshold rhs z); cbn in *; try contradiction;
      [right; apply in_app_iff; now right|exact I].
Qed.

(** The predecessor is no greater than the query. *)
Theorem lower_threshold_lower : forall tree z,
  bound_leb (lower_threshold tree z) (Fin z) = true.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intro z;
    rewrite lower_threshold_equation; [reflexivity|].
  destruct (Z.leb value z) eqn:Hle; [|apply IHleft].
  apply bound_max_least; [exact Hle|apply IHright].
Qed.

(** The successor is no less than the query. *)
Theorem upper_threshold_upper : forall tree z,
  bound_leb (Fin z) (upper_threshold tree z) = true.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intro z;
    rewrite upper_threshold_equation; [reflexivity|].
  destruct (Z.leb z value) eqn:Hle; [|apply IHright].
  apply bound_min_greatest; [exact Hle|apply IHleft].
Qed.

(** Every eligible predecessor candidate is below the ordered search result. *)
Theorem lower_threshold_greatest : forall tree z x,
  threshold_ordered tree -> In x (threshold_values tree) -> (x <= z)%Z ->
  bound_leb (Fin x) (lower_threshold tree z) = true.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intros z x Hordered Hin Hxz.
  - contradiction.
  - cbn in Hordered. destruct Hordered as [Hleft [Hright [Hbelow Habove]]].
    apply threshold_node_values in Hin. rewrite lower_threshold_equation.
    destruct (Z.leb value z) eqn:Htest.
    + destruct Hin as [->|[Hin|Hin]].
      * apply bound_max_upper_l.
      * eapply bound_leb_trans; [|apply bound_max_upper_l].
        cbn. apply Z.leb_le. specialize (Hbelow x Hin). lia.
      * eapply bound_leb_trans; [apply IHright; eassumption|apply bound_max_upper_r].
    + apply Z.leb_gt in Htest. destruct Hin as [Heq|[Hin|Hin]].
      * lia.
      * now apply IHleft.
      * specialize (Habove x Hin). lia.
Qed.

(** Every eligible successor candidate is above the ordered search result. *)
Theorem upper_threshold_least : forall tree z x,
  threshold_ordered tree -> In x (threshold_values tree) -> (z <= x)%Z ->
  bound_leb (upper_threshold tree z) (Fin x) = true.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intros z x Hordered Hin Hzx.
  - contradiction.
  - cbn in Hordered. destruct Hordered as [Hleft [Hright [Hbelow Habove]]].
    apply threshold_node_values in Hin. rewrite upper_threshold_equation.
    destruct (Z.leb z value) eqn:Htest.
    + destruct Hin as [->|[Hin|Hin]].
      * apply bound_min_lower_l.
      * eapply bound_leb_trans; [apply bound_min_lower_r|apply IHleft; eassumption].
      * eapply bound_leb_trans; [apply bound_min_lower_l|].
        cbn. apply Z.leb_le. specialize (Habove x Hin). lia.
    + apply Z.leb_gt in Htest. destruct Hin as [Heq|[Hin|Hin]].
      * lia.
      * specialize (Hbelow x Hin). lia.
      * now apply IHright.
Qed.

(** The predecessor agrees with the greatest eligible member specification over the input list. *)
Theorem lower_threshold_spec : forall ts z,
  match lower_threshold (threshold_of_list ts) z with
  | NegInf => forall x, In x ts -> (z < x)%Z
  | Fin value => In value ts /\ (value <= z)%Z /\
      forall x, In x ts -> (x <= z)%Z -> (x <= value)%Z
  | PosInf => False
  end.
Proof.
  intros ts z.
  pose proof (lower_threshold_member (threshold_index ts) z) as Hmember.
  pose proof (lower_threshold_lower (threshold_index ts) z) as Hbound.
  assert (Hgreatest : forall x, In x ts -> (x <= z)%Z ->
    bound_leb (Fin x) (lower_threshold (threshold_index ts) z) = true).
  { intros x Hin Hxz.
    apply lower_threshold_greatest; [apply threshold_index_ordered| |exact Hxz].
    now apply threshold_index_complete. }
  change (match lower_threshold (threshold_index ts) z with
    | NegInf => forall x, In x ts -> (z < x)%Z
    | Fin value => In value ts /\ (value <= z)%Z /\
        forall x, In x ts -> (x <= z)%Z -> (x <= value)%Z
    | PosInf => False
    end).
  destruct (lower_threshold (threshold_index ts) z) as [|value|] eqn:Hresult; cbn in *.
  - intros x Hin. destruct (Z_le_gt_dec x z) as [Hxz|Hzx]; [|lia].
    specialize (Hgreatest x Hin Hxz). discriminate.
  - split; [now apply threshold_index_values|].
    apply Z.leb_le in Hbound. split; [exact Hbound|].
    intros x Hin Hxz. apply Z.leb_le. now apply Hgreatest.
  - exact Hmember.
Qed.

(** The successor agrees with the least eligible member specification over the input list. *)
Theorem upper_threshold_spec : forall ts z,
  match upper_threshold (threshold_of_list ts) z with
  | NegInf => False
  | Fin value => In value ts /\ (z <= value)%Z /\
      forall x, In x ts -> (z <= x)%Z -> (value <= x)%Z
  | PosInf => forall x, In x ts -> (x < z)%Z
  end.
Proof.
  intros ts z.
  pose proof (upper_threshold_member (threshold_index ts) z) as Hmember.
  pose proof (upper_threshold_upper (threshold_index ts) z) as Hbound.
  assert (Hleast : forall x, In x ts -> (z <= x)%Z ->
    bound_leb (upper_threshold (threshold_index ts) z) (Fin x) = true).
  { intros x Hin Hzx.
    apply upper_threshold_least; [apply threshold_index_ordered| |exact Hzx].
    now apply threshold_index_complete. }
  change (match upper_threshold (threshold_index ts) z with
    | NegInf => False
    | Fin value => In value ts /\ (z <= value)%Z /\
        forall x, In x ts -> (z <= x)%Z -> (value <= x)%Z
    | PosInf => forall x, In x ts -> (x < z)%Z
    end).
  destruct (upper_threshold (threshold_index ts) z) as [|value|] eqn:Hresult; cbn in *.
  - exact Hmember.
  - split; [now apply threshold_index_values|].
    apply Z.leb_le in Hbound. split; [exact Hbound|].
    intros x Hin Hzx. apply Z.leb_le. now apply Hleast.
  - intros x Hin. destruct (Z_le_gt_dec z x) as [Hzx|Hxz]; [|lia].
    specialize (Hleast x Hin Hzx). discriminate.
Qed.
