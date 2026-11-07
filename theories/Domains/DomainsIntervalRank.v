(** * Threshold widening progress

    Each outward endpoint movement consumes a threshold or reaches infinity.
    For example, duplicate input thresholds disappear during preparation and consume no extra rank.
    Builds on: DomainsInterval and LatticeHeight. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval.

Local Open Scope nat_scope.

Definition lower_count (ts : list Z) (z : Z) : nat :=
  length (filter (fun t => Z.ltb t z) ts).

Definition upper_count (ts : list Z) (z : Z) : nat :=
  length (filter (fun t => Z.ltb z t) ts).

Definition lower_rank (ts : list Z) (b : bound) : nat :=
  match b with
  | NegInf => 0
  | Fin z => S (lower_count ts z)
  | PosInf => S (length ts)
  end.

Definition upper_rank (ts : list Z) (b : bound) : nat :=
  match b with
  | NegInf => S (length ts)
  | Fin z => S (upper_count ts z)
  | PosInf => 0
  end.

Local Lemma lower_count_bounded ts z : lower_count ts z <= length ts.
Proof.
  unfold lower_count. induction ts as [|t rest IH]; cbn; [lia|].
  destruct (Z.ltb t z); cbn; lia.
Qed.

Local Lemma upper_count_bounded ts z : upper_count ts z <= length ts.
Proof.
  unfold upper_count. induction ts as [|t rest IH]; cbn; [lia|].
  destruct (Z.ltb z t); cbn; lia.
Qed.

Local Lemma lower_count_monotone ts x y : (x <= y)%Z ->
  lower_count ts x <= lower_count ts y.
Proof.
  intro Hxy. unfold lower_count. induction ts as [|t rest IH]; cbn; [lia|].
  destruct (Z.ltb t x) eqn:Htx, (Z.ltb t y) eqn:Hty; cbn; lia.
Qed.

Local Lemma upper_count_monotone ts x y : (x <= y)%Z ->
  upper_count ts y <= upper_count ts x.
Proof.
  intro Hxy. unfold upper_count. induction ts as [|t rest IH]; cbn; [lia|].
  destruct (Z.ltb y t) eqn:Hyt, (Z.ltb x t) eqn:Hxt; cbn; lia.
Qed.

Local Lemma lower_count_strict ts x y : In x ts -> (x < y)%Z ->
  lower_count ts x < lower_count ts y.
Proof.
  intros Hin Hxy. unfold lower_count. induction ts as [|t rest IH]; cbn in *.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst t. rewrite Z.ltb_irrefl.
      assert (Hlt : Z.ltb x y = true) by (apply Z.ltb_lt; exact Hxy).
      rewrite Hlt. cbn. pose proof (lower_count_monotone rest x y ltac:(lia)) as Hmono.
      unfold lower_count in Hmono. lia.
    + specialize (IH Hin). destruct (Z.ltb t x) eqn:Htx, (Z.ltb t y) eqn:Hty;
        cbn in *; lia.
Qed.

Local Lemma upper_count_strict ts x y : In y ts -> (x < y)%Z ->
  upper_count ts y < upper_count ts x.
Proof.
  intros Hin Hxy. unfold upper_count. induction ts as [|t rest IH]; cbn in *.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst t. rewrite Z.ltb_irrefl.
      assert (Hlt : Z.ltb x y = true) by (apply Z.ltb_lt; exact Hxy).
      rewrite Hlt. cbn. pose proof (upper_count_monotone rest x y ltac:(lia)) as Hmono.
      unfold upper_count in Hmono. lia.
    + specialize (IH Hin). destruct (Z.ltb y t) eqn:Hyt, (Z.ltb x t) eqn:Hxt;
        cbn in *; lia.
Qed.

Local Lemma lower_rank_monotone ts a b : bound_leb a b = true ->
  lower_rank ts a <= lower_rank ts b.
Proof.
  destruct a as [|x|], b as [|y|]; intro Hle; cbn in *; try discriminate; try lia.
  - apply Z.leb_le in Hle. pose proof (lower_count_monotone ts x y Hle). lia.
  - pose proof (lower_count_bounded ts x). lia.
Qed.

Local Lemma upper_rank_monotone ts a b : bound_leb a b = true ->
  upper_rank ts b <= upper_rank ts a.
Proof.
  destruct a as [|x|], b as [|y|]; intro Hle; cbn in *; try discriminate; try lia.
  - pose proof (upper_count_bounded ts y). lia.
  - apply Z.leb_le in Hle. pose proof (upper_count_monotone ts x y Hle). lia.
Qed.

Local Lemma lower_count_member_bound ts x : In x ts -> lower_count ts x < length ts.
Proof.
  intro Hin. induction ts as [|t rest IH]; cbn in Hin; [contradiction|].
  unfold lower_count in *. cbn. destruct Hin as [Heq|Hin].
  - subst t. rewrite Z.ltb_irrefl. pose proof (lower_count_bounded rest x) as Hbound.
    unfold lower_count in Hbound. cbn. lia.
  - specialize (IH Hin). destruct (Z.ltb t x); cbn; lia.
Qed.

Local Lemma upper_count_member_bound ts x : In x ts -> upper_count ts x < length ts.
Proof.
  intro Hin. induction ts as [|t rest IH]; cbn in Hin; [contradiction|].
  unfold upper_count in *. cbn. destruct Hin as [Heq|Hin].
  - subst t. rewrite Z.ltb_irrefl. pose proof (upper_count_bounded rest x) as Hbound.
    unfold upper_count in Hbound. cbn. lia.
  - specialize (IH Hin). destruct (Z.ltb x t); cbn; lia.
Qed.

Local Lemma widen_lower_progress ts old next :
  bound_leb old next = false ->
  lower_rank (threshold_values ts) (widen_lower ts old next) <
    lower_rank (threshold_values ts) old.
Proof.
  destruct old as [|x|], next as [|y|]; intro Hmove; cbn in Hmove; try discriminate;
    unfold widen_lower; cbn [bound_leb]; try rewrite Hmove; cbn [lower_rank]; try lia.
  - pose proof (lower_threshold_lower ts y) as Hlower.
    pose proof (lower_threshold_member ts y) as Hmember.
    destruct (lower_threshold ts y) as [|r|] eqn:Hresult;
      cbn in *; try contradiction; try lia.
    apply Z.leb_le in Hlower. apply Z.leb_gt in Hmove.
    pose proof (lower_count_strict (threshold_values ts) r x Hmember ltac:(lia)). lia.
  - pose proof (lower_threshold_member ts y) as Hmember.
    destruct (lower_threshold ts y) as [|r|] eqn:Hresult;
      cbn in *; try contradiction; try lia.
    pose proof (lower_count_member_bound (threshold_values ts) r Hmember). lia.
Qed.

Local Lemma widen_upper_progress ts old next :
  bound_leb next old = false ->
  upper_rank (threshold_values ts) (widen_upper ts old next) <
    upper_rank (threshold_values ts) old.
Proof.
  destruct old as [|x|], next as [|y|]; intro Hmove; cbn in Hmove; try discriminate;
    unfold widen_upper; cbn [bound_leb]; try rewrite Hmove; cbn [upper_rank]; try lia.
  - pose proof (upper_threshold_member ts y) as Hmember.
    destruct (upper_threshold ts y) as [|r|] eqn:Hresult;
      cbn in *; try contradiction; try lia.
    pose proof (upper_count_member_bound (threshold_values ts) r Hmember). lia.
  - pose proof (upper_threshold_upper ts y) as Hupper.
    pose proof (upper_threshold_member ts y) as Hmember.
    destruct (upper_threshold ts y) as [|r|] eqn:Hresult;
      cbn in *; try contradiction; try lia.
    apply Z.leb_le in Hupper. apply Z.leb_gt in Hmove.
    pose proof (upper_count_strict (threshold_values ts) x r Hmember ltac:(lia)). lia.
Qed.

(** Bottom has one more credit than any endpoint pair. *)
Definition interval_rank (ts : list Z) (i : interval) : nat :=
  match i with
  | IBot => S (2 * S (length ts))
  | Itv l h => lower_rank ts l + upper_rank ts h
  end.

Local Lemma interval_rank_bound ts i :
  interval_rank ts i <= S (2 * S (length ts)).
Proof.
  destruct i as [|l h]; cbn [interval_rank]; [lia|].
  destruct l as [|x|], h as [|y|]; cbn [lower_rank upper_rank];
    try pose proof (lower_count_bounded ts x);
    try pose proof (upper_count_bounded ts y); lia.
Qed.

(** The endpoint invariant admits infinities and finite endpoints in the unsigned word range. *)
Definition interval_word_invariant (w : width) (i : interval) : Prop :=
  let endpoint b :=
    match b with
    | Fin z => is_word w z
    | _ => True
    end in
  match i with
  | IBot => True
  | Itv lo hi => endpoint lo /\ endpoint hi
  end.

(** Threshold widening decreases a bounded rank on all payloads, hence on word-range payloads. *)
Theorem interval_widening_rank_on ts w :
  widening_rank_on (interval_lattice ts) (interval_word_invariant w).
Proof.
  refine {| wrank := interval_rank (threshold_values ts);
            wbound := S (2 * S (length (threshold_values ts))) |}.
  - intros a _. apply interval_rank_bound.
  - intros a b _ _ Hle.
    change (interval_leb b a = true) in Hle.
    change (interval_rank (threshold_values ts) (interval_widen ts a b) <=
      interval_rank (threshold_values ts) a).
    destruct a as [|la ha], b as [|lb hb];
      cbn [interval_rank interval_widen interval_leb] in *; try discriminate; try lia.
    pose proof (lower_rank_monotone (threshold_values ts) _ _
      (widen_lower_old ts la lb)) as Hlower.
    pose proof (upper_rank_monotone (threshold_values ts) _ _
      (widen_upper_old ts ha hb)) as Hupper. exact (Nat.add_le_mono _ _ _ _ Hlower Hupper).
  - intros a b _ _ Hle.
    change (interval_leb b a = false) in Hle.
    change (interval_rank (threshold_values ts) (interval_widen ts a b) <
      interval_rank (threshold_values ts) a).
    destruct a as [|la ha], b as [|lb hb];
      cbn [interval_rank interval_widen interval_leb] in *; try discriminate; try lia.
    + destruct lb as [|x|], hb as [|y|]; cbn [lower_rank upper_rank];
        try pose proof (lower_count_bounded (threshold_values ts) x);
        try pose proof (upper_count_bounded (threshold_values ts) y); lia.
    + apply andb_false_iff in Hle as [Hlower|Hupper].
      * pose proof (widen_lower_progress ts la lb Hlower) as Hstrict.
        pose proof (upper_rank_monotone (threshold_values ts) _ _
          (widen_upper_old ts ha hb)) as Hstable. lia.
      * pose proof (lower_rank_monotone (threshold_values ts) _ _
          (widen_lower_old ts la lb)) as Hstable.
        pose proof (widen_upper_progress ts ha hb Hupper) as Hstrict. lia.
Defined.
