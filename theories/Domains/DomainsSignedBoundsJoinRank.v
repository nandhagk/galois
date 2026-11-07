(** * Explicit legacy join-widening credits

    The legacy choice has a finite exponential bound and scores normalized half spans.
    For example, semantically equal raw and reduced singleton halves have the same legacy rank.
    Builds on: DomainsSignedOrder, DomainsSignedWiden and DomainsTnumRank. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsTnum DomainsTnumRank DomainsSignedBounds
  DomainsSignedOrder DomainsSignedWiden.
Import Cost.Notations.

Local Open Scope nat_scope.

Definition sb_join_measure_c (w : width) (h : sb_half) : Cost.t nat :=
  match h with
  | SBEmpty => Cost.ret 0
  | SBRange t lo hi =>
    let* bits := tnum_rank_c w t in
    Cost.ret (1 + bits + Z.to_nat (hi - lo))
  end.

Definition sb_join_measure (w : width) (h : sb_half) : nat :=
  Cost.value (sb_join_measure_c w h).

Lemma sb_join_measure_equation : forall w h,
  sb_join_measure w h =
  match h with
  | SBEmpty => 0
  | SBRange t lo hi => 1 + tnum_rank w t + Z.to_nat (hi - lo)
  end.
Proof.
  intros w [|t lo hi]; unfold sb_join_measure, sb_join_measure_c;
    autorewrite with galois_cost; reflexivity.
Qed.

Definition sb_join_measure_bound (w : width) : nat :=
  1 + 2 * Pos.to_nat w + Z.to_nat (modulus w).

Lemma sb_join_reduced_bounds : forall w s h t lo hi,
  sb_reduce_half w s h = SBRange t lo hi -> (0 <= lo <= hi /\ hi < modulus w)%Z.
Proof.
  intros w s h t lo hi Hreduce. pose proof (sb_reduce_half_summary w s h) as Hsummary.
  rewrite Hreduce in Hsummary. destruct Hsummary as [_ [Hlo [Hhi [Hsound _]]]].
  pose proof (Hsound lo Hlo). pose proof (Hsound hi Hhi). unfold is_word in *. intuition lia.
Qed.

Lemma sb_join_measure_order : forall w a b,
  sb_order w a b = true -> sb_join_measure w a <= sb_join_measure w b.
Proof.
  intros w [|ta la ua] [|tb lb ub] Hle; rewrite sb_order_equation in Hle;
    rewrite !sb_join_measure_equation; try discriminate; try lia.
  rewrite !andb_true_iff, !Z.leb_le in Hle. destruct Hle as [[Ht Hl] Hu].
  pose proof (tnum_rank_monotone w ta tb Ht).
  assert (Hspan : Z.to_nat (ua - la) <= Z.to_nat (ub - lb)).
  { destruct (Z_le_dec 0 (ua - la)).
    - apply Z2Nat.inj_le; lia.
    - assert (Hzero : Z.to_nat (ua - la) = 0)
        by (destruct (ua - la)%Z; cbn; try reflexivity; lia).
      rewrite Hzero. lia. }
  lia.
Qed.

Definition sb_join_ordered (h : sb_half) : Prop :=
  match h with
  | SBEmpty => True
  | SBRange _ lo hi => (lo <= hi)%Z
  end.

Lemma sb_join_reduce_ordered : forall w s h, sb_join_ordered (sb_reduce_half w s h).
Proof.
  intros w s h. destruct (sb_reduce_half w s h) as [|t lo hi] eqn:Hreduce; [exact I|].
  pose proof (sb_join_reduced_bounds w s h t lo hi Hreduce). cbn [sb_join_ordered]. lia.
Qed.

Lemma sb_join_measure_equal : forall w a b,
  sb_join_ordered a -> sb_join_ordered b -> sb_order w a b = true ->
  sb_join_measure w a = sb_join_measure w b -> sb_order w b a = true.
Proof.
  intros w [|ta la ua] [|tb lb ub] Ha Hb Hle Heq;
    rewrite sb_order_equation in Hle |- *; rewrite !sb_join_measure_equation in Heq;
    try discriminate; try reflexivity.
  rewrite !andb_true_iff, !Z.leb_le in *. destruct Hle as [[Ht Hl] Hu].
  pose proof (tnum_rank_monotone w ta tb Ht) as Hrank.
  assert (Hspan : Z.to_nat (ua - la) <= Z.to_nat (ub - lb)).
  { cbn [sb_join_ordered] in Ha, Hb. apply Z2Nat.inj_le; lia. }
  assert (Hrankeq : tnum_rank w ta = tnum_rank w tb) by lia.
  assert (Hspaneq : Z.to_nat (ua - la) = Z.to_nat (ub - lb)) by lia.
  cbn [sb_join_ordered] in Ha, Hb.
  apply (f_equal Z.of_nat) in Hspaneq. rewrite !Z2Nat.id in Hspaneq by lia.
  split; [split; [now apply tnum_rank_equal|]|]; lia.
Qed.

Definition signed_bounds_join_measure_c (w : width) (a : signed_bounds) : Cost.t nat :=
  let* reduced := signed_bounds_reduce_c w a in
  let* zero := sb_join_measure_c w (sb_zero reduced) in
  let* one := sb_join_measure_c w (sb_one reduced) in
  Cost.ret (zero + one).

Definition signed_bounds_join_measure (w : width) (a : signed_bounds) : nat :=
  Cost.value (signed_bounds_join_measure_c w a).

Lemma signed_bounds_join_measure_equation : forall w a,
  signed_bounds_join_measure w a =
  sb_join_measure w (sb_reduce_half w false (sb_zero a)) +
    sb_join_measure w (sb_reduce_half w true (sb_one a)).
Proof.
  intros w a. unfold signed_bounds_join_measure, signed_bounds_join_measure_c.
  autorewrite with galois_cost.
  change (sb_join_measure w (sb_zero (signed_bounds_reduce w a)) +
    sb_join_measure w (sb_one (signed_bounds_reduce w a)) =
    sb_join_measure w (sb_reduce_half w false (sb_zero a)) +
      sb_join_measure w (sb_reduce_half w true (sb_one a))).
  rewrite signed_bounds_reduce_equation. reflexivity.
Qed.

Lemma signed_bounds_join_measure_bounded : forall w a,
  signed_bounds_join_measure w a <= 2 * sb_join_measure_bound w.
Proof.
  intros w a.
  assert (Hhalf : forall s h,
    sb_join_measure w (sb_reduce_half w s h) <= sb_join_measure_bound w).
  { intros s h. destruct (sb_reduce_half w s h) as [|t lo hi] eqn:Hreduce;
      rewrite sb_join_measure_equation; [unfold sb_join_measure_bound; lia|].
    pose proof (sb_join_reduced_bounds w s h t lo hi Hreduce).
    pose proof (tnum_rank_bounded w t).
    assert (Hspan : Z.to_nat (hi - lo) <= Z.to_nat (modulus w)).
    { apply Z2Nat.inj_le; pose proof (modulus_pos w); lia. }
    unfold sb_join_measure_bound. lia. }
  rewrite signed_bounds_join_measure_equation.
  pose proof (Hhalf false (sb_zero a)). pose proof (Hhalf true (sb_one a)). lia.
Qed.

Lemma signed_bounds_join_measure_monotone : forall w a b,
  signed_bounds_leb w a b = true ->
  signed_bounds_join_measure w a <= signed_bounds_join_measure w b.
Proof.
  intros w a b Hle. rewrite signed_bounds_leb_equation in Hle.
  apply andb_true_iff in Hle as [Hz Ho]. rewrite sb_leb_equation in Hz, Ho.
  apply sb_join_measure_order in Hz, Ho. rewrite !signed_bounds_join_measure_equation. lia.
Qed.

Lemma signed_bounds_join_measure_equal : forall w a b,
  signed_bounds_leb w a b = true ->
  signed_bounds_join_measure w a = signed_bounds_join_measure w b ->
  signed_bounds_leb w b a = true.
Proof.
  intros w a b Hle Heq. rewrite signed_bounds_leb_equation in Hle |- *.
  apply andb_true_iff in Hle as [Hz Ho]. rewrite sb_leb_equation in Hz, Ho.
  pose proof (sb_join_measure_order w _ _ Hz) as Hzero.
  pose proof (sb_join_measure_order w _ _ Ho) as Hone.
  rewrite !signed_bounds_join_measure_equation in Heq.
  apply andb_true_iff. split; rewrite sb_leb_equation; apply sb_join_measure_equal;
    try apply sb_join_reduce_ordered; try assumption; lia.
Qed.

Definition signed_bounds_join_wrank (w : width) (a : signed_bounds) : nat :=
  2 * sb_join_measure_bound w - signed_bounds_join_measure w a.

(** The explicit legacy choice has finite normalized credits with an exponential width bound. *)
Definition signed_bounds_join_widening_rank (w : width) :
  widening_rank_on (signed_bounds_lattice WidenJoin w) (fun _ => True).
Proof.
  refine {| wrank := signed_bounds_join_wrank w; wbound := 2 * sb_join_measure_bound w |}.
  - intros. unfold signed_bounds_join_wrank. lia.
  - intros a b _ _ _.
    pose proof (sb_widen_upper_l WidenJoin w a b) as Hupper.
    apply signed_bounds_join_measure_monotone in Hupper.
    change (signed_bounds_join_wrank w (sb_widen_with WidenJoin w a b) <=
      signed_bounds_join_wrank w a).
    unfold signed_bounds_join_wrank. lia.
  - intros a b _ _ Hescape.
    change (signed_bounds_leb w b a = false) in Hescape.
    pose proof (sb_widen_upper_l WidenJoin w a b) as Hleft.
    pose proof (sb_widen_upper_r WidenJoin w a b) as Hright.
    pose proof (signed_bounds_join_measure_monotone w _ _ Hleft) as Hmono.
    pose proof (signed_bounds_join_measure_bounded w (sb_widen_with WidenJoin w a b)).
    assert (Hstrict : signed_bounds_join_measure w a <
      signed_bounds_join_measure w (sb_widen_with WidenJoin w a b)).
    { destruct (Nat.eq_dec (signed_bounds_join_measure w a)
        (signed_bounds_join_measure w (sb_widen_with WidenJoin w a b))) as [Heq|Hne]; [|lia].
      pose proof (signed_bounds_join_measure_equal w _ _ Hleft Heq) as Hreverse.
      assert (Hba : signed_bounds_leb w b a = true).
      { exact (leb_trans (signed_bounds_join_laws w) b _ a Hright Hreverse). }
      congruence. }
    change (signed_bounds_join_wrank w (sb_widen_with WidenJoin w a b) <
      signed_bounds_join_wrank w a).
    unfold signed_bounds_join_wrank. lia.
Defined.
