(** * Selectable signed-bound widening

    Doubling expands a changed hemisphere by its current size without reducing its interval.
    For example, widening [0,0] toward [0,1] expands the positive hemisphere to [0,2].
    Builds on: DomainsSignedOrder, DomainsTnumRank and the public Cost combinators. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit.
From Galois.Domains Require Import DomainsTnum DomainsTnumRank DomainsSignedBounds
  DomainsSignedOrder.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

(** Join is the legacy choice and doubling is the selected default policy. *)
Inductive sb_widening : Type :=
  | WidenJoin
  | WidenDouble
  | WidenThresholds (ts : list Z).

Definition sb_floor (w : width) (s : bool) : Z := if s then half w else 0.

Definition sb_ceiling (w : width) (s : bool) : Z :=
  if s then modulus w - 1 else half w - 1.

(** A word of the selected sign lies within the hemisphere endpoints. *)
Theorem sb_sign_bounds : forall w s z,
  is_word w z -> msb w z = s -> sb_floor w s <= z <= sb_ceiling w s.
Proof.
  intros w s z Hw Hs. rewrite msb_half, (wrap_id w z Hw) in Hs.
  unfold sb_floor, sb_ceiling. destruct s.
  - apply negb_true_iff, Z.ltb_ge in Hs. unfold is_word in Hw. lia.
  - apply negb_false_iff, Z.ltb_lt in Hs. unfold is_word in Hw. lia.
Qed.

(** Threshold scans charge every visited list cell and keep the nearest admissible endpoint. *)
Fixpoint sb_threshold_lower_c (ts : list Z) (x best : Z) : Cost.t Z :=
  match ts with
  | [] => Cost.ret best
  | t :: rest =>
    Cost.step ;;
    sb_threshold_lower_c rest x (if t <=? x then Z.max best t else best)
  end.

Fixpoint sb_threshold_upper_c (ts : list Z) (x best : Z) : Cost.t Z :=
  match ts with
  | [] => Cost.ret best
  | t :: rest =>
    Cost.step ;;
    sb_threshold_upper_c rest x (if x <=? t then Z.min best t else best)
  end.

Lemma sb_threshold_lower_bound : forall ts x best,
  best <= x -> Cost.value (sb_threshold_lower_c ts x best) <= x.
Proof.
  intro ts. induction ts as [|t rest IH]; intros x best Hbest; [exact Hbest|].
  cbn [sb_threshold_lower_c]. autorewrite with galois_cost. apply IH.
  destruct (t <=? x) eqn:Ht; [apply Z.leb_le in Ht; lia|exact Hbest].
Qed.

Lemma sb_threshold_upper_bound : forall ts x best,
  x <= best -> x <= Cost.value (sb_threshold_upper_c ts x best).
Proof.
  intro ts. induction ts as [|t rest IH]; intros x best Hbest; [exact Hbest|].
  cbn [sb_threshold_upper_c]. autorewrite with galois_cost. apply IH.
  destruct (x <=? t) eqn:Ht; [apply Z.leb_le in Ht; lia|exact Hbest].
Qed.

Definition sb_double_half (w : width) (s : bool) (a b : sb_half) : sb_half :=
  match a, b with
  | SBEmpty, _ => b
  | _, SBEmpty => a
  | SBRange ta la ua, SBRange tb lb ub =>
    let bits := tnum_join w ta tb in
    if (la <=? lb) && (ub <=? ua) then SBRange bits la ua else
    let size := Z.max 1 (ua - la + 1) in
    SBRange bits
      (Z.max (sb_floor w s) (Z.min la lb - size))
      (Z.min (sb_ceiling w s) (Z.max ua ub + size))
  end.

Definition sb_threshold_half_c (ts : list Z) (w : width) (s : bool) (a b : sb_half)
    : Cost.t sb_half :=
  match a, b with
  | SBEmpty, _ => Cost.ret b
  | _, SBEmpty => Cost.ret a
  | SBRange ta la ua, SBRange tb lb ub =>
    let bits := tnum_join w ta tb in
    let* lo := sb_threshold_lower_c ts (Z.min la lb)
      (Z.min (sb_floor w s) (Z.min la lb)) in
    let* hi := sb_threshold_upper_c ts (Z.max ua ub)
      (Z.max (sb_ceiling w s) (Z.max ua ub)) in
    Cost.ret (SBRange bits (Z.max (sb_floor w s) lo) (Z.min (sb_ceiling w s) hi))
  end.

(** Doubling encloses both raw halves even when an input's endpoints are malformed. *)
Theorem sb_double_half_upper : forall w s a b z,
  sb_half_gamma w s a z \/ sb_half_gamma w s b z ->
  sb_half_gamma w s (sb_double_half w s a b) z.
Proof.
  intros w s [|ta la ua] [|tb lb ub] z Hz;
    cbn [sb_double_half];
    try solve [destruct Hz as [Hz|Hz]; try exact Hz; exfalso; exact (proj1 Hz)].
  rewrite !sb_half_gamma_range in *.
  assert (Hword : is_word w z) by tauto.
  assert (Hsign : msb w z = s) by tauto.
  pose proof (sb_sign_bounds w s z Hword Hsign) as Hhemisphere.
  assert (Ht : tnum_gamma w (tnum_join w ta tb) z)
    by (apply tnum_join_sound; tauto).
  destruct ((la <=? lb) && (ub <=? ua)) eqn:Hinside.
  - apply andb_true_iff in Hinside as [Hl Hu]. apply Z.leb_le in Hl, Hu.
    apply sb_half_gamma_range. intuition lia.
  - apply sb_half_gamma_range. split; [exact Hword|]. split; [exact Hsign|].
    split; [exact Ht|]. destruct Hz as [Hz|Hz];
      pose proof (Z.le_min_l la lb); pose proof (Z.le_min_r la lb);
      pose proof (Z.le_max_l ua ub); pose proof (Z.le_max_r ua ub);
      pose proof (Z.le_max_l 1 (ua - la + 1)); intuition lia.
Qed.

(** Threshold widening encloses both raw halves while retaining the full threshold scans. *)
Theorem sb_threshold_half_upper : forall ts w s a b z,
  sb_half_gamma w s a z \/ sb_half_gamma w s b z ->
  sb_half_gamma w s (Cost.value (sb_threshold_half_c ts w s a b)) z.
Proof.
  intros ts w s [|ta la ua] [|tb lb ub] z Hz;
    cbn [sb_threshold_half_c];
    try solve [destruct Hz as [Hz|Hz]; try exact Hz; exfalso; exact (proj1 Hz)].
  autorewrite with galois_cost. rewrite !sb_half_gamma_range in *.
  assert (Hword : is_word w z) by tauto.
  assert (Hsign : msb w z = s) by tauto.
  pose proof (sb_sign_bounds w s z Hword Hsign) as Hhemisphere.
  pose proof (sb_threshold_lower_bound ts (Z.min la lb)
    (Z.min (sb_floor w s) (Z.min la lb)) (Z.le_min_r _ _)) as Hl.
  pose proof (sb_threshold_upper_bound ts (Z.max ua ub)
    (Z.max (sb_ceiling w s) (Z.max ua ub)) (Z.le_max_r _ _)) as Hu.
  split; [exact Hword|]. split; [exact Hsign|]. split.
  - apply tnum_join_sound. tauto.
  - destruct Hz as [Hz|Hz]; pose proof (Z.le_min_l la lb);
      pose proof (Z.le_min_r la lb); pose proof (Z.le_max_l ua ub);
      pose proof (Z.le_max_r ua ub); intuition lia.
Qed.

(** The selected widening is data and never consumes a soundness or termination proof. *)
Definition sb_widen_with_c (strategy : sb_widening) (w : width)
    (a b : signed_bounds) : Cost.t signed_bounds :=
  match strategy with
  | WidenJoin => signed_bounds_join_c w a b
  | WidenDouble =>
    Cost.step ;;
    Cost.ret (SignedBounds
      (sb_double_half w false (sb_zero a) (sb_zero b))
      (sb_double_half w true (sb_one a) (sb_one b)))
  | WidenThresholds ts =>
    let* zero := sb_threshold_half_c ts w false (sb_zero a) (sb_zero b) in
    let* one := sb_threshold_half_c ts w true (sb_one a) (sb_one b) in
    Cost.ret (SignedBounds zero one)
  end.

Definition sb_widen_with (strategy : sb_widening) (w : width)
    (a b : signed_bounds) : signed_bounds := Cost.value (sb_widen_with_c strategy w a b).

Lemma sb_widen_upper : forall strategy w a b z,
  signed_bounds_gamma w a z \/ signed_bounds_gamma w b z ->
  signed_bounds_gamma w (sb_widen_with strategy w a b) z.
Proof.
  intros strategy w a b z Hz. destruct strategy.
  - apply signed_bounds_join_sound. exact Hz.
  - change (signed_bounds_gamma w
      (SignedBounds (sb_double_half w false (sb_zero a) (sb_zero b))
        (sb_double_half w true (sb_one a) (sb_one b))) z).
    unfold signed_bounds_gamma in *. cbn [sb_zero sb_one].
    destruct Hz as [[Hz|Hz]|[Hz|Hz]];
      first [left; apply sb_double_half_upper; tauto
      |right; apply sb_double_half_upper; tauto].
  - unfold sb_widen_with, sb_widen_with_c. autorewrite with galois_cost.
    unfold signed_bounds_gamma in *. cbn [sb_zero sb_one].
    destruct Hz as [[Hz|Hz]|[Hz|Hz]];
      first [left; apply sb_threshold_half_upper; tauto
      |right; apply sb_threshold_half_upper; tauto].
Qed.

(** Every widening choice contains its left input under the total semantic order. *)
Theorem sb_widen_upper_l : forall strategy w a b,
  signed_bounds_leb w a (sb_widen_with strategy w a b) = true.
Proof.
  intros strategy w a b. apply signed_bounds_leb_spec. intros z Hz.
  apply sb_widen_upper. now left.
Qed.

(** Every widening choice contains its right input under the total semantic order. *)
Theorem sb_widen_upper_r : forall strategy w a b,
  signed_bounds_leb w b (sb_widen_with strategy w a b) = true.
Proof.
  intros strategy w a b. apply signed_bounds_leb_spec. intros z Hz.
  apply sb_widen_upper. now right.
Qed.

(** Exact reduction preserves the meaning of the actual selected widening result.
    The default does not apply that interval reduction during its ascending iteration. *)
Theorem sb_widen_gamma : forall strategy w a b z,
  signed_bounds_gamma w (signed_bounds_reduce w (sb_widen_with strategy w a b)) z <->
  signed_bounds_gamma w (sb_widen_with strategy w a b) z.
Proof.
  intros. apply signed_bounds_reduce_gamma.
Qed.

(** Selected widening replaces only the base dictionary's widening callback. *)
Definition signed_bounds_lattice (strategy : sb_widening) (w : width)
    : lattice signed_bounds :=
  with_widen_c (signed_bounds_join_lattice w) (sb_widen_with_c strategy w).

(** Every selected dictionary obeys the weak lattice laws for arbitrary raw values. *)
Theorem signed_bounds_laws : forall strategy w,
  lattice_laws (signed_bounds_lattice strategy w).
Proof.
  intros strategy w. apply with_widen_c_laws.
  - apply signed_bounds_join_laws.
  - apply sb_widen_upper_l.
  - apply sb_widen_upper_r.
Qed.

(** Widening readiness constrains endpoints, and leaves raw masks unrestricted. *)
Definition sb_widen_ready (w : width) (s : bool) (h : sb_half) : Prop :=
  match h with
  | SBEmpty => True
  | SBRange _ lo hi => sb_floor w s <= lo /\ lo <= hi /\ hi <= sb_ceiling w s
  end.

Definition signed_bounds_widen_ready (w : width) (a : signed_bounds) : Prop :=
  sb_widen_ready w false (sb_zero a) /\ sb_widen_ready w true (sb_one a).

Lemma sb_capacity : forall w s, sb_ceiling w s - sb_floor w s + 1 = half w.
Proof.
  intros w s. unfold sb_floor, sb_ceiling. pose proof (modulus_half w).
  destruct s; lia.
Qed.

Lemma sb_capacity_bounds : forall w s,
  0 < sb_ceiling w s - sb_floor w s + 1 <= modulus w.
Proof.
  intros w s. rewrite sb_capacity. pose proof (half_pos w).
  pose proof (modulus_half w). lia.
Qed.

(** The exact reducer produces valid endpoint ranges for the widening invariant. *)
Theorem sb_reduce_half_widen_ready : forall w s h,
  sb_widen_ready w s (sb_reduce_half w s h).
Proof.
  intros w s h. pose proof (sb_reduce_half_summary w s h) as Hsummary.
  destruct (sb_reduce_half w s h) as [|t lo hi]; [exact I|].
  destruct Hsummary as [_ [Hlo [Hhi [Hsound _]]]].
  pose proof (sb_half_word_sign w s h lo Hlo) as [Hwlo Hslo].
  pose proof (sb_half_word_sign w s h hi Hhi) as [Hwhi Hshi].
  pose proof (sb_sign_bounds w s lo Hwlo Hslo).
  pose proof (sb_sign_bounds w s hi Hwhi Hshi).
  pose proof (Hsound lo Hlo). cbn [sb_widen_ready]. intuition lia.
Qed.

(** Exact payload reduction establishes the endpoint invariant for arbitrary raw payloads. *)
Theorem signed_bounds_reduce_widen_ready : forall w a,
  signed_bounds_widen_ready w (signed_bounds_reduce w a).
Proof.
  intros w a. rewrite signed_bounds_reduce_equation.
  split; apply sb_reduce_half_widen_ready.
Qed.

Lemma sb_double_endpoints : forall l u la ua lb ub,
  l <= la -> la <= ua -> ua <= u ->
  let d := ua - la + 1 in
  let nextlo := Z.max l (Z.min la lb - d) in
  let nexthi := Z.min u (Z.max ua ub + d) in
  l <= nextlo /\ nextlo <= la /\ ua <= nexthi /\ nexthi <= u /\
    (nexthi - nextlo + 1 = u - l + 1 \/ 2 * d <= nexthi - nextlo + 1).
Proof.
  intros l u la ua lb ub Hla Hordered Hua. cbn zeta.
  pose proof (Z.le_min_l la lb) as Hmin.
  pose proof (Z.le_max_l ua ub) as Hmax.
  destruct (Z_le_dec (Z.min la lb - (ua - la + 1)) l) as [Hleft|Hleft];
    destruct (Z_le_dec u (Z.max ua ub + (ua - la + 1))) as [Hright|Hright];
    rewrite ?Z.max_l, ?Z.max_r, ?Z.min_l, ?Z.min_r by lia;
    intuition lia.
Qed.

(** Doubling preserves valid endpoint ranges without running interval reduction. *)
Theorem sb_double_half_ready : forall w s a b,
  sb_widen_ready w s a -> sb_widen_ready w s b ->
  sb_widen_ready w s (sb_double_half w s a b).
Proof.
  intros w s [|ta la ua] [|tb lb ub] Ha Hb; cbn [sb_double_half] in *; try assumption.
  destruct ((la <=? lb) && (ub <=? ua)); [exact Ha|].
  cbn [sb_widen_ready] in *. rewrite (Z.max_r 1 (ua - la + 1)) by lia.
  destruct Ha as [Hl [Ho Hu]].
  pose proof (sb_double_endpoints (sb_floor w s) (sb_ceiling w s)
    la ua lb ub Hl Ho Hu). cbn zeta in *. intuition lia.
Qed.

Definition sb_size_score (w : width) (s : bool) (size : Z) : Z :=
  if size =? sb_ceiling w s - sb_floor w s + 1 then Zpos w + 1 else Z.log2 size.

Lemma sb_size_score_bounds : forall w s size,
  0 < size <= sb_ceiling w s - sb_floor w s + 1 ->
  0 <= sb_size_score w s size <= Zpos w + 1.
Proof.
  intros w s size Hsize. unfold sb_size_score.
  destruct (size =? sb_ceiling w s - sb_floor w s + 1); [lia|].
  pose proof (sb_capacity_bounds w s).
  pose proof (Z.log2_nonneg size).
  pose proof (Z.log2_le_mono size (modulus w) ltac:(lia)).
  rewrite modulus_log2 in *. lia.
Qed.

Lemma sb_size_score_monotone : forall w s old next,
  0 < old <= next -> next <= sb_ceiling w s - sb_floor w s + 1 ->
  sb_size_score w s old <= sb_size_score w s next.
Proof.
  intros w s old next Hold Hnext.
  pose proof (sb_size_score_bounds w s old ltac:(lia)) as Hbound.
  unfold sb_size_score in *.
  destruct (next =? sb_ceiling w s - sb_floor w s + 1) eqn:Hnextfull; [lia|].
  destruct (old =? sb_ceiling w s - sb_floor w s + 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. apply Z.eqb_neq in Hnextfull. lia.
  - apply Z.log2_le_mono. lia.
Qed.

Lemma sb_size_score_progress : forall w s old next,
  0 < old < sb_ceiling w s - sb_floor w s + 1 ->
  0 < next <= sb_ceiling w s - sb_floor w s + 1 ->
  (next = sb_ceiling w s - sb_floor w s + 1 \/ 2 * old <= next) ->
  sb_size_score w s old < sb_size_score w s next.
Proof.
  intros w s old next Hold Hnext Hgrow.
  assert (Hproper : (old =? sb_ceiling w s - sb_floor w s + 1) = false)
    by (apply Z.eqb_neq; lia).
  pose proof (sb_capacity_bounds w s).
  pose proof (Z.log2_le_mono old (modulus w) ltac:(lia)) as Hlogold.
  rewrite modulus_log2 in Hlogold.
  unfold sb_size_score. rewrite Hproper.
  destruct (next =? sb_ceiling w s - sb_floor w s + 1) eqn:Hfull; [lia|].
  apply Z.eqb_neq in Hfull. assert (Hdouble : 2 * old <= next) by tauto.
  pose proof (Z.log2_le_mono (2 * old) next Hdouble) as Hlog.
  rewrite Z.log2_double in Hlog by lia. lia.
Qed.

Definition sb_half_score_c (w : width) (s : bool) (h : sb_half) : Cost.t Z :=
  match h with
  | SBEmpty => Cost.ret 0
  | SBRange t lo hi =>
    let* bits := tnum_rank_c w t in
    Cost.ret (1 + Z.of_nat bits + sb_size_score w s (hi - lo + 1))
  end.

Definition sb_half_score (w : width) (s : bool) (h : sb_half) : Z :=
  Cost.value (sb_half_score_c w s h).

(** The score combines bit-fact loss with logarithmic size growth and a saturation jump. *)
Theorem sb_half_score_equation : forall w s h,
  sb_half_score w s h =
  match h with
  | SBEmpty => 0
  | SBRange t lo hi => 1 + Z.of_nat (tnum_rank w t) + sb_size_score w s (hi - lo + 1)
  end.
Proof.
  intros w s [|t lo hi]; unfold sb_half_score, sb_half_score_c;
    autorewrite with galois_cost; reflexivity.
Qed.

Lemma sb_half_score_bounds : forall w s h,
  sb_widen_ready w s h -> 0 <= sb_half_score w s h <= 3 * Zpos w + 2.
Proof.
  intros w s [|t lo hi] Hready; rewrite sb_half_score_equation; [lia|].
  destruct Hready as [Hl [Ho Hu]].
  pose proof (tnum_rank_bounded w t) as Hbits.
  apply Nat2Z.inj_le in Hbits. rewrite Nat2Z.inj_mul, positive_nat_Z in Hbits.
  change (Z.of_nat (tnum_rank w t) <= 2 * Zpos w) in Hbits.
  pose proof (sb_size_score_bounds w s (hi - lo + 1) ltac:(lia)). lia.
Qed.

Lemma sb_double_size_progress : forall w s la ua lb ub,
  sb_floor w s <= la -> la <= ua -> ua <= sb_ceiling w s ->
  sb_floor w s <= lb -> lb <= ub -> ub <= sb_ceiling w s ->
  (la <=? lb) && (ub <=? ua) = false ->
  sb_size_score w s (ua - la + 1) <
    sb_size_score w s
      (Z.min (sb_ceiling w s) (Z.max ua ub + (ua - la + 1)) -
        Z.max (sb_floor w s) (Z.min la lb - (ua - la + 1)) + 1).
Proof.
  intros w s la ua lb ub Hla Ho Hua Hlb Hob Hub Hescape.
  pose proof (sb_double_endpoints (sb_floor w s) (sb_ceiling w s)
    la ua lb ub Hla Ho Hua) as Hendpoints. cbn zeta in Hendpoints.
  assert (Hproper : ua - la + 1 < sb_ceiling w s - sb_floor w s + 1).
  { apply andb_false_iff in Hescape as [Hbad|Hbad];
      apply Z.leb_gt in Hbad; lia. }
  apply sb_size_score_progress; intuition lia.
Qed.

(** Every actual doubling result has a nondecreasing combined score on ready inputs. *)
Theorem sb_double_score_monotone : forall w s a b,
  sb_widen_ready w s a -> sb_widen_ready w s b ->
  sb_half_score w s a <= sb_half_score w s (sb_double_half w s a b).
Proof.
  intros w s [|ta la ua] [|tb lb ub] Ha Hb; cbn [sb_double_half].
  - lia.
  - pose proof (sb_half_score_bounds w s (SBRange tb lb ub) Hb).
    rewrite sb_half_score_equation. lia.
  - lia.
  - rewrite (sb_half_score_equation w s (SBRange ta la ua)).
    pose proof (tnum_rank_monotone w ta (tnum_join w ta tb)
      (join_upper_l (tnum_laws w) ta tb)) as Hbits.
    apply Nat2Z.inj_le in Hbits.
    destruct ((la <=? lb) && (ub <=? ua)) eqn:Hinside;
      rewrite sb_half_score_equation; [lia|].
    cbn [sb_widen_ready] in Ha, Hb.
    rewrite (Z.max_r 1 (ua - la + 1)) by lia.
    destruct Ha as [Hl [Ho Hu]], Hb as [Hlb [Hob Hub]].
    pose proof (sb_double_size_progress w s la ua lb ub Hl Ho Hu Hlb Hob Hub Hinside).
    lia.
Qed.

(** Equal scores force the actual widening result below the old half in component order. *)
Theorem sb_double_score_equal : forall w s a b,
  sb_widen_ready w s a -> sb_widen_ready w s b ->
  sb_half_score w s a = sb_half_score w s (sb_double_half w s a b) ->
  sb_order w (sb_double_half w s a b) a = true.
Proof.
  intros w s [|ta la ua] [|tb lb ub] Ha Hb Heq; cbn [sb_double_half] in *.
  - reflexivity.
  - rewrite !sb_half_score_equation in Heq.
    pose proof (sb_size_score_bounds w s (ub - lb + 1)
      ltac:(cbn [sb_widen_ready] in Hb; lia)). lia.
  - rewrite sb_order_equation, !Z.leb_refl, (leb_refl (tnum_laws w)). reflexivity.
  - rewrite (sb_half_score_equation w s (SBRange ta la ua)) in Heq.
    pose proof (tnum_rank_monotone w ta (tnum_join w ta tb)
      (join_upper_l (tnum_laws w) ta tb)) as Hbits.
    destruct ((la <=? lb) && (ub <=? ua)) eqn:Hinside.
    + rewrite sb_half_score_equation in Heq.
      rewrite sb_order_equation, !Z.leb_refl, !andb_true_r.
      apply (tnum_rank_equal w ta (tnum_join w ta tb)).
      * apply (join_upper_l (tnum_laws w)).
      * lia.
    + rewrite sb_half_score_equation in Heq. cbn [sb_widen_ready] in Ha, Hb.
      rewrite (Z.max_r 1 (ua - la + 1)) in Heq by lia.
      destruct Ha as [Hl [Ho Hu]], Hb as [Hlb [Hob Hub]].
      pose proof (sb_double_size_progress w s la ua lb ub Hl Ho Hu Hlb Hob Hub Hinside).
      apply Nat2Z.inj_le in Hbits. lia.
Qed.

Definition signed_bounds_score_c (w : width) (a : signed_bounds) : Cost.t Z :=
  let* zero := sb_half_score_c w false (sb_zero a) in
  let* one := sb_half_score_c w true (sb_one a) in
  Cost.ret (zero + one).

Definition signed_bounds_score (w : width) (a : signed_bounds) : Z :=
  Cost.value (signed_bounds_score_c w a).

Definition signed_bounds_wrank (w : width) (a : signed_bounds) : nat :=
  Z.to_nat (6 * Zpos w + 4 - signed_bounds_score w a).

Definition signed_bounds_wbound (w : width) : nat := (6 * Pos.to_nat w + 4)%nat.

Lemma signed_bounds_score_equation : forall w a,
  signed_bounds_score w a =
  sb_half_score w false (sb_zero a) + sb_half_score w true (sb_one a).
Proof.
  intros w a. unfold signed_bounds_score, signed_bounds_score_c.
  autorewrite with galois_cost. reflexivity.
Qed.

Lemma signed_bounds_score_bounds : forall w a,
  signed_bounds_widen_ready w a -> 0 <= signed_bounds_score w a <= 6 * Zpos w + 4.
Proof.
  intros w a [Hz Ho]. rewrite signed_bounds_score_equation.
  pose proof (sb_half_score_bounds w false (sb_zero a) Hz).
  pose proof (sb_half_score_bounds w true (sb_one a) Ho). lia.
Qed.

Lemma signed_bounds_double_score : forall w a b,
  signed_bounds_widen_ready w a -> signed_bounds_widen_ready w b ->
  signed_bounds_score w a <= signed_bounds_score w (sb_widen_with WidenDouble w a b).
Proof.
  intros w a b [Haz Hao] [Hbz Hbo]. rewrite !signed_bounds_score_equation.
  change (sb_half_score w false (sb_zero a) + sb_half_score w true (sb_one a) <=
    sb_half_score w false (sb_double_half w false (sb_zero a) (sb_zero b)) +
    sb_half_score w true (sb_double_half w true (sb_one a) (sb_one b))).
  pose proof (sb_double_score_monotone w false _ _ Haz Hbz).
  pose proof (sb_double_score_monotone w true _ _ Hao Hbo). lia.
Qed.

(** The rank drops on every semantically strict widening input without assuming progress. *)
Theorem sb_widen_rank_decreases : forall w a b,
  signed_bounds_widen_ready w a -> signed_bounds_widen_ready w b ->
  signed_bounds_leb w b a = false ->
  (signed_bounds_wrank w (sb_widen_with WidenDouble w a b) < signed_bounds_wrank w a)%nat.
Proof.
  intros w a b Ha Hb Hescape.
  pose proof (signed_bounds_double_score w a b Ha Hb) as Hmono.
  assert (Hready : signed_bounds_widen_ready w (sb_widen_with WidenDouble w a b)).
  { destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. split;
      apply sb_double_half_ready; assumption. }
  pose proof (signed_bounds_score_bounds w a Ha) as Ha_bound.
  pose proof (signed_bounds_score_bounds w _ Hready) as Hb_bound.
  assert (Hstrict : signed_bounds_score w a <
    signed_bounds_score w (sb_widen_with WidenDouble w a b)).
  { destruct (Z.eq_dec (signed_bounds_score w a)
      (signed_bounds_score w (sb_widen_with WidenDouble w a b))) as [Heq|Hne]; [|lia].
    destruct Ha as [Haz Hao], Hb as [Hbz Hbo].
    rewrite !signed_bounds_score_equation in Heq.
    change (sb_half_score w false (sb_zero a) + sb_half_score w true (sb_one a) =
      sb_half_score w false (sb_double_half w false (sb_zero a) (sb_zero b)) +
      sb_half_score w true (sb_double_half w true (sb_one a) (sb_one b))) in Heq.
    pose proof (sb_double_score_monotone w false _ _ Haz Hbz) as Hzmono.
    pose proof (sb_double_score_monotone w true _ _ Hao Hbo) as Homono.
    pose proof (sb_double_score_equal w false _ _ Haz Hbz ltac:(lia)) as Hzreverse.
    pose proof (sb_double_score_equal w true _ _ Hao Hbo ltac:(lia)) as Horeverse.
    assert (Hreverse : signed_bounds_leb w (sb_widen_with WidenDouble w a b) a = true).
    { apply signed_bounds_leb_spec. intros z [Hz|Hz].
      - left. eapply sb_order_sound; [exact Hzreverse|exact Hz].
      - right. eapply sb_order_sound; [exact Horeverse|exact Hz]. }
    assert (Hba : signed_bounds_leb w b a = true).
    { exact (leb_trans (signed_bounds_join_laws w) b _ a
        (sb_widen_upper_r WidenDouble w a b) Hreverse). }
    congruence. }
  unfold signed_bounds_wrank. apply Z2Nat.inj_lt; lia.
Qed.

(** The selected doubling rank is bounded by a linear polynomial in the word width. *)
Definition signed_bounds_widening_rank_on (w : width) :
  widening_rank_on (signed_bounds_lattice WidenDouble w) (signed_bounds_widen_ready w).
Proof.
  refine {| wrank := signed_bounds_wrank w; wbound := signed_bounds_wbound w |}.
  - intros a Ha. pose proof (signed_bounds_score_bounds w a Ha).
    unfold signed_bounds_wrank, signed_bounds_wbound.
    apply Nat2Z.inj_le. rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, positive_nat_Z.
    change (6 * Zpos w + 4 - signed_bounds_score w a <= 6 * Zpos w + 4). lia.
  - intros a b Ha Hb _. pose proof (signed_bounds_double_score w a b Ha Hb).
    assert (Hready : signed_bounds_widen_ready w (sb_widen_with WidenDouble w a b)).
    { destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. split;
        apply sb_double_half_ready; assumption. }
    pose proof (signed_bounds_score_bounds w _ Hready).
    pose proof (signed_bounds_score_bounds w a Ha).
    change (signed_bounds_wrank w (sb_widen_with WidenDouble w a b) <=
      signed_bounds_wrank w a)%nat.
    unfold signed_bounds_wrank. apply Z2Nat.inj_le; lia.
  - intros a b Ha Hb Hescape. apply sb_widen_rank_decreases; assumption.
Defined.

(** The default dictionary preserves readiness under bottom, join, widening and narrowing. *)
Theorem signed_bounds_widen_ready_closed : forall w,
  closed_on (signed_bounds_lattice WidenDouble w) (signed_bounds_widen_ready w).
Proof.
  intro w. constructor.
  - split; exact I.
  - intros a b _ _.
    change (signed_bounds_widen_ready w (signed_bounds_join w a b)).
    rewrite signed_bounds_join_equation. split; rewrite sb_join_equation;
      apply sb_reduce_half_widen_ready.
  - intros a b [Haz Hao] [Hbz Hbo]. split; apply sb_double_half_ready; assumption.
  - intros a b _ _ _.
    change (signed_bounds_widen_ready w (signed_bounds_reduce w a)).
    apply signed_bounds_reduce_widen_ready.
Qed.
