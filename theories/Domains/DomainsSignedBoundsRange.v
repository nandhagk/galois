(** * Local modular range pieces

    Inclusive integer ranges project to at most two unsigned pieces without enumerating words.
    For example, projecting [14,17] at width four gives [14,15] and [0,1].
    Builds on: DomainsSignedBounds and public Bits modular equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsTnum DomainsTnumCompare DomainsSignedBounds
  DomainsSignedOrder.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

(** Piece meaning keeps integer endpoints separate from word-range validity. *)
Definition sb_ranges_gamma (w : width) (rs : list sb_range) (z : Z) : Prop :=
  is_word w z /\ exists r, In r rs /\ sb_range_gamma r z.

(** The width-indexed payload interpretation leaves word validity to the shared payload relation. *)
Definition sb_range_pgamma (_ : width) (r : sb_range) (z : Z) : Prop := sb_range_gamma r z.

Definition sb_mod_ranges (w : width) (lo hi : Z) : list sb_range :=
  if hi <? lo then [] else
  if modulus w - 1 <=? hi - lo then [(0, modulus w - 1)] else
  let l := wrap w lo in
  let h := wrap w hi in
  if l <=? h then [(l, h)] else [(l, modulus w - 1); (0, h)].

Definition sb_mod_size (w : width) (lo hi : Z) : Z :=
  if hi <? lo then 0 else Z.min (modulus w) (hi - lo + 1).

Lemma sb_wrap_translate : forall w lo z,
  wrap w z = wrap w (wrap w lo + (z - lo)).
Proof.
  intros w lo z. replace z with (lo + (z - lo)) at 1 by ring.
  apply wrap_add_left.
Qed.

Lemma sb_wrap_one_subtract : forall w z,
  modulus w <= z < 2 * modulus w -> wrap w z = z - modulus w.
Proof.
  intros w z Hz. rewrite wrap_mod. symmetry. apply Z.mod_unique with (q := 1).
  - left. lia.
  - ring.
Qed.

(** Projecting a finite integer range covers every modular image of that range. *)
Theorem sb_mod_ranges_sound : forall w lo hi z,
  lo <= z <= hi -> sb_ranges_gamma w (sb_mod_ranges w lo hi) (wrap w z).
Proof.
  intros w lo hi z Hz. unfold sb_mod_ranges, sb_ranges_gamma.
  split; [apply wrap_is_word|].
  rewrite (proj2 (Z.ltb_ge hi lo)) by lia.
  destruct (modulus w - 1 <=? hi - lo) eqn:Hfull.
  - exists (0, modulus w - 1). split; [now left|].
    pose proof (wrap_is_word w z). unfold sb_range_gamma, is_word in *. cbn [fst snd]. lia.
  - apply Z.leb_gt in Hfull.
    pose proof (wrap_is_word w lo) as Hlo.
    assert (Hhi_translate : wrap w hi = wrap w (wrap w lo + (hi - lo)))
      by apply sb_wrap_translate.
    assert (Hz_translate : wrap w z = wrap w (wrap w lo + (z - lo)))
      by apply sb_wrap_translate.
    destruct (Z_lt_ge_dec (wrap w lo + (hi - lo)) (modulus w)) as [Hfit|Hcross].
    + rewrite (wrap_id w (wrap w lo + (hi - lo))) in Hhi_translate by
        (unfold is_word in *; lia).
      rewrite Hhi_translate, (proj2 (Z.leb_le _ _)) by lia.
      exists (wrap w lo, wrap w lo + (hi - lo)). split; [now left|].
      rewrite Hz_translate, (wrap_id w (wrap w lo + (z - lo))) by
        (unfold is_word in *; lia).
      unfold sb_range_gamma. cbn [fst snd]. lia.
    + rewrite (sb_wrap_one_subtract w (wrap w lo + (hi - lo))) in Hhi_translate by
        (unfold is_word in Hlo; lia).
      rewrite Hhi_translate, (proj2 (Z.leb_gt _ _)) by lia.
      destruct (Z_lt_ge_dec (wrap w lo + (z - lo)) (modulus w)) as [Hzfit|Hzcross].
      * exists (wrap w lo, modulus w - 1). split; [now left|].
        rewrite Hz_translate, (wrap_id w (wrap w lo + (z - lo))) by
          (unfold is_word in *; lia).
        unfold sb_range_gamma. cbn [fst snd]. lia.
      * exists (0, wrap w lo + (hi - lo) - modulus w). split; [right; now left|].
        rewrite Hz_translate, (sb_wrap_one_subtract w (wrap w lo + (z - lo))) by
          (unfold is_word in Hlo; lia).
        unfold sb_range_gamma. cbn [fst snd]. lia.
Qed.

Definition sb_checked_ranges (w : width) (lo hi : Z) : list sb_range :=
  if (0 <=? lo) && (hi <? modulus w) then [(lo, hi)] else [(0, modulus w - 1)].

Definition sb_checked_range (w : width) (lo hi : Z) : sb_range :=
  if (0 <=? lo) && (hi <? modulus w) then (lo, hi) else (0, modulus w - 1).

Lemma sb_checked_ranges_pair : forall w lo hi,
  sb_checked_ranges w lo hi = [sb_checked_range w lo hi].
Proof.
  intros w lo hi. unfold sb_checked_ranges, sb_checked_range.
  destruct ((0 <=? lo) && (hi <? modulus w)); reflexivity.
Qed.

Lemma sb_single_range_gamma : forall w r z,
  sb_ranges_gamma w [r] z -> sb_range_gamma r z.
Proof.
  intros w r z [_ [q [[<-|Hnone] Hq]]]; [exact Hq|contradiction].
Qed.

(** Checked bounds retain a fitting unsigned range and use the word top when they do not fit. *)
Theorem sb_checked_ranges_sound : forall w lo hi z,
  is_word w z -> lo <= z <= hi -> sb_ranges_gamma w (sb_checked_ranges w lo hi) z.
Proof.
  intros w lo hi z Hw Hz. split; [exact Hw|]. unfold sb_checked_ranges.
  destruct ((0 <=? lo) && (hi <? modulus w)).
  - exists (lo, hi). split; [now left|exact Hz].
  - exists (0, modulus w - 1). split; [now left|].
    unfold sb_range_gamma, is_word in *. cbn [fst snd]. lia.
Qed.

Lemma sb_checked_range_sound : forall w lo hi z,
  is_word w z -> lo <= z <= hi -> sb_range_gamma (sb_checked_range w lo hi) z.
Proof.
  intros w lo hi z Hw Hz.
  pose proof (sb_checked_ranges_sound w lo hi z Hw Hz) as H.
  rewrite sb_checked_ranges_pair in H. now apply sb_single_range_gamma in H.
Qed.

(** Checked projection retains a fitting integer range and otherwise uses the word top. *)
Theorem sb_checked_ranges_wrapped_sound : forall w lo hi z,
  lo <= z <= hi -> sb_ranges_gamma w (sb_checked_ranges w lo hi) (wrap w z).
Proof.
  intros w lo hi z Hz. unfold sb_checked_ranges.
  destruct ((0 <=? lo) && (hi <? modulus w)) eqn:Hfit.
  - apply andb_true_iff in Hfit as [Hl Hu]. apply Z.leb_le in Hl. apply Z.ltb_lt in Hu.
    assert (Hword : is_word w z) by (unfold is_word; lia).
    rewrite (wrap_id w z Hword). split; [exact Hword|].
    exists (lo, hi). split; [now left|exact Hz].
  - split; [apply wrap_is_word|]. exists (0, modulus w - 1). split; [now left|].
    pose proof (wrap_is_word w z). unfold sb_range_gamma, is_word in *. cbn [fst snd]. lia.
Qed.

Definition sb_lift_c (w : width) (t : tnum) (lo hi : Z) : Cost.t signed_bounds :=
  signed_bounds_reduce_c w (SignedBounds (SBRange t lo hi) (SBRange t lo hi)).

Definition sb_lift (w : width) (t : tnum) (lo hi : Z) : signed_bounds :=
  Cost.value (sb_lift_c w t lo hi).

(** Lifting splits and exactly reduces a bit/range conjunction at the sign pole. *)
Theorem sb_lift_gamma : forall w t lo hi z,
  signed_bounds_gamma w (sb_lift w t lo hi) z <->
  is_word w z /\ tnum_gamma w t z /\ lo <= z <= hi.
Proof.
  intros w t lo hi z.
  change (signed_bounds_gamma w
    (signed_bounds_reduce w (SignedBounds (SBRange t lo hi) (SBRange t lo hi))) z <->
    is_word w z /\ tnum_gamma w t z /\ lo <= z <= hi).
  rewrite signed_bounds_reduce_gamma. unfold signed_bounds_gamma. cbn [sb_zero sb_one].
  rewrite !sb_half_gamma_range. destruct (msb w z); tauto.
Qed.

Definition sb_from_ranges_c (w : width) (t : tnum) (rs : list sb_range)
    : Cost.t signed_bounds :=
  fold_right_c
    (fun r acc =>
      Cost.step ;;
      let* a := sb_lift_c w t (fst r) (snd r) in
      signed_bounds_join_c w a acc)
    (SignedBounds SBEmpty SBEmpty) rs.

Definition sb_from_ranges (w : width) (t : tnum) (rs : list sb_range) : signed_bounds :=
  Cost.value (sb_from_ranges_c w t rs).

(** Building a payload from pieces charges each piece and every complete reduction/join callee. *)
Theorem sb_from_ranges_equation : forall w t rs,
  sb_from_ranges w t rs =
  fold_right (fun r acc => signed_bounds_join w (sb_lift w t (fst r) (snd r)) acc)
    (SignedBounds SBEmpty SBEmpty) rs.
Proof.
  intros w t rs. unfold sb_from_ranges, sb_from_ranges_c. rewrite value_fold_right_c.
  reflexivity.
Qed.

(** Every feasible piece remains represented after exact per-half hull construction. *)
Theorem sb_from_ranges_sound : forall w t rs z,
  tnum_gamma w t z -> sb_ranges_gamma w rs z ->
  signed_bounds_gamma w (sb_from_ranges w t rs) z.
Proof.
  intros w t rs z Ht [Hw [r [Hin Hr]]]. rewrite sb_from_ranges_equation.
  induction rs as [|a rest IH]; [contradiction|].
  cbn [fold_right]. apply signed_bounds_join_sound.
  destruct Hin as [<-|Hin].
  - left. apply sb_lift_gamma. split; [exact Hw|]. split; [exact Ht|exact Hr].
  - right. now apply IH.
Qed.

Definition signed_bounds_top_c (w : width) : Cost.t signed_bounds :=
  Cost.step ;;
  Cost.ret (SignedBounds (SBRange (Tnum (half w) 0) 0 (half w - 1))
    (SBRange (Tnum 0 (half w)) (half w) (modulus w - 1))).

Definition signed_bounds_top (w : width) : signed_bounds :=
  Cost.value (signed_bounds_top_c w).

(** The reduced top describes exactly all words of the supplied width. *)
Theorem signed_bounds_top_sound : forall w z,
  is_word w z -> signed_bounds_gamma w (signed_bounds_top w) z.
Proof.
  intros w z Hz. unfold signed_bounds_top, signed_bounds_top_c.
  autorewrite with galois_cost. unfold signed_bounds_gamma. cbn [sb_zero sb_one].
  destruct (msb w z) eqn:Hsign.
  - right. apply sb_half_gamma_range. split; [exact Hz|]. split; [exact Hsign|]. split.
    + rewrite tnum_half_value. change (tnum_gamma w (sb_bit (Zpos w - 1) true) z).
      apply sb_bit_gamma_exact; [lia|]. now rewrite <- msb_testbit.
    + rewrite msb_half, (wrap_id w z Hz) in Hsign.
      apply negb_true_iff, Z.ltb_ge in Hsign. unfold is_word in Hz. lia.
  - left. apply sb_half_gamma_range. split; [exact Hz|]. split; [exact Hsign|]. split.
    + rewrite tnum_half_value. change (tnum_gamma w (sb_bit (Zpos w - 1) false) z).
      apply sb_bit_gamma_exact; [lia|]. now rewrite <- msb_testbit.
    + rewrite msb_half, (wrap_id w z Hz) in Hsign.
      apply negb_false_iff, Z.ltb_lt in Hsign. unfold is_word in Hz. lia.
Qed.

Definition signed_bounds_const_c (w : width) (z : Z) : Cost.t signed_bounds :=
  sb_lift_c w (tnum_const w z) (wrap w z) (wrap w z).

Definition signed_bounds_const (w : width) (z : Z) : signed_bounds :=
  Cost.value (signed_bounds_const_c w z).

(** The reduced singleton describes the normalized integer. *)
Theorem signed_bounds_const_sound : forall w z,
  signed_bounds_gamma w (signed_bounds_const w z) (wrap w z).
Proof.
  intros w z. apply sb_lift_gamma. split; [apply wrap_is_word|].
  split; [apply tnum_const_sound|lia].
Qed.

Definition sb_range_valid (w : width) (r : sb_range) : bool :=
  (0 <=? fst r) && (fst r <=? snd r) && (snd r <? modulus w).

Lemma sb_range_valid_bounds : forall w r,
  sb_range_valid w r = true -> 0 <= fst r <= snd r /\ snd r < modulus w.
Proof.
  intros w r Hvalid. unfold sb_range_valid in Hvalid.
  rewrite !andb_true_iff in Hvalid. destruct Hvalid as [[Hl Ho] Hu].
  apply Z.leb_le in Hl, Ho. apply Z.ltb_lt in Hu. lia.
Qed.

Definition sb_range_cover_ordered (w : width) (low high : sb_range) (prefer_linear : bool)
    : list sb_range :=
  let linear := snd high - fst low + 1 in
  let circular := modulus w - fst high + snd low + 1 in
  if (linear <? circular) || ((linear =? circular) && prefer_linear)
  then sb_mod_ranges w (fst low) (snd high)
  else sb_mod_ranges w (fst high) (snd low + modulus w).

Lemma sb_range_cover_ordered_sound : forall w low high prefer z,
  sb_range_valid w low = true -> sb_range_valid w high = true ->
  snd low < fst high -> is_word w z ->
  (sb_range_gamma low z \/ sb_range_gamma high z) ->
  sb_ranges_gamma w (sb_range_cover_ordered w low high prefer) z.
Proof.
  intros w [la ua] [lb ub] prefer z Hlow Hhigh Hgap Hz Hrange.
  apply sb_range_valid_bounds in Hlow, Hhigh.
  cbn [fst snd] in Hlow, Hhigh, Hgap.
  unfold sb_range_cover_ordered. cbn [fst snd].
  destruct ((ub - la + 1 <? modulus w - lb + ua + 1) ||
    ((ub - la + 1 =? modulus w - lb + ua + 1) && prefer)).
  - rewrite <- (wrap_id w z Hz). apply sb_mod_ranges_sound.
    unfold sb_range_gamma in Hrange. cbn [fst snd] in Hrange. intuition lia.
  - destruct Hrange as [Hrange|Hrange]; unfold sb_range_gamma in Hrange;
      cbn [fst snd] in Hrange.
    + pose proof (sb_mod_ranges_sound w lb (ua + modulus w) (z + modulus w)
        ltac:(unfold is_word in Hz; lia)) as H.
      replace (z + modulus w) with (z + 1 * modulus w) in H by ring.
      rewrite wrap_add_modulus, (wrap_id w z Hz) in H. exact H.
    + rewrite <- (wrap_id w z Hz). apply sb_mod_ranges_sound. lia.
Qed.

(** Two endpoint covers reproduce the legacy circular tie-break without enumerating words. *)
Definition sb_range_cover (w : width) (a b : sb_range) : list sb_range :=
  if sb_range_valid w a && sb_range_valid w b then
    if snd a <? fst b then sb_range_cover_ordered w a b true else
    if snd b <? fst a then sb_range_cover_ordered w b a false else
    sb_mod_ranges w (Z.min (fst a) (fst b)) (Z.max (snd a) (snd b))
  else [(0, modulus w - 1)].

(** The selected endpoint cover contains either input range, including malformed raw endpoints. *)
Theorem sb_range_cover_sound : forall w a b z,
  is_word w z -> (sb_range_gamma a z \/ sb_range_gamma b z) ->
  sb_ranges_gamma w (sb_range_cover w a b) z.
Proof.
  intros w a b z Hz Hrange. unfold sb_range_cover.
  destruct (sb_range_valid w a && sb_range_valid w b) eqn:Hvalid.
  - apply andb_true_iff in Hvalid as [Ha Hb].
    destruct (snd a <? fst b) eqn:Hgap.
    + apply Z.ltb_lt in Hgap. now apply sb_range_cover_ordered_sound.
    + destruct (snd b <? fst a) eqn:Hgap'.
      * apply Z.ltb_lt in Hgap'. apply sb_range_cover_ordered_sound; try assumption. tauto.
      * rewrite <- (wrap_id w z Hz). apply sb_mod_ranges_sound.
        unfold sb_range_gamma in Hrange.
        pose proof (Z.le_min_l (fst a) (fst b)).
        pose proof (Z.le_min_r (fst a) (fst b)).
        pose proof (Z.le_max_l (snd a) (snd b)).
        pose proof (Z.le_max_r (snd a) (snd b)). intuition lia.
  - split; [exact Hz|]. exists (0, modulus w - 1). split; [now left|].
    unfold sb_range_gamma, is_word in *. cbn [fst snd]. lia.
Qed.
