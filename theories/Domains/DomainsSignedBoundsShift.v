(** * Local signed-bound shift ranges

    Shift rules guard powers by the width and distinguish arithmetic sign fill.
    For example, an oversized arithmetic shift of a negative half returns the all-ones word.
    Builds on: DomainsSignedBoundsControl and public Bits shift-bit equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsTnum DomainsSignedBounds DomainsSignedBoundsRange
  DomainsSignedBoundsArith DomainsSignedBoundsControl.
Import List.ListNotations.

Local Open Scope Z_scope.

Lemma sb_div_power_bounds : forall la ua lb ub x y,
  0 <= la -> la <= x <= ua -> 0 <= lb -> lb <= y <= ub ->
  la / 2 ^ ub <= x / 2 ^ y <= ua / 2 ^ lb.
Proof.
  intros la ua lb ub x y Hla Hx Hlb Hy.
  assert (Hpowlo : 2 ^ lb <= 2 ^ y) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowhi : 2 ^ y <= 2 ^ ub) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowpos : 0 < 2 ^ lb) by (apply Z.pow_pos_nonneg; lia).
  split.
  - eapply (Z.le_trans _ (x / 2 ^ ub));
      [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
  - eapply (Z.le_trans _ (x / 2 ^ lb));
      [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
Qed.

Definition sb_range_shl (w : width) (a b : sb_range) : list sb_range :=
  if (0 <=? fst a) && (0 <=? fst b) && (snd b <? Zpos w)
  then sb_checked_ranges w (fst a * 2 ^ fst b) (snd a * 2 ^ snd b)
  else [(0, modulus w - 1)].

(** A bounded left shift uses endpoint multiplication and otherwise keeps the legacy word top. *)
Theorem sb_range_shl_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_shl w a b) (wshl w x y).
Proof.
  intros w [la ua] [lb ub] x y Hx Hy Ha Hb.
  unfold sb_range_shl, sb_range_gamma in *. cbn [fst snd] in *.
  destruct ((0 <=? la) && (0 <=? lb) && (ub <? Zpos w)) eqn:Hrange.
  - rewrite !andb_true_iff in Hrange. destruct Hrange as [[Hla Hlb] Hub].
    apply Z.leb_le in Hla, Hlb. apply Z.ltb_lt in Hub.
    rewrite wshl_value, (wrap_id w x Hx), (wrap_id w y Hy),
      (proj2 (Z.leb_gt (Zpos w) y)) by lia.
    apply sb_checked_ranges_wrapped_sound.
    pose proof (Z.pow_le_mono_r 2 lb y ltac:(lia) ltac:(lia)).
    pose proof (Z.pow_le_mono_r 2 y ub ltac:(lia) ltac:(lia)).
    pose proof (Z.pow_pos_nonneg 2 lb ltac:(lia) ltac:(lia)). nia.
  - split; [apply wshl_is_word|]. exists (0, modulus w - 1). split; [now left|].
    pose proof (wshl_is_word w x y). unfold sb_range_gamma, is_word in *.
    cbn [fst snd]. lia.
Qed.

Definition sb_lshr_bound (w : width) (a b : sb_range) : sb_range :=
  if (0 <=? fst a) && (0 <=? fst b) && (snd b <? Zpos w)
  then sb_checked_range w (fst a / 2 ^ snd b) (snd a / 2 ^ fst b)
  else (0, modulus w - 1).

Lemma sb_lshr_bound_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_lshr_bound w a b) (wlshr w x y).
Proof.
  intros w [la ua] [lb ub] x y Hx Hy Ha Hb.
  unfold sb_lshr_bound, sb_range_gamma in *. cbn [fst snd] in *.
  destruct ((0 <=? la) && (0 <=? lb) && (ub <? Zpos w)) eqn:Hrange.
  - rewrite !andb_true_iff in Hrange. destruct Hrange as [[Hla Hlb] Hub].
    apply Z.leb_le in Hla, Hlb. apply Z.ltb_lt in Hub.
    apply sb_checked_range_sound; [apply wlshr_is_word|].
    rewrite wlshr_value, (wrap_id w x Hx), (wrap_id w y Hy),
      (proj2 (Z.leb_gt (Zpos w) y)) by lia.
    now apply sb_div_power_bounds.
  - pose proof (wlshr_is_word w x y). unfold is_word in *. cbn [fst snd]. lia.
Qed.

Definition sb_range_lshr (w : width) (a b : sb_range) : list sb_range :=
  [sb_lshr_bound w a b].

(** A bounded logical right shift uses monotone quotient endpoints. *)
Theorem sb_range_lshr_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_lshr w a b) (wlshr w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. split; [apply wlshr_is_word|].
  exists (sb_lshr_bound w a b). split; [now left|].
  now apply sb_lshr_bound_sound.
Qed.

Lemma sb_ashr_nonnegative : forall w x y,
  is_word w x -> is_word w y -> msb w x = false -> washr w x y = wlshr w x y.
Proof.
  intros w x y Hx Hy Hsign. apply (word_ext w);
    [apply washr_is_word|apply wlshr_is_word|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite testbit_washr, testbit_wlshr by (try assumption; lia).
    rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia.
    cbn [andb]. destruct (Z_lt_ge_dec (i + y) (Zpos w)) as [Hsource|Hfill].
    + rewrite Z.min_l by lia. reflexivity.
    + rewrite Z.min_r by lia. rewrite <- msb_testbit, Hsign.
      symmetry. apply (word_bits_high w x); [exact Hx|lia].
  - rewrite !(word_bits_high w) by
      (try apply washr_is_word; try apply wlshr_is_word; lia). reflexivity.
Qed.

Lemma sb_ashr_negative : forall w x y,
  is_word w x -> is_word w y -> msb w x = true ->
  washr w x y = wnot w (wlshr w (wnot w x) y).
Proof.
  intros w x y Hx Hy Hsign. apply (word_ext w);
    [apply washr_is_word|apply wnot_is_word|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite tnum_not_bit, testbit_washr, testbit_wlshr by
      (try assumption; try apply wnot_is_word; lia).
    rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia.
    cbn [andb]. destruct (Z_lt_ge_dec (i + y) (Zpos w)) as [Hsource|Hfill].
    + rewrite Z.min_l, tnum_not_bit by (unfold is_word in Hy; lia).
      now rewrite negb_involutive.
    + rewrite Z.min_r by lia. rewrite <- msb_testbit, Hsign.
      rewrite (word_bits_high w (wnot w x) (i + y) (wnot_is_word w x) ltac:(lia)).
      reflexivity.
  - rewrite !(word_bits_high w) by
      (try apply washr_is_word; try apply wnot_is_word; lia). reflexivity.
Qed.

Definition sb_not_bound (w : width) (a : sb_range) : sb_range :=
  sb_checked_range w (modulus w - 1 - snd a) (modulus w - 1 - fst a).

Lemma sb_not_bound_sound : forall w a x,
  is_word w x -> sb_range_gamma a x -> sb_range_gamma (sb_not_bound w a) (wnot w x).
Proof.
  intros w a x Hx Ha. pose proof (sb_range_not_sound w a x Hx Ha) as Hnot.
  unfold sb_range_not in Hnot. rewrite sb_checked_ranges_pair in Hnot.
  now apply sb_single_range_gamma in Hnot.
Qed.

Definition sb_ashr_small_bound (w : width) (a b : sb_range) : sb_range :=
  match sb_range_sign w a with
  | Some false => sb_lshr_bound w a b
  | Some true => sb_not_bound w (sb_lshr_bound w (sb_not_bound w a) b)
  | None => (0, modulus w - 1)
  end.

Lemma sb_ashr_small_bound_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_ashr_small_bound w a b) (washr w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold sb_ashr_small_bound.
  destruct (sb_range_sign w a) as [s|] eqn:Hsign.
  - pose proof (sb_range_sign_sound w a x s Hx Ha Hsign) as Hs. destruct s.
    + rewrite sb_ashr_negative by assumption.
      apply sb_not_bound_sound; [apply wlshr_is_word|].
      apply sb_lshr_bound_sound; try assumption; [apply wnot_is_word|].
      now apply sb_not_bound_sound.
    + rewrite sb_ashr_nonnegative by assumption. now apply sb_lshr_bound_sound.
  - pose proof (washr_is_word w x y). unfold sb_range_gamma, is_word in *.
    cbn [fst snd]. lia.
Qed.

Definition sb_range_ashr (w : width) (a b : sb_range) : list sb_range :=
  match sb_range_sign w a with
  | Some sign =>
    let saturated := if sign then modulus w - 1 else 0 in
    if snd b <? Zpos w then [sb_ashr_small_bound w a b] else
    if Zpos w <=? fst b then [(saturated, saturated)] else
    let small := sb_ashr_small_bound w a (fst b, Zpos w - 1) in
    [(Z.min (fst small) saturated, Z.max (snd small) saturated)]
  | None => [sb_ashr_small_bound w a b]
  end.

(** Arithmetic shift adds the saturated sign-fill result when the count range reaches the width. *)
Theorem sb_range_ashr_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_ashr w a b) (washr w x y).
Proof.
  intros w a [lo hi] x y Hx Hy Ha Hb.
  assert (Hbound : lo <= y <= hi) by exact Hb.
  split; [apply washr_is_word|]. unfold sb_range_ashr.
  destruct (sb_range_sign w a) as [sign|] eqn:Hsign.
  2: { exists (sb_ashr_small_bound w a (lo, hi)). split; [now left|].
    now apply sb_ashr_small_bound_sound. }
  pose proof (sb_range_sign_sound w a x sign Hx Ha Hsign) as Hs.
  assert (Hsat : Zpos w <= y -> washr w x y = if sign then modulus w - 1 else 0).
  { intro Hlarge. rewrite washr_value, (wrap_id w y Hy),
      (proj2 (Z.leb_le (Zpos w) y) Hlarge), Hs. reflexivity. }
  cbn [fst snd].
  destruct (hi <? Zpos w) eqn:Hsmall.
  - exists (sb_ashr_small_bound w a (lo, hi)). split; [now left|].
    now apply sb_ashr_small_bound_sound.
  - destruct (Zpos w <=? lo) eqn:Hlarge.
    + apply Z.leb_le in Hlarge. rewrite Hsat by lia.
      exists ((if sign then modulus w - 1 else 0), (if sign then modulus w - 1 else 0)).
      split; [now left|]. unfold sb_range_gamma. cbn [fst snd]. lia.
    + set (small := sb_ashr_small_bound w a (lo, Zpos w - 1)).
      exists (Z.min (fst small) (if sign then modulus w - 1 else 0),
        Z.max (snd small) (if sign then modulus w - 1 else 0)).
      split; [now left|]. unfold sb_range_gamma. cbn [fst snd].
      destruct (Z_le_gt_dec (Zpos w) y) as [Hylarge|Hysmall].
      * rewrite Hsat by exact Hylarge.
        pose proof (Z.le_min_r (fst small) (if sign then modulus w - 1 else 0)).
        pose proof (Z.le_max_r (snd small) (if sign then modulus w - 1 else 0)). lia.
      * assert (Hinside : sb_range_gamma small (washr w x y)).
        { apply sb_ashr_small_bound_sound; try assumption.
          change (lo <= y <= Zpos w - 1). lia. }
        unfold sb_range_gamma in Hinside.
        pose proof (Z.le_min_l (fst small) (if sign then modulus w - 1 else 0)).
        pose proof (Z.le_max_l (snd small) (if sign then modulus w - 1 else 0)). lia.
Qed.
