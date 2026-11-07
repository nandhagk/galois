(** * Local signed-bound control and bitwise rules

    Constant-size endpoint rules cover bitwise operations, comparisons and changes of width.
    For example, conjunction of ranges ending at five and nine has upper bound five.
    Builds on: DomainsSignedBoundsArith and public Bits range and testbit laws. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsTnum DomainsTnumMul DomainsSignedBounds
  DomainsSignedBoundsRange DomainsSignedBoundsArith.
Import List.ListNotations.

Local Open Scope Z_scope.

Definition sb_range_not (w : width) (a : sb_range) : list sb_range :=
  sb_checked_ranges w (modulus w - 1 - snd a) (modulus w - 1 - fst a).

Lemma sb_complement_word : forall w x,
  is_word w x -> wnot w x = modulus w - 1 - x.
Proof.
  intros w x Hx. rewrite wnot_lnot, (wrap_id w x Hx), lnot_value, wrap_mod.
  symmetry. apply Z.mod_unique with (q := -1).
  - left. unfold is_word in Hx. lia.
  - ring.
Qed.

(** Complement reverses the inclusive unsigned endpoint order. *)
Theorem sb_range_not_sound : forall w a x,
  is_word w x -> sb_range_gamma a x ->
  sb_ranges_gamma w (sb_range_not w a) (wnot w x).
Proof.
  intros w [lo hi] x Hx Ha. apply sb_checked_ranges_sound; [apply wnot_is_word|].
  rewrite sb_complement_word by exact Hx.
  unfold sb_range_gamma in Ha. cbn [fst snd] in *. lia.
Qed.

Definition sb_range_and (w : width) (a b : sb_range) : list sb_range :=
  sb_checked_ranges w 0 (Z.min (snd a) (snd b)).

(** Conjunction is no greater than either unsigned input. *)
Theorem sb_range_and_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_and w a b) (wand w x y).
Proof.
  intros w [la ua] [lb ub] x y Hx Hy Ha Hb.
  apply sb_checked_ranges_sound; [apply wand_is_word|].
  pose proof (wand_is_word w x y) as Hword.
  assert (Hleft : wand w x y <= x).
  { apply (tnum_bitwise_le w); [apply wand_is_word|exact Hx|].
    intros i Hi Hbit. rewrite tnum_and_bit in Hbit by exact Hi.
    apply andb_true_iff in Hbit. tauto. }
  assert (Hright : wand w x y <= y).
  { rewrite wand_comm. apply (tnum_bitwise_le w); [apply wand_is_word|exact Hy|].
    intros i Hi Hbit. rewrite tnum_and_bit in Hbit by exact Hi.
    apply andb_true_iff in Hbit. tauto. }
  unfold sb_range_gamma, is_word in *. cbn [fst snd] in *. lia.
Qed.

Definition sb_range_mask (hi : Z) : Z :=
  if hi =? 0 then 0 else Z.ones (Z.log2 hi + 1).

Lemma sb_range_mask_covers : forall x y hi,
  0 <= x <= hi -> 0 <= y <= hi ->
  (0 <= Z.lor x y <= sb_range_mask hi) /\ (0 <= Z.lxor x y <= sb_range_mask hi).
Proof.
  intros x y hi Hx Hy. unfold sb_range_mask. destruct (hi =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. assert (x = 0 /\ y = 0) by lia.
    destruct H as [-> ->]. cbn. lia.
  - set (n := Z.log2 hi + 1).
    assert (Hn : 0 <= n) by (unfold n; pose proof (Z.log2_nonneg hi); lia).
    assert (Hlogx : Z.log2 x < n) by
      (unfold n; pose proof (Z.log2_le_mono x hi ltac:(lia)); lia).
    assert (Hlogy : Z.log2 y < n) by
      (unfold n; pose proof (Z.log2_le_mono y hi ltac:(lia)); lia).
    assert (Hor : Z.lor (Z.lor x y) (Z.ones n) = Z.ones n).
    { rewrite <- Z.lor_assoc, Z.lor_ones_low by lia. apply Z.lor_ones_low; lia. }
    assert (Hlor : 0 <= Z.lor x y) by (apply Z.lor_nonneg; lia).
    assert (Hmaskdiff : 0 <= Z.land (Z.ones n) (Z.lnot (Z.lor x y))).
    { apply Z.land_nonneg. left. rewrite Z.ones_equiv.
      pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). lia. }
    pose proof (Z.sub_lor_l_same_l (Z.ones n) (Z.lor x y)) as Hdiff.
    rewrite Hor in Hdiff.
    assert (Hand : 0 <= Z.land x y) by (apply Z.land_nonneg; lia).
    pose proof (Z.sub_lor_land x y) as Hxor.
    assert (Hxor_nonneg : 0 <= Z.lxor x y) by (apply Z.lxor_nonneg; lia). lia.
Qed.

Lemma sb_wor_word_value : forall w x y,
  is_word w x -> is_word w y -> wor w x y = Z.lor x y.
Proof.
  intros w x y Hx Hy. apply Z.bits_inj'. intros i Hi.
  rewrite testbit_wor, Z.lor_spec by assumption. reflexivity.
Qed.

Lemma sb_wxor_word_value : forall w x y,
  is_word w x -> is_word w y -> wxor w x y = Z.lxor x y.
Proof.
  intros w x y Hx Hy. apply Z.bits_inj'. intros i Hi.
  rewrite testbit_wxor, Z.lxor_spec by assumption. reflexivity.
Qed.

Definition sb_range_or_xor (w : width) (a b : sb_range) : list sb_range :=
  sb_checked_ranges w 0 (sb_range_mask (Z.max (snd a) (snd b))).

(** Disjunction and exclusive-or fit under the next all-ones upper mask. *)
Theorem sb_range_or_xor_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_or_xor w a b) (wor w x y) /\
  sb_ranges_gamma w (sb_range_or_xor w a b) (wxor w x y).
Proof.
  intros w [la ua] [lb ub] x y Hx Hy Ha Hb.
  unfold sb_range_gamma in Ha, Hb. cbn [fst snd] in Ha, Hb.
  pose proof (sb_range_mask_covers x y (Z.max ua ub)
    ltac:(unfold is_word in Hx; lia) ltac:(unfold is_word in Hy; lia)) as [Hor Hxor].
  split; apply sb_checked_ranges_sound; try apply wor_is_word; try apply wxor_is_word.
  - rewrite sb_wor_word_value by assumption. exact Hor.
  - rewrite sb_wxor_word_value by assumption. exact Hxor.
Qed.

Definition sb_range_count (w : width) : list sb_range := [(0, Zpos w)].

(** The three count primitives share the legacy inclusive range zero through width. *)
Theorem sb_range_count_sound : forall o w f x,
  (o = bvclz \/ o = bvctz \/ o = bvpopcnt) -> word_fun1 o = Some f ->
  sb_ranges_gamma w (sb_range_count w) (f w x).
Proof.
  intros o w f x Ho Hf.
  pose proof (word_fun1_is_word o f w x Hf) as Hword.
  destruct Ho as [Ho|[Ho|Ho]]; subst o; injection Hf as <-.
  all: split; [exact Hword|].
  all: exists (0, Zpos w); split; [now left|].
  all: first [apply wclz_range|apply tnum_ctz_range|apply wpopcnt_range].
Qed.

Definition sb_order_range (strict : bool) (a b : sb_range) : sb_range :=
  if (if strict then snd a <? fst b else snd a <=? fst b) then (1, 1) else
  if (if strict then snd b <=? fst a else snd b <? fst a) then (0, 0) else (0, 1).

(** Separated endpoint bounds decide either strict or non-strict integer comparison. *)
Theorem sb_order_range_sound : forall strict a b x y,
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_order_range strict a b)
    (if (if strict then x <? y else x <=? y) then 1 else 0).
Proof.
  intros strict [la ua] [lb ub] x y Ha Hb.
  unfold sb_order_range, sb_range_gamma in *. cbn [fst snd] in *.
  destruct strict.
  - destruct (ua <? lb) eqn:Htrue.
    + apply Z.ltb_lt in Htrue. rewrite (proj2 (Z.ltb_lt x y)) by lia. cbn. lia.
    + destruct (ub <=? la) eqn:Hfalse.
      * apply Z.leb_le in Hfalse. rewrite (proj2 (Z.ltb_ge x y)) by lia. cbn. lia.
      * destruct (x <? y); cbn; lia.
  - destruct (ua <=? lb) eqn:Htrue.
    + apply Z.leb_le in Htrue. rewrite (proj2 (Z.leb_le x y)) by lia. cbn. lia.
    + destruct (ub <? la) eqn:Hfalse.
      * apply Z.ltb_lt in Hfalse. rewrite (proj2 (Z.leb_gt x y)) by lia. cbn. lia.
      * destruct (x <=? y); cbn; lia.
Qed.

Definition sb_equal_range (a b : sb_range) : sb_range :=
  if (snd a <? fst b) || (snd b <? fst a) then (0, 0) else
  if (fst a =? snd a) && (fst b =? snd b) && (fst a =? fst b) then (1, 1) else (0, 1).

(** Disjoint ranges prove inequality and equal singleton ranges prove equality. *)
Theorem sb_equal_range_sound : forall a b x y,
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_equal_range a b) (if x =? y then 1 else 0).
Proof.
  intros [la ua] [lb ub] x y Ha Hb.
  unfold sb_equal_range, sb_range_gamma in *. cbn [fst snd] in *.
  destruct ((ua <? lb) || (ub <? la)) eqn:Hdisjoint.
  - assert (Hneq : x <> y).
    { apply orb_true_iff in Hdisjoint as [Hbad|Hbad]; apply Z.ltb_lt in Hbad; lia. }
    rewrite (proj2 (Z.eqb_neq x y) Hneq). cbn. lia.
  - destruct ((la =? ua) && (lb =? ub) && (la =? lb)) eqn:Hpoint.
    + rewrite !andb_true_iff in Hpoint. destruct Hpoint as [[Ha' Hb'] Hab].
      apply Z.eqb_eq in Ha', Hb', Hab. assert (Heq : x = y) by lia. subst y.
      rewrite Z.eqb_refl. cbn. lia.
    + destruct (x =? y); cbn; lia.
Qed.

Definition sb_range_concat (rw lower : width) (a b : sb_range) : list sb_range :=
  sb_mod_ranges rw (fst a * modulus lower + fst b) (snd a * modulus lower + snd b).

(** Concatenation combines the high and low operand endpoint ranges in the low operand radix. *)
Theorem sb_range_concat_sound : forall rw lower a b x y,
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma rw (sb_range_concat rw lower a b) (wrap rw (x * modulus lower + y)).
Proof.
  intros rw lower [la ua] [lb ub] x y Ha Hb.
  apply sb_mod_ranges_sound. unfold sb_range_gamma in *. cbn [fst snd] in *.
  pose proof (modulus_pos lower). nia.
Qed.
