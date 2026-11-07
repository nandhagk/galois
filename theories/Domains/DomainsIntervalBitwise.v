(** * Bitwise interval bounds

    Conjunction uses the smaller upper endpoint and disjunction uses an enclosing all-ones mask.
    For example, conjoining [240,255] and the singleton fifteen gives [0,15].
    Builds on: DomainsIntervalArith and public Bits testbit specifications. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit.
From Galois.Domains Require Import DomainsBound DomainsInterval DomainsIntervalArith.

Local Open Scope Z_scope.

(** Complementing a normalized word reverses its position in the unsigned range. *)
Theorem interval_complement_word w x :
  is_word w x -> wnot w x = modulus w - 1 - x.
Proof.
  intro Hword. rewrite wnot_lnot, (wrap_id w x Hword), lnot_value.
  rewrite <- (wrap_add_modulus w (- x - 1) 1).
  replace (- x - 1 + 1 * modulus w) with (modulus w - 1 - x) by ring.
  apply wrap_id. destruct Hword. split; lia.
Qed.

Definition interval_not (w : width) (a : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) => interval_checked w (modulus w - 1 - hi) (modulus w - 1 - lo)
  | None => interval_top w
  end.

(** Complement contains every complemented represented word. *)
Theorem interval_not_sound w a x :
  interval_pgamma w a x -> interval_pgamma w (interval_not w a) (wnot w x).
Proof.
  intro Ha. unfold interval_not.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite;
    [|apply interval_top_sound, wnot_is_word].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite).
  rewrite wnot_lnot, (wrap_id w x (proj1 Ha)), lnot_value.
  rewrite <- (wrap_add_modulus w (- x - 1) 1).
  replace (- x - 1 + 1 * modulus w) with (modulus w - 1 - x) by ring.
  apply interval_checked_wrap_sound. lia.
Qed.

Local Lemma wand_words w x y :
  is_word w x -> is_word w y -> wand w x y = Z.land x y.
Proof.
  intros Hx Hy. apply (word_ext w); [apply wand_is_word| |].
  - apply word_of_bits. intros i Hi. rewrite Z.land_spec.
    rewrite (word_bits_high w x i Hx Hi). reflexivity.
  - intros i Hi. rewrite testbit_wand by assumption. symmetry. apply Z.land_spec.
Qed.

Local Lemma wor_words w x y :
  is_word w x -> is_word w y -> wor w x y = Z.lor x y.
Proof.
  intros Hx Hy. apply (word_ext w); [apply wor_is_word| |].
  - apply word_of_bits. intros i Hi. rewrite Z.lor_spec.
    rewrite (word_bits_high w x i Hx Hi), (word_bits_high w y i Hy Hi). reflexivity.
  - intros i Hi. rewrite testbit_wor by assumption. symmetry. apply Z.lor_spec.
Qed.

Local Lemma wxor_words w x y :
  is_word w x -> is_word w y -> wxor w x y = Z.lxor x y.
Proof.
  intros Hx Hy. apply (word_ext w); [apply wxor_is_word| |].
  - apply word_of_bits. intros i Hi. rewrite Z.lxor_spec.
    rewrite (word_bits_high w x i Hx Hi), (word_bits_high w y i Hy Hi). reflexivity.
  - intros i Hi. rewrite testbit_wxor by assumption. symmetry. apply Z.lxor_spec.
Qed.

Definition interval_and (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (_, ha), Some (_, hb) => interval_checked w 0 (Z.min ha hb)
  | _, _ => interval_top w
  end.

(** Conjunction is bounded by either represented nonnegative operand. *)
Theorem interval_and_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_and w a b) (wand w x y).
Proof.
  intros Ha Hb. unfold interval_and.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound, wand_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa).
  pose proof (interval_finite_sound w b lb hb y Hb Hfb).
  destruct Ha as [Hwordx _], Hb as [Hwordy _].
  apply interval_checked_sound; [apply wand_is_word|].
  rewrite wand_words by assumption.
  pose proof (Z.sub_land_same_l x y) as Hx.
  pose proof (Z.sub_land_same_l y x) as Hy. rewrite Z.land_comm in Hy.
  assert (Hnonnegx : 0 <= Z.land x (Z.lnot y)).
  { apply Z.land_nonneg. left. exact (proj1 Hwordx). }
  assert (Hnonnegy : 0 <= Z.land y (Z.lnot x)).
  { apply Z.land_nonneg. left. exact (proj1 Hwordy). }
  assert (Hnonneg : 0 <= Z.land x y).
  { apply Z.land_nonneg. left. exact (proj1 Hwordx). }
  split; [exact Hnonneg|]. apply Z.min_glb; lia.
Qed.

Definition interval_mask (hi : Z) : Z :=
  if Z.eqb hi 0 then 0 else Z.ones (Z.log2 hi + 1).

Local Lemma interval_mask_covers x y hi :
  0 <= x <= hi -> 0 <= y <= hi ->
  0 <= Z.lor x y <= interval_mask hi /\ 0 <= Z.lxor x y <= interval_mask hi.
Proof.
  intros Hx Hy. unfold interval_mask. destruct (Z.eqb hi 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero.
    assert (Hxzero : x = 0) by lia. assert (Hyzero : y = 0) by lia.
    subst x y. cbn. lia.
  - set (n := Z.log2 hi + 1).
    assert (Hn : 0 <= n) by (unfold n; pose proof (Z.log2_nonneg hi); lia).
    assert (Hmask : 0 <= Z.ones n).
    { rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). lia. }
    assert (Hlogx : Z.log2 x < n) by
      (unfold n; pose proof (Z.log2_le_mono x hi ltac:(lia)); lia).
    assert (Hlogy : Z.log2 y < n) by
      (unfold n; pose proof (Z.log2_le_mono y hi ltac:(lia)); lia).
    assert (Hor : Z.lor (Z.lor x y) (Z.ones n) = Z.ones n).
    { rewrite <- Z.lor_assoc, Z.lor_ones_low by lia. apply Z.lor_ones_low; lia. }
    assert (Hlor : 0 <= Z.lor x y) by (apply Z.lor_nonneg; lia).
    assert (Hmaskdiff : 0 <= Z.land (Z.ones n) (Z.lnot (Z.lor x y))).
    { apply Z.land_nonneg. now left. }
    pose proof (Z.sub_lor_l_same_l (Z.ones n) (Z.lor x y)) as Hdiff.
    rewrite Hor in Hdiff.
    assert (Hand : 0 <= Z.land x y) by (apply Z.land_nonneg; lia).
    pose proof (Z.sub_lor_land x y) as Hxor.
    assert (Hxor_nonneg : 0 <= Z.lxor x y) by (apply Z.lxor_nonneg; lia).
    lia.
Qed.

Definition interval_or_xor (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (_, ha), Some (_, hb) => interval_checked w 0 (interval_mask (Z.max ha hb))
  | _, _ => interval_top w
  end.

(** The enclosing mask contains both disjunction and exclusive disjunction results. *)
Theorem interval_or_xor_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_or_xor w a b) (wor w x y) /\
  interval_pgamma w (interval_or_xor w a b) (wxor w x y).
Proof.
  intros Ha Hb. unfold interval_or_xor.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (split; apply interval_top_sound; first [apply wor_is_word|apply wxor_is_word]).
  pose proof (interval_finite_sound w a la ha x Ha Hfa).
  pose proof (interval_finite_sound w b lb hb y Hb Hfb).
  destruct Ha as [Hwordx _], Hb as [Hwordy _].
  pose proof (proj1 Hwordx). pose proof (proj1 Hwordy).
  pose proof (interval_mask_covers x y (Z.max ha hb)
    ltac:(pose proof (Z.le_max_l ha hb); lia)
    ltac:(pose proof (Z.le_max_r ha hb); lia)) as [Hor Hxor].
  split; apply interval_checked_sound; try apply wor_is_word; try apply wxor_is_word.
  - now rewrite wor_words by assumption.
  - now rewrite wxor_words by assumption.
Qed.
