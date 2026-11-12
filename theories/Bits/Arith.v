(** * Signed and unsigned word arithmetic

    Division, counts and rotations obey their integer and bit-level specifications.
    For example, signed division truncates toward zero and signed modulus follows the divisor.
    Builds on: Word, Fun and Testbit. *)

From Stdlib Require Import ZArith List Bool Lia Ring.
From Argent Require Import Time.
From Galois.Bits Require Import Word Fun Testbit.
Open Scope Z_scope.

(** * Signed interpretations and comparison *)

(** Signed values stay in the symmetric two's complement interval. *)
Theorem signed_range : forall w x, - half w <= signed w x < half w.
Proof.
  intros w x. pose proof (wrap_is_word w x) as Hrange.
  pose proof (modulus_half w). unfold signed, is_word in *.
  destruct (wrap w x <? half w) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - apply Z.ltb_ge in Hlt. lia.
Qed.

Local Lemma lxor_pow2_low : forall a k, 0 <= k -> 0 <= a < 2 ^ k ->
  Z.lxor a (2 ^ k) = a + 2 ^ k.
Proof.
  intros a k Hk Ha. symmetry. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec k i) as [<-|Hne].
  - assert (Hbit : Z.testbit a k = false).
    { rewrite <- (Z.mod_small a (2 ^ k) Ha) at 1.
      apply Z.mod_pow2_bits_high. lia. }
    now rewrite Hbit.
  - rewrite Z.pow2_bits_false by exact Hne. apply Bool.andb_false_r.
Qed.

(** Flipping the sign bit adds half the modulus to the signed value. *)
Theorem wxor_half_value : forall w x, wxor w x (half w) = signed w x + half w.
Proof.
  intros w x. pose proof (half_pos w) as Hhalf.
  pose proof (modulus_half w) as Hmodulus.
  pose proof (wrap_is_word w x) as Hrange. unfold is_word in Hrange.
  unfold wxor. rewrite (wrap_id w (half w)) by (unfold is_word; lia).
  unfold signed. destruct (wrap w x <? half w) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. apply lxor_pow2_low; [lia|exact (conj (proj1 Hrange) Hlt)].
  - apply Z.ltb_ge in Hlt.
    assert (Hlow : 0 <= wrap w x - half w < half w) by lia.
    assert (Hsplit : wrap w x = Z.lxor (wrap w x - half w) (half w)).
    { pose proof (lxor_pow2_low (wrap w x - half w) (Zpos w - 1) ltac:(lia) Hlow)
        as Hxor. fold (half w) in Hxor. rewrite Hxor. lia. }
    rewrite Hsplit at 1. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. lia.
Qed.

(** Flipping the sign bit biases signed order into unsigned order. *)
Theorem wslt_bias : forall w x y,
  wslt w x y = wult w (wxor w x (half w)) (wxor w y (half w)).
Proof.
  intros w x y. unfold wslt, wult.
  rewrite !wrap_id by apply wxor_is_word. rewrite !wxor_half_value.
  destruct (signed w x <? signed w y) eqn:Hsigned;
    destruct (signed w x + half w <? signed w y + half w) eqn:Hbiased;
    try reflexivity;
    apply Z.ltb_lt in Hsigned || apply Z.ltb_ge in Hsigned;
    apply Z.ltb_lt in Hbiased || apply Z.ltb_ge in Hbiased; lia.
Qed.

(** Wrapping a signed view recovers the original word. *)
Theorem wrap_signed : forall w x, wrap w (signed w x) = wrap w x.
Proof.
  intros w x. unfold signed. destruct (wrap w x <? half w).
  - apply wrap_wrap.
  - replace (wrap w x - modulus w) with (wrap w x + (-1) * modulus w) by ring.
    now rewrite wrap_add_modulus, wrap_wrap.
Qed.

(** Normalization does not change the signed interpretation. *)
Theorem signed_wrap : forall w x, signed w (wrap w x) = signed w x.
Proof.
  intros w x. unfold signed. now rewrite wrap_wrap.
Qed.

(** Every integer in the signed interval is its own signed interpretation. *)
Theorem signed_id : forall w z, - half w <= z < half w -> signed w z = z.
Proof.
  intros w z Hz. pose proof (half_pos w). pose proof (modulus_half w).
  destruct (Z_le_gt_dec 0 z) as [Hnonneg|Hneg].
  - unfold signed. rewrite wrap_id by (unfold is_word; lia).
    now rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hz)).
  - assert (Hwrap : wrap w z = z + modulus w).
    { unfold wrap. symmetry. apply Z.mod_unique with (q := -1).
      - left. lia.
      - ring. }
    unfold signed. rewrite Hwrap.
    rewrite (proj2 (Z.ltb_ge (z + modulus w) (half w)) ltac:(lia)). lia.
Qed.

(** Equal signed views identify the normalized words. *)
Theorem signed_inj : forall w x y,
  signed w x = signed w y -> wrap w x = wrap w y.
Proof.
  intros w x y Heq. rewrite <- (wrap_signed w x), <- (wrap_signed w y).
  now rewrite Heq.
Qed.

(** The sign bit is set exactly for negative signed values. *)
Theorem signed_neg_iff_msb : forall w x, signed w x < 0 <-> msb w x = true.
Proof.
  intros w x. rewrite msb_half. unfold signed.
  pose proof (wrap_is_word w x) as Hrange. unfold is_word in Hrange.
  destruct (wrap w x <? half w) eqn:Hlt.
  - change (wrap w x < 0 <-> false = true). split; [lia|discriminate].
  - change (wrap w x - modulus w < 0 <-> true = true). split; [reflexivity|lia].
Qed.

(** Word addition may use the signed interpretations of both operands. *)
Theorem wadd_signed : forall w x y,
  wadd w x y = wrap w (signed w x + signed w y).
Proof.
  intros w x y. unfold wadd. rewrite (wrap_add w x y),
    (wrap_add w (signed w x) (signed w y)), !wrap_signed. reflexivity.
Qed.

(** Word subtraction may use the signed interpretations of both operands. *)
Theorem wsub_signed : forall w x y,
  wsub w x y = wrap w (signed w x - signed w y).
Proof.
  intros w x y. unfold wsub. rewrite (wrap_sub w x y),
    (wrap_sub w (signed w x) (signed w y)), !wrap_signed. reflexivity.
Qed.

(** Equal sign bits make signed and unsigned strict comparisons agree. *)
Theorem wslt_wult : forall w x y,
  msb w x = msb w y -> wslt w x y = wult w x y.
Proof.
  intros w x y Hsign. rewrite !msb_half in Hsign. unfold wslt, wult, signed.
  destruct (wrap w x <? half w), (wrap w y <? half w); cbn in Hsign;
    try discriminate; [reflexivity|].
  destruct (wrap w x - modulus w <? wrap w y - modulus w) eqn:Hsigned;
    destruct (wrap w x <? wrap w y) eqn:Hunsigned; try reflexivity;
    apply Z.ltb_lt in Hsigned || apply Z.ltb_ge in Hsigned;
    apply Z.ltb_lt in Hunsigned || apply Z.ltb_ge in Hunsigned; lia.
Qed.

(** A clear sign bit makes the signed view equal the unsigned value. *)
Theorem signed_nonnegative : forall w x, msb w x = false -> signed w x = wrap w x.
Proof.
  intros w x Hsign. rewrite msb_half in Hsign. unfold signed.
  destruct (wrap w x <? half w); [reflexivity|discriminate].
Qed.

(** A set sign bit makes the signed view the negative of the modular negation. *)
Theorem signed_negative : forall w x, msb w x = true -> signed w x = - wneg w x.
Proof.
  intros w x Hsign. pose proof (signed_range w x) as Hrange.
  pose proof (proj2 (signed_neg_iff_msb w x) Hsign) as Hnegative.
  pose proof (modulus_half w). pose proof (half_pos w).
  assert (Hwrap : wrap w (- x) = wrap w (- signed w x)).
  { rewrite <- (wrap_opp w x), <- (wrap_opp w (signed w x)), wrap_signed.
    reflexivity. }
  unfold wneg. rewrite Hwrap, wrap_id by (unfold is_word; lia). lia.
Qed.

(** Negating a word with a set sign bit gives a positive unsigned value. *)
Theorem wneg_positive : forall w x, msb w x = true -> 0 < wneg w x.
Proof.
  intros w x Hsign. pose proof (proj2 (signed_neg_iff_msb w x) Hsign) as Hnegative.
  rewrite (signed_negative w x Hsign) in Hnegative. lia.
Qed.

(** * Signed division and remainders *)

(** Unsigned division agrees with wrapped truncating division for a nonzero divisor. *)
Theorem wudiv_quot : forall w a b, wrap w b <> 0 ->
  wudiv w a b = wrap w (Z.quot (wrap w a) (wrap w b)).
Proof.
  intros w a b Hnz. pose proof (wrap_is_word w a) as Ha.
  pose proof (wrap_is_word w b) as Hb.
  assert (Hpos : 0 < wrap w b) by (unfold is_word in Hb; lia).
  unfold wudiv. rewrite (proj2 (Z.eqb_neq _ _) Hnz).
  rewrite Z.quot_div_nonneg by (try exact Hpos; exact (proj1 Ha)).
  symmetry. apply wrap_id. now apply word_div_is_word.
Qed.

Local Lemma rem_zero_r : forall a, Z.rem a 0 = a.
Proof.
  intros [|a|a]; reflexivity.
Qed.

(** Unsigned remainder agrees with wrapped truncating remainder. *)
Theorem wurem_rem : forall w a b,
  wurem w a b = wrap w (Z.rem (wrap w a) (wrap w b)).
Proof.
  intros w a b. unfold wurem. destruct (wrap w b =? 0) eqn:Hb.
  - apply Z.eqb_eq in Hb. rewrite Hb, rem_zero_r. symmetry. apply wrap_wrap.
  - apply Z.eqb_neq in Hb. pose proof (wrap_is_word w b) as Hrange.
    assert (Hpos : 0 < wrap w b) by (unfold is_word in Hrange; lia).
    rewrite Z.rem_mod_nonneg by (try exact Hpos; exact (proj1 (wrap_is_word w a))).
    symmetry. apply wrap_id. pose proof (Z.mod_pos_bound (wrap w a) (wrap w b) Hpos).
    unfold is_word in *. lia.
Qed.

(** Signed division agrees with truncating integer division for nonzero divisors. *)
Theorem wsdiv_signed : forall w x y, signed w y <> 0 ->
  wsdiv w x y = wrap w (Z.quot (signed w x) (signed w y)).
Proof.
  intros w x y Hnz. unfold wsdiv.
  destruct (msb w x) eqn:Hx; destruct (msb w y) eqn:Hy.
  - rewrite (signed_negative w x Hx), (signed_negative w y Hy) in *.
    rewrite Z.quot_opp_opp by lia.
    rewrite wudiv_quot by (rewrite wrap_id by apply wrap_is_word; lia).
    now rewrite (wrap_id w (wneg w x)), (wrap_id w (wneg w y)) by apply wrap_is_word.
  - rewrite (signed_negative w x Hx), (signed_nonnegative w y Hy) in *.
    rewrite Z.quot_opp_l by exact Hnz. unfold wneg at 1.
    rewrite wudiv_quot by exact Hnz. rewrite wrap_opp.
    now rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
  - rewrite (signed_nonnegative w x Hx), (signed_negative w y Hy) in *.
    rewrite Z.quot_opp_r by lia. unfold wneg at 1.
    rewrite wudiv_quot by (rewrite wrap_id by apply wrap_is_word; lia).
    rewrite wrap_opp. now rewrite (wrap_id w (wneg w y)) by apply wrap_is_word.
  - rewrite (signed_nonnegative w x Hx), (signed_nonnegative w y Hy) in *.
    now apply wudiv_quot.
Qed.

(** Signed remainder agrees with truncating integer remainder, including zero divisors. *)
Theorem wsrem_signed : forall w x y,
  wsrem w x y = wrap w (Z.rem (signed w x) (signed w y)).
Proof.
  intros w x y. unfold wsrem.
  destruct (msb w x) eqn:Hx; destruct (msb w y) eqn:Hy;
    rewrite ?(signed_negative w x Hx), ?(signed_negative w y Hy),
      ?(signed_nonnegative w x Hx), ?(signed_nonnegative w y Hy).
  - destruct (Z.eq_dec (wneg w y) 0) as [Hz|Hnz].
    + rewrite Hz, Z.opp_0, rem_zero_r, wurem_rem, !wrap_0, rem_zero_r.
      unfold wneg at 1. rewrite wrap_opp.
      now rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
    + rewrite Z.rem_opp_opp by exact Hnz. unfold wneg at 1.
      rewrite wurem_rem, wrap_opp.
      now rewrite (wrap_id w (wneg w x)), (wrap_id w (wneg w y)) by apply wrap_is_word.
  - destruct (Z.eq_dec (wrap w y) 0) as [Hz|Hnz].
    + rewrite Hz, rem_zero_r, wurem_rem, Hz, rem_zero_r.
      unfold wneg at 1. rewrite wrap_opp.
      now rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
    + rewrite Z.rem_opp_l by exact Hnz. unfold wneg at 1.
      rewrite wurem_rem, wrap_opp.
      now rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
  - destruct (Z.eq_dec (wneg w y) 0) as [Hz|Hnz].
    + rewrite Hz, Z.opp_0, rem_zero_r, wurem_rem, wrap_0, rem_zero_r. reflexivity.
    + rewrite Z.rem_opp_r by exact Hnz. rewrite wurem_rem.
      now rewrite (wrap_id w (wneg w y)) by apply wrap_is_word.
  - apply wurem_rem.
Qed.

(** Unsigned remainder includes the integer modulo convention at zero. *)
Theorem wurem_mod : forall w a b, wurem w a b = wrap w a mod wrap w b.
Proof.
  intros w a b. unfold wurem. destruct (wrap w b =? 0) eqn:Hb; [|reflexivity].
  apply Z.eqb_eq in Hb. now rewrite Hb, Z.mod_0_r.
Qed.

(** Wrapping the right summand does not change the wrapped sum. *)
Theorem wrap_add_right : forall w a b, wrap w (a + b) = wrap w (a + wrap w b).
Proof.
  intros w a b. unfold wrap. symmetry. apply Z.add_mod_idemp_r. apply modulus_nonzero.
Qed.

(** Wrapping the left summand does not change the wrapped sum. *)
Theorem wrap_add_left : forall w a b, wrap w (a + b) = wrap w (wrap w a + b).
Proof.
  intros w a b. unfold wrap. symmetry. apply Z.add_mod_idemp_l. apply modulus_nonzero.
Qed.

(** Zero has signed value zero at every width. *)
Theorem signed_zero : forall w, signed w 0 = 0.
Proof.
  intros w. apply signed_id. pose proof (half_pos w). lia.
Qed.

(** Zero has a clear sign bit at every width. *)
Theorem msb_zero : forall w, msb w 0 = false.
Proof.
  intros w. unfold msb. rewrite wrap_0. apply Z.bits_0.
Qed.

(** Signed division by zero follows the SMT-LIB sign-dependent total convention. *)
Theorem wsdiv_zero : forall w x,
  wsdiv w x 0 = if msb w x then 1 else modulus w - 1.
Proof.
  intros w x. unfold wsdiv. rewrite msb_zero. destruct (msb w x).
  - unfold wneg at 1. unfold wudiv. rewrite wrap_0.
    change (wrap w (- (modulus w - 1)) = 1).
    replace (- (modulus w - 1)) with (1 + (-1) * modulus w) by ring.
    now rewrite wrap_add_modulus, wrap_1.
  - unfold wudiv. now rewrite wrap_0.
Qed.

(** Signed quotient and remainder reconstruct the dividend modulo the width. *)
Theorem wsdiv_wsrem_euclid : forall w x y,
  wadd w (wmul w y (wsdiv w x y)) (wsrem w x y) = wrap w x.
Proof.
  intros w x y. destruct (Z.eq_dec (signed w y) 0) as [Hz|Hnz].
  - assert (Hy : wrap w y = 0).
    { rewrite <- (wrap_signed w y), Hz. apply wrap_0. }
    rewrite wsrem_signed, Hz, rem_zero_r, wrap_signed.
    unfold wadd, wmul. rewrite (wrap_mul w y _), Hy, Z.mul_0_l, wrap_0, Z.add_0_l.
    apply wrap_wrap.
  - rewrite wsdiv_signed by exact Hnz. rewrite wsrem_signed.
    unfold wadd, wmul. rewrite (wrap_mul w y _), wrap_wrap.
    rewrite <- (wrap_signed w y), <- (wrap_mul w (signed w y) _).
    rewrite <- wrap_add.
    rewrite <- Z.quot_rem by exact Hnz. apply wrap_signed.
Qed.

(** Adding a modular negation is wrapped unsigned subtraction. *)
Theorem wadd_wrapped_neg : forall w a y,
  wadd w (wneg w a) y = wrap w (wrap w y - a).
Proof.
  intros w a y. unfold wadd, wneg.
  rewrite <- wrap_add_left, wrap_add_right. f_equal. ring.
Qed.

(** Addition may interpret its right operand as signed. *)
Theorem wadd_signed_right : forall w a y,
  wadd w a y = wrap w (a + signed w y).
Proof.
  intros w a y. unfold wadd. rewrite (wrap_add_right w a y),
    (wrap_add_right w a (signed w y)), wrap_signed. reflexivity.
Qed.

(** Signed modulus agrees with flooring integer modulo, including zero divisors. *)
Theorem wsmod_signed : forall w x y,
  wsmod w x y = wrap w (Z.modulo (signed w x) (signed w y)).
Proof.
  intros w x y. unfold wsmod.
  destruct (msb w x) eqn:Hx; destruct (msb w y) eqn:Hy.
  - rewrite (signed_negative w x Hx), (signed_negative w y Hy).
    assert (Hnz : wneg w y <> 0) by (pose proof (wneg_positive w y Hy); lia).
    rewrite Z.mod_opp_opp by exact Hnz.
    rewrite (wurem_mod w (wneg w x) (wneg w y)).
    rewrite (wrap_id w (wneg w x)), (wrap_id w (wneg w y)) by apply wrap_is_word.
    destruct (wneg w x mod wneg w y =? 0) eqn:Hu.
    + apply Z.eqb_eq in Hu. rewrite Hu, Z.opp_0, wrap_0. reflexivity.
    + reflexivity.
  - rewrite (signed_negative w x Hx), (signed_nonnegative w y Hy).
    rewrite (wurem_mod w (wneg w x) (wrap w y)), wrap_wrap.
    rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
    destruct (Z.eq_dec (wrap w y) 0) as [Hz|Hnz].
    + rewrite Hz, !Z.mod_0_r.
      pose proof (wneg_positive w x Hx) as Hpositive.
      rewrite (proj2 (Z.eqb_neq (wneg w x) 0) ltac:(lia)), wadd_wrapped_neg, Hz.
      f_equal.
    + destruct (wneg w x mod wrap w y =? 0) eqn:Hu.
      * apply Z.eqb_eq in Hu. rewrite Z.mod_opp_l_z by assumption.
        rewrite Hu, wrap_0. reflexivity.
      * apply Z.eqb_neq in Hu. rewrite Z.mod_opp_l_nz by assumption.
        apply wadd_wrapped_neg.
  - rewrite (signed_nonnegative w x Hx), (signed_negative w y Hy).
    assert (Hnz : wneg w y <> 0) by (pose proof (wneg_positive w y Hy); lia).
    rewrite (wurem_mod w (wrap w x) (wneg w y)), wrap_wrap.
    rewrite (wrap_id w (wneg w y)) by apply wrap_is_word.
    destruct (wrap w x mod wneg w y =? 0) eqn:Hu.
    + apply Z.eqb_eq in Hu. rewrite Z.mod_opp_r_z by assumption.
      rewrite Hu, wrap_0. reflexivity.
    + apply Z.eqb_neq in Hu. rewrite Z.mod_opp_r_nz by assumption.
      rewrite wadd_signed_right, (signed_negative w y Hy). reflexivity.
  - rewrite (signed_nonnegative w x Hx), (signed_nonnegative w y Hy).
    pose proof (wurem_is_word w (wrap w x) (wrap w y)) as Hrange.
    rewrite wurem_mod, !wrap_wrap in Hrange |- *.
    destruct (wrap w x mod wrap w y =? 0); symmetry; now apply wrap_id.
Qed.

(** A nonzero signed modulus has the divisor's sign and a smaller magnitude. *)
Theorem wsmod_sign : forall w x y,
  (0 < signed w y -> 0 <= signed w (wsmod w x y) < signed w y) /\
  (signed w y < 0 -> signed w y < signed w (wsmod w x y) <= 0).
Proof.
  intros w x y. rewrite wsmod_signed, signed_wrap.
  pose proof (signed_range w y) as Hrange. pose proof (half_pos w) as Hhalf.
  split; intro Hy.
  - pose proof (Z.mod_pos_bound (signed w x) (signed w y) Hy) as Hmod.
    rewrite (signed_id w (signed w x mod signed w y)) by lia. exact Hmod.
  - pose proof (Z.mod_neg_bound (signed w x) (signed w y) Hy) as Hmod.
    rewrite (signed_id w (signed w x mod signed w y)) by lia. exact Hmod.
Qed.

(** * Unsigned division and powers of two *)

(** Unsigned division by zero gives the all-ones word. *)
Theorem wudiv_zero : forall w x, wudiv w x 0 = modulus w - 1.
Proof.
  intros w x. unfold wudiv. now rewrite wrap_0.
Qed.

(** Unsigned remainder by zero preserves the normalized dividend. *)
Theorem wurem_zero : forall w x, wurem w x 0 = wrap w x.
Proof.
  intros w x. unfold wurem. now rewrite wrap_0.
Qed.

(** Unsigned division agrees with integer division on words with nonzero divisor. *)
Theorem wudiv_spec : forall w x y, is_word w x -> is_word w y -> y <> 0 ->
  wudiv w x y = x / y.
Proof.
  intros w x y Hx Hy Hnz. unfold wudiv. rewrite !wrap_id by assumption.
  now rewrite (proj2 (Z.eqb_neq y 0) Hnz).
Qed.

(** Unsigned remainder agrees with integer modulo on words with nonzero divisor. *)
Theorem wurem_spec : forall w x y, is_word w x -> is_word w y -> y <> 0 ->
  wurem w x y = x mod y.
Proof.
  intros w x y Hx Hy Hnz. unfold wurem. rewrite !wrap_id by assumption.
  now rewrite (proj2 (Z.eqb_neq y 0) Hnz).
Qed.

(** A nonzero unsigned divisor strictly bounds its remainder. *)
Theorem wurem_lt : forall w x y, is_word w x -> is_word w y -> y <> 0 ->
  wurem w x y < y.
Proof.
  intros w x y Hx Hy Hnz. rewrite wurem_spec by assumption.
  apply Z.mod_pos_bound. unfold is_word in Hy. lia.
Qed.

(** Quotient and remainder reconstruct the dividend modulo its width. *)
Theorem wudiv_wurem_euclid : forall w x y,
  wadd w (wmul w y (wudiv w x y)) (wurem w x y) = wrap w x.
Proof.
  intros w x y. unfold wadd, wmul.
  rewrite (wrap_add w (wrap w _) _), wrap_wrap, (wrap_mul w y _).
  rewrite (wrap_id w _ (wudiv_is_word w x y)).
  rewrite <- (wrap_add w (wrap w y * _) _).
  unfold wudiv, wurem.
  destruct (wrap w y =? 0) eqn:Hy.
  - apply Z.eqb_eq in Hy. rewrite Hy. cbn. apply wrap_wrap.
  - apply Z.eqb_neq in Hy.
    rewrite <- Z.div_mod by exact Hy. apply wrap_wrap.
Qed.

(** Multiplication may use the signed interpretations of its operands. *)
Theorem wmul_signed : forall w x y,
  wmul w x y = wrap w (signed w x * signed w y).
Proof.
  intros w x y. unfold wmul. rewrite (wrap_mul w x y),
    (wrap_mul w (signed w x) (signed w y)), !wrap_signed. reflexivity.
Qed.

(** Nonnegative shift amounts below the width fit in a word. *)
Theorem small_amount_word : forall w k, 0 <= k < Zpos w -> is_word w k.
Proof.
  intros w k Hk. pose proof (width_lt_modulus w). unfold is_word. lia.
Qed.

(** A power of two below the width fits in a word. *)
Theorem pow2_word : forall w k, 0 <= k < Zpos w -> is_word w (2 ^ k).
Proof.
  intros w k Hk. split.
  - apply Z.pow_nonneg. lia.
  - apply Z.pow_lt_mono_r; lia.
Qed.

(** Multiplication by a representable power of two is a left shift. *)
Theorem wmul_wshl : forall w x k, is_word w x -> 0 <= k < Zpos w ->
  wmul w x (2 ^ k) = wshl w x k.
Proof.
  intros w x k Hx Hk. unfold wmul, wshl.
  rewrite (wrap_id w k (small_amount_word w k Hk)), (wrap_id w x Hx).
  now rewrite (proj2 (Z.leb_gt (Zpos w) k) (proj2 Hk)).
Qed.

(** Unsigned division by a representable power of two is a logical right shift. *)
Theorem wudiv_wlshr : forall w x k, is_word w x -> 0 <= k < Zpos w ->
  wudiv w x (2 ^ k) = wlshr w x k.
Proof.
  intros w x k Hx Hk. rewrite wudiv_spec by
    (try assumption; try apply pow2_word; try assumption;
      pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) (proj1 Hk)); lia).
  unfold wlshr. rewrite (wrap_id w k (small_amount_word w k Hk)), (wrap_id w x Hx).
  now rewrite (proj2 (Z.leb_gt (Zpos w) k) (proj2 Hk)).
Qed.

(** Unsigned remainder by a power of two keeps exactly the lower bits. *)
Theorem wurem_mask : forall w x k, is_word w x -> 0 <= k < Zpos w ->
  wurem w x (2 ^ k) = wand w x (2 ^ k - 1).
Proof.
  intros w x k Hx Hk. pose proof (pow2_word w k Hk) as Hpow.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) (proj1 Hk)) as Hpos.
  rewrite wurem_spec by (try assumption; lia).
  unfold wand. rewrite (wrap_id w x Hx), wrap_id by (unfold is_word in *; lia).
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  symmetry. apply Z.land_ones. exact (proj1 Hk).
Qed.

(** * Counts *)

(** Zero has one leading zero for each bit position. *)
Theorem wclz_zero : forall w, wclz w 0 = Zpos w.
Proof.
  intros w. unfold wclz. now rewrite wrap_0.
Qed.

(** Zero has one trailing zero for each bit position. *)
Theorem wctz_zero : forall w, wctz w 0 = Zpos w.
Proof.
  intros w. unfold wctz. now rewrite wrap_0.
Qed.

(** The highest set bit determines the leading-zero count of a nonzero word. *)
Theorem wclz_spec : forall w x, is_word w x -> x <> 0 ->
  wclz w x = Zpos w - 1 - Z.log2 x.
Proof.
  intros w x Hx Hnz. unfold wclz. rewrite (wrap_id w x Hx).
  now rewrite (proj2 (Z.eqb_neq x 0) Hnz).
Qed.

(** Leading-zero counts lie between zero and the width. *)
Theorem wclz_range : forall w x, 0 <= wclz w x <= Zpos w.
Proof.
  intros w x. unfold wclz. destruct (wrap w x =? 0); [lia|].
  pose proof (log2_word w _ (wrap_is_word w x)).
  pose proof (Z.log2_nonneg (wrap w x)). lia.
Qed.

(** Population counts lie between zero and the width. *)
Theorem wpopcnt_range : forall w x, 0 <= wpopcnt w x <= Zpos w.
Proof.
  intros w x. rewrite wpopcnt_spec. split; [lia|].
  rewrite <- (positive_nat_Z w). apply Nat2Z.inj_le.
  eapply Nat.le_trans; [apply List.filter_length_le|]. rewrite List.length_seq. lia.
Qed.

Local Lemma filter_complement_length : forall (A : Type) (f : A -> bool) xs,
  (length (filter f xs) + length (filter (fun a => negb (f a)) xs) = length xs)%nat.
Proof.
  intros A f xs. induction xs as [|a xs IH]; [reflexivity|].
  cbn [filter]. destruct (f a); cbn; lia.
Qed.

(** Complement exchanges set and clear bits below the width. *)
Theorem wpopcnt_wnot : forall w x, is_word w x ->
  wpopcnt w (wnot w x) = Zpos w - wpopcnt w x.
Proof.
  intros w x Hx. rewrite !wpopcnt_spec.
  rewrite (wrap_id w (wnot w x)) by apply wnot_is_word.
  assert (Hfilter :
    filter (fun i => Z.testbit (wnot w x) (Z.of_nat i)) (seq 0 (Pos.to_nat w)) =
    filter (fun i => negb (Z.testbit (wrap w x) (Z.of_nat i))) (seq 0 (Pos.to_nat w))).
  { apply filter_ext_in. intros i Hi. apply in_seq in Hi.
    rewrite testbit_wnot by (try exact Hx; lia).
    rewrite (wrap_id w x Hx).
    rewrite (proj2 (Z.ltb_lt (Z.of_nat i) (Zpos w))) by
      (rewrite <- positive_nat_Z; lia). reflexivity. }
  rewrite Hfilter.
  pose proof (filter_complement_length nat
    (fun i => Z.testbit (wrap w x) (Z.of_nat i)) (seq 0 (Pos.to_nat w))) as Hlength.
  rewrite length_seq in Hlength. rewrite <- (positive_nat_Z w). lia.
Qed.

Local Lemma lowbit_odd : forall a, Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  intros a. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_opp by exact Hi.
  replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec i 0) as [->|Hnz].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite Z.pow2_bits_false with (n := 0) by lia.
    destruct (Z.testbit a (i - 1)); reflexivity.
Qed.

Local Lemma lowbit_double : forall a,
  Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (-a).
Proof.
  intros a. replace (- (2 * a)) with (2 * (-a)) by ring.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hnz].
  - now rewrite !Z.testbit_even_0.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Local Lemma positive_lowbit : forall p, exists k,
  0 <= k /\ Z.land (Zpos p) (- Zpos p) = 2 ^ k /\
  Z.testbit (Zpos p) k = true /\
  forall j, 0 <= j < k -> Z.testbit (Zpos p) j = false.
Proof.
  intros p. induction p as [p IH|p IH|].
  - exists 0. split; [lia|]. split.
    + change (Z.land (2 * Zpos p + 1) (- (2 * Zpos p + 1)) = 1).
      apply lowbit_odd.
    + split; [reflexivity|]. intros j Hj. lia.
  - destruct IH as [k [Hk [Hlow [Hset Hclear]]]]. exists (Z.succ k).
    split; [lia|]. split.
    + change (Z.land (2 * Zpos p) (- (2 * Zpos p)) = 2 ^ Z.succ k).
      rewrite lowbit_double, Hlow, Z.pow_succ_r by exact Hk. reflexivity.
    + split.
      * change (Z.testbit (2 * Zpos p) (Z.succ k) = true).
        now rewrite Z.testbit_even_succ by exact Hk.
      * intros j Hj. change (Z.testbit (2 * Zpos p) j = false).
        destruct (Z.eq_dec j 0) as [->|Hnz]; [apply Z.testbit_even_0|].
        replace j with (Z.succ (j - 1)) by lia.
        rewrite Z.testbit_even_succ by lia. apply Hclear. lia.
  - exists 0. split; [lia|]. split; [reflexivity|].
    split; [reflexivity|]. intros j Hj. lia.
Qed.

(** The trailing-zero count names the first set bit of a nonzero word. *)
Theorem wctz_spec : forall w x, is_word w x -> x <> 0 ->
  Z.testbit x (wctz w x) = true /\
  forall j, 0 <= j < wctz w x -> Z.testbit x j = false.
Proof.
  intros w x Hx Hnz. unfold wctz. rewrite (wrap_id w x Hx).
  rewrite (proj2 (Z.eqb_neq x 0) Hnz).
  destruct x as [|p|p]; try (unfold is_word in Hx; lia).
  destruct (positive_lowbit p) as [k [Hk [Hlow Hbits]]].
  rewrite Hlow, Z.log2_pow2 by exact Hk. exact Hbits.
Qed.

(** * Rotations *)

(** Disjoint low and high parts contribute their bits without a carry. *)
Theorem split_sum_bits : forall a b k i, 0 <= k -> 0 <= b < 2 ^ k -> 0 <= i ->
  Z.testbit (a * 2 ^ k + b) i =
    if i <? k then Z.testbit b i else Z.testbit a (i - k).
Proof.
  intros a b k i Hk Hb Hi.
  assert (Hdisjoint : Z.land (a * 2 ^ k) b = 0).
  { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_ge_dec j k) as [Hlow|Hhigh].
    - rewrite Z.mul_pow2_bits_low by exact Hlow. reflexivity.
    - assert (Hbit : Z.testbit b j = false).
      { rewrite <- (Z.mod_small b (2 ^ k) Hb) at 1.
        apply Z.mod_pow2_bits_high. lia. }
      rewrite Hbit. apply Bool.andb_false_r. }
  rewrite Z.add_nocarry_lxor by exact Hdisjoint. rewrite Z.lxor_spec.
  destruct (i <? k) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. rewrite Z.mul_pow2_bits_low by exact Hlow. reflexivity.
  - apply Z.ltb_ge in Hlow. rewrite Z.mul_pow2_bits by exact Hk.
    assert (Hbit : Z.testbit b i = false).
    { rewrite <- (Z.mod_small b (2 ^ k) Hb) at 1.
      apply Z.mod_pow2_bits_high. lia. }
    rewrite Hbit. apply Bool.xorb_false_r.
Qed.

Local Lemma rotation_index : forall n i y, 0 < n -> 0 <= i < n ->
  (i - y) mod n = if i <? y mod n then i + n - y mod n else i - y mod n.
Proof.
  intros n i y Hn Hi. pose proof (Z.mod_pos_bound y n Hn) as Hk.
  replace (i - y) with ((i - y mod n) + (- (y / n)) * n)
    by (pose proof (Z.div_mod y n ltac:(lia)); nia).
  rewrite Z.mod_add by lia. destruct (i <? y mod n) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. symmetry. apply Z.mod_unique with (q := -1).
    + left. lia.
    + ring.
  - apply Z.ltb_ge in Hlow. apply Z.mod_small. lia.
Qed.

Local Lemma rotate_high_part : forall w x k, 0 <= k < Zpos w ->
  0 <= wrap w x / 2 ^ (Zpos w - k) < 2 ^ k.
Proof.
  intros w x k Hk. pose proof (wrap_is_word w x) as Hx.
  assert (Hd : 0 < 2 ^ (Zpos w - k)) by (apply Z.pow_pos_nonneg; lia).
  split.
  - apply Z.div_pos; [exact (proj1 Hx)|lia].
  - apply Z.div_lt_upper_bound; [exact Hd|].
    rewrite <- Z.pow_add_r by lia.
    replace (Zpos w - k + k) with (Zpos w) by lia. exact (proj2 Hx).
Qed.

(** Left rotation reads each source bit at the corresponding cyclic index. *)
Theorem testbit_wrotl : forall w x y i, 0 <= i < Zpos w ->
  Z.testbit (wrotl w x y) i =
    Z.testbit (wrap w x) ((i - wrap w y) mod Zpos w).
Proof.
  intros w x y i Hi.
  pose proof (Z.mod_pos_bound (wrap w y) (Zpos w) ltac:(lia)) as Hk.
  unfold wrotl. rewrite testbit_wrap by exact (proj1 Hi).
  rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)). cbn [andb].
  rewrite split_sum_bits by
    (try exact (proj1 Hk); try exact (proj1 Hi); now apply rotate_high_part).
  rewrite rotation_index by lia.
  destruct (i <? wrap w y mod Zpos w).
  - rewrite Z.div_pow2_bits by lia. f_equal. lia.
  - reflexivity.
Qed.

(** Reducing a rotation amount modulo the width leaves the rotation unchanged. *)
Theorem wrotl_mod : forall w x y,
  wrotl w x y = wrotl w x (wrap w y mod Zpos w).
Proof.
  intros w x y. unfold wrotl.
  pose proof (Z.mod_pos_bound (wrap w y) (Zpos w) ltac:(lia)) as Hk.
  rewrite (wrap_id w (wrap w y mod Zpos w)) by (apply small_amount_word; exact Hk).
  now rewrite Z.mod_mod by lia.
Qed.

(** Right rotation undoes left rotation by the same amount. *)
Theorem wrotr_wrotl : forall w x y, wrotr w (wrotl w x y) y = wrap w x.
Proof.
  intros w x y. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - unfold wrotr. rewrite testbit_wrotl by lia.
    rewrite (wrap_id w (wrotl w x y)) by (unfold wrotl; apply wrap_is_word).
    rewrite testbit_wrotl by (apply Z.mod_pos_bound; lia).
    pose proof (Z.mod_pos_bound (wrap w y) (Zpos w) ltac:(lia)) as Hk.
    assert (Hamount : is_word w (Zpos w - wrap w y mod Zpos w)).
    { pose proof (width_lt_modulus w). unfold is_word. lia. }
    rewrite (wrap_id w _ Hamount).
    replace (((i - (Zpos w - wrap w y mod Zpos w)) mod Zpos w - wrap w y)
      mod Zpos w) with i; [reflexivity|].
    rewrite Zminus_mod, Z.mod_mod by lia.
    rewrite <- Zminus_mod by lia.
    replace (i - (Zpos w - wrap w y mod Zpos w) - wrap w y) with
      (i - Zpos w - (wrap w y / Zpos w) * Zpos w)
      by (pose proof (Z.div_mod (wrap w y) (Zpos w) ltac:(lia)); nia).
    replace (i - Zpos w - wrap w y / Zpos w * Zpos w) with
      (i + (-1 - wrap w y / Zpos w) * Zpos w) by ring.
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
  - unfold wrotr, wrotl. rewrite testbit_wrap, testbit_wrap by exact Hi.
    now rewrite (proj2 (Z.ltb_ge i (Zpos w)) ltac:(lia)).
Qed.

(** * Width bounds and concatenation *)

(** Increasing the width increases the modulus. *)
Theorem modulus_monotone : forall w t, (w <= t)%positive -> modulus w <= modulus t.
Proof.
  intros w t Hle. unfold modulus. apply Z.pow_le_mono_r; [lia|].
  apply Pos2Z.pos_le_pos. exact Hle.
Qed.

(** Adding a positive width gives a wider word. *)
Theorem width_add_le : forall w n, (w <= w + n)%positive.
Proof.
  intros w n. apply Pos.lt_le_incl. apply Pos.lt_add_r.
Qed.

(** A word remains in range at every larger width. *)
Theorem word_widen : forall w t x, (w <= t)%positive -> is_word w x -> is_word t x.
Proof.
  intros w t x Hle Hx. pose proof (modulus_monotone w t Hle).
  unfold is_word in *. lia.
Qed.

(** Increasing the width increases the signed half range. *)
Theorem half_monotone : forall w t, (w <= t)%positive -> half w <= half t.
Proof.
  intros w t Hle. unfold half. apply Z.pow_le_mono_r; [lia|].
  apply Pos2Z.pos_le_pos in Hle. lia.
Qed.

(** Adding widths multiplies their moduli. *)
Theorem modulus_add : forall w w2, modulus (w + w2)%positive = modulus w * modulus w2.
Proof.
  intros w w2. unfold modulus. rewrite Pos2Z.inj_add. apply Z.pow_add_r; lia.
Qed.

(** Concatenating normalized words fits in the sum of their widths. *)
Theorem concat_is_word : forall w w2 x y,
  is_word (w + w2)%positive (wrap w x * modulus w2 + wrap w2 y).
Proof.
  intros w w2 x y. pose proof (wrap_is_word w x) as Hx.
  pose proof (wrap_is_word w2 y) as Hy. pose proof (modulus_pos w2).
  unfold is_word in *. rewrite modulus_add. nia.
Qed.
