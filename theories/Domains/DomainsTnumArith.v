(** * Known-bit arithmetic

    Carry bounds provide closed-form addition and subtraction of known-bit masks.
    For example, adding one to the cube containing seven and fifteen exposes carry uncertainty.
    Builds on: DomainsTnum and the public Bits arithmetic equations. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsTnum.

Local Open Scope Z_scope.

Definition tnum_not (w : width) (a : tnum) : tnum :=
  Tnum (wrap w (ones a)) (wrap w (zeros a)).

Definition tnum_and (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (zeros a) (zeros b)) (wand w (ones a) (ones b)).

Definition tnum_or (w : width) (a b : tnum) : tnum :=
  Tnum (wand w (zeros a) (zeros b)) (wor w (ones a) (ones b)).

Definition tnum_xor (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (wand w (zeros a) (zeros b)) (wand w (ones a) (ones b)))
    (wor w (wand w (zeros a) (ones b)) (wand w (ones a) (zeros b))).

(** Complement swaps the two known-bit masks. *)
Theorem tnum_not_sound : forall w a z,
  tnum_gamma w a z -> tnum_gamma w (tnum_not w a) (wnot w z).
Proof.
  intros w a z Hgamma. apply tnum_gamma_bits in Hgamma.
  destruct Hgamma as [Hz Ho]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_not zeros ones] in Hbit;
    rewrite tnum_wrap_bit in Hbit by exact Hi; rewrite tnum_not_bit by exact Hi.
  - now rewrite (Ho i Hi Hbit).
  - now rewrite (Hz i Hi Hbit).
Qed.

(** Conjunction propagates known zero bits from either operand and shared known one bits. *)
Theorem tnum_and_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_and w a b) (wand w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_and zeros ones] in Hbit;
    rewrite tnum_and_bit by exact Hi.
  - rewrite tnum_or_bit in Hbit by exact Hi. apply orb_true_iff in Hbit as [Hz|Hz].
    + now rewrite (Haz i Hi Hz).
    + rewrite (Hbz i Hi Hz). apply andb_false_r.
  - rewrite tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Ho Ho'].
    now rewrite (Hao i Hi Ho), (Hbo i Hi Ho').
Qed.

(** Disjunction propagates known one bits from either operand and shared known zero bits. *)
Theorem tnum_or_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_or w a b) (wor w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_or zeros ones] in Hbit;
    rewrite tnum_or_bit by exact Hi.
  - rewrite tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Hz Hz'].
    now rewrite (Haz i Hi Hz), (Hbz i Hi Hz').
  - rewrite tnum_or_bit in Hbit by exact Hi. apply orb_true_iff in Hbit as [Ho|Ho].
    + now rewrite (Hao i Hi Ho).
    + rewrite (Hbo i Hi Ho). apply orb_true_r.
Qed.

(** Exclusive-or retains each bit whose two input bits are known. *)
Theorem tnum_xor_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_xor w a b) (wxor w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_xor zeros ones] in Hbit;
    rewrite tnum_or_bit, !tnum_and_bit in Hbit by exact Hi;
    rewrite tnum_xor_bit by exact Hi;
    apply orb_true_iff in Hbit as [Hbit|Hbit]; apply andb_true_iff in Hbit as [Hl Hr].
  - now rewrite (Haz i Hi Hl), (Hbz i Hi Hr).
  - now rewrite (Hao i Hi Hl), (Hbo i Hi Hr).
  - now rewrite (Haz i Hi Hl), (Hbo i Hi Hr).
  - now rewrite (Hao i Hi Hl), (Hbz i Hi Hr).
Qed.

(** A carry stream obeys the full-adder recurrence and an initial carry bit. *)
Definition tnum_carry (a b c : Z) (initial : bool) : Prop :=
  c / 2 = Z.lor (Z.land a b) (Z.land c (Z.lor a b)) /\ Z.testbit c 0 = initial.

Local Lemma tnum_carry_step : forall a b c initial i,
  tnum_carry a b c initial -> 0 <= i ->
  Z.testbit c (Z.succ i) =
    ((Z.testbit a i && Z.testbit b i) ||
      (Z.testbit c i && (Z.testbit a i || Z.testbit b i))).
Proof.
  intros a b c initial i [Hstep _] Hi.
  rewrite <- Z.div2_bits by exact Hi.
  rewrite Hstep, !Z.lor_spec, !Z.land_spec, !Z.lor_spec. reflexivity.
Qed.

Local Lemma tnum_carry_monotone : forall w a b a' b' c c' initial,
  tnum_carry a b c initial -> tnum_carry a' b' c' initial ->
  (forall i, 0 <= i < Zpos w -> Z.testbit a i = true -> Z.testbit a' i = true) ->
  (forall i, 0 <= i < Zpos w -> Z.testbit b i = true -> Z.testbit b' i = true) ->
  forall i, 0 <= i <= Zpos w -> Z.testbit c i = true -> Z.testbit c' i = true.
Proof.
  intros w a b a' b' c c' initial Hc Hc' Ha Hb i Hi.
  assert (Hnat : forall n, (n <= Pos.to_nat w)%nat ->
    Z.testbit c (Z.of_nat n) = true -> Z.testbit c' (Z.of_nat n) = true).
  { intro n. induction n as [|n IH]; intros Hn Hbit.
    - change (Z.testbit c 0 = true) in Hbit. rewrite (proj2 Hc) in Hbit.
      change (Z.testbit c' 0 = true). now rewrite (proj2 Hc').
    - rewrite Nat2Z.inj_succ,
        (tnum_carry_step a b c initial (Z.of_nat n) Hc ltac:(lia)) in Hbit.
      rewrite Nat2Z.inj_succ,
        (tnum_carry_step a' b' c' initial (Z.of_nat n) Hc' ltac:(lia)).
      pose proof (Ha (Z.of_nat n) ltac:(rewrite <- positive_nat_Z; lia)) as Haa.
      pose proof (Hb (Z.of_nat n) ltac:(rewrite <- positive_nat_Z; lia)) as Hbb.
      specialize (IH ltac:(lia)).
      destruct (Z.testbit a (Z.of_nat n)), (Z.testbit b (Z.of_nat n)),
        (Z.testbit a' (Z.of_nat n)), (Z.testbit b' (Z.of_nat n)),
        (Z.testbit c (Z.of_nat n)), (Z.testbit c' (Z.of_nat n));
        cbn in *; intuition discriminate. }
  replace i with (Z.of_nat (Z.to_nat i)) by (rewrite Z2Nat.id; lia).
  apply Hnat. apply Nat2Z.inj_le. rewrite positive_nat_Z, Z2Nat.id by lia. lia.
Qed.

Local Lemma tnum_sum_known : forall w a b x y initial i,
  tnum_gamma w a x -> tnum_gamma w b y -> 0 <= i < Zpos w ->
  Z.testbit (tnum_mask w a) i = false -> Z.testbit (tnum_mask w b) i = false ->
  Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i =
    Z.testbit (tnum_max w a + tnum_max w b + Z.b2z initial) i ->
  Z.testbit (x + y + Z.b2z initial) i =
    Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i.
Proof.
  intros w a b x y initial i Ha Hb Hi Hma Hmb Heq.
  destruct (Z.add_carry_bits x y initial) as [c [Hsum [Hstep Hzero]]].
  destruct (Z.add_carry_bits (tnum_min w a) (tnum_min w b) initial)
    as [cl [Hsuml [Hstepl Hzerol]]].
  destruct (Z.add_carry_bits (tnum_max w a) (tnum_max w b) initial)
    as [ch [Hsumh [Hsteph Hzeroh]]].
  destruct (tnum_value_bounds w a x Ha) as [Hal Hah].
  destruct (tnum_value_bounds w b y Hb) as [Hbl Hbh].
  pose proof (tnum_carry_monotone w _ _ _ _ _ _ initial (conj Hstepl Hzerol)
    (conj Hstep Hzero) Hal Hbl i ltac:(lia)) as Hlower.
  pose proof (tnum_carry_monotone w _ _ _ _ _ _ initial (conj Hstep Hzero)
    (conj Hsteph Hzeroh) Hah Hbh i ltac:(lia)) as Hupper.
  destruct (tnum_known_bit w a x i Ha Hi Hma) as [Halbit Hahbit].
  destruct (tnum_known_bit w b y i Hb Hi Hmb) as [Hblbit Hbhbit].
  rewrite Hsuml, Hsumh, !Z.lxor_spec, Halbit, Hahbit, Hblbit, Hbhbit in Heq.
  rewrite Hsum, Hsuml, !Z.lxor_spec, Halbit, Hblbit.
  destruct (Z.testbit x i), (Z.testbit y i), (Z.testbit c i),
    (Z.testbit cl i), (Z.testbit ch i); cbn in *; intuition discriminate.
Qed.

Definition tnum_adc_uncertain (w : width) (a b : tnum) (initial : bool) : Z :=
  Z.lor (Z.lxor (tnum_min w a + tnum_min w b + Z.b2z initial)
      (tnum_max w a + tnum_max w b + Z.b2z initial))
    (Z.lor (tnum_mask w a) (tnum_mask w b)).

(** Low and high carry streams bound the result bits that may change. *)
Definition tnum_adc (w : width) (a b : tnum) (initial : bool) : tnum :=
  let v := tnum_min w a + tnum_min w b + Z.b2z initial in
  let m := tnum_adc_uncertain w a b initial in
  Tnum (wrap w (Z.lnot (Z.lor v m))) (wrap w (Z.land v (Z.lnot m))).

Local Lemma tnum_adc_known : forall w a b x y initial i,
  tnum_gamma w a x -> tnum_gamma w b y -> 0 <= i < Zpos w ->
  Z.testbit (tnum_adc_uncertain w a b initial) i = false ->
  Z.testbit (x + y + Z.b2z initial) i =
    Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i.
Proof.
  intros w a b x y initial i Ha Hb Hi Hm.
  unfold tnum_adc_uncertain in Hm. rewrite !Z.lor_spec, Z.lxor_spec in Hm.
  apply orb_false_iff in Hm as [Hsum Hm]. apply orb_false_iff in Hm as [Hma Hmb].
  eapply tnum_sum_known; try eassumption.
  destruct (Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i),
    (Z.testbit (tnum_max w a + tnum_max w b + Z.b2z initial) i);
    cbn in Hsum; congruence.
Qed.

(** Addition with either initial carry contains every concrete modular sum. *)
Theorem tnum_adc_sound : forall w a b x y initial,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_adc w a b initial) (wrap w (x + y + Z.b2z initial)).
Proof.
  intros w a b x y initial Ha Hb. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_adc zeros ones] in Hbit;
    rewrite tnum_wrap_bit, ?Z.land_spec, ?Z.lnot_spec, ?Z.lor_spec in Hbit by
      (try exact Hi; lia).
  - apply negb_true_iff in Hbit. apply orb_false_iff in Hbit as [Hv Hm].
    rewrite tnum_wrap_bit, (tnum_adc_known w a b x y initial i Ha Hb Hi Hm)
      by exact Hi. exact Hv.
  - apply andb_true_iff in Hbit as [Hv Hm]. apply negb_true_iff in Hm.
    rewrite tnum_wrap_bit, (tnum_adc_known w a b x y initial i Ha Hb Hi Hm)
      by exact Hi. exact Hv.
Qed.

Definition tnum_add (w : width) (a b : tnum) : tnum := tnum_adc w a b false.

Definition tnum_sub (w : width) (a b : tnum) : tnum := tnum_adc w a (tnum_not w b) true.

Definition tnum_neg (w : width) (a : tnum) : tnum := tnum_sub w (tnum_const w 0) a.

(** Closed-form addition contains every concrete modular sum. *)
Theorem tnum_add_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w (tnum_add w a b) (wadd w x y).
Proof.
  intros w a b x y Ha Hb. rewrite wadd_value. unfold tnum_add.
  replace (x + y) with (x + y + Z.b2z false) by (cbn [Z.b2z]; ring).
  now apply tnum_adc_sound.
Qed.

(** Subtraction uses complemented bits and a set initial carry. *)
Theorem tnum_sub_sound : forall w a b x y,
  is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_sub w a b) (wsub w x y).
Proof.
  intros w a b x y Hy Ha Hb.
  pose proof (tnum_adc_sound w a (tnum_not w b) x (wnot w y) true Ha
    (tnum_not_sound w b y Hb)) as Hresult.
  unfold tnum_sub. cbn [Z.b2z] in Hresult.
  assert (Hnot : wnot w y = modulus w - 1 - y).
  { pose proof (wnot_lnot w y) as Hnot.
    rewrite (wrap_id w y Hy), lnot_value in Hnot.
    rewrite wrap_mod in Hnot. rewrite Hnot.
    symmetry. apply Z.mod_unique with (q := -1).
    - left. unfold is_word in Hy. lia.
    - ring. }
  rewrite Hnot in Hresult.
  replace (x + (modulus w - 1 - y) + 1) with ((x - y) + 1 * modulus w)
    in Hresult by ring.
  rewrite wrap_add_modulus in Hresult. rewrite wsub_value. exact Hresult.
Qed.

(** Negation contains the modular additive inverse of every represented word. *)
Theorem tnum_neg_sound : forall w a x,
  is_word w x -> tnum_gamma w a x -> tnum_gamma w (tnum_neg w a) (wneg w x).
Proof.
  intros w a x Hx Ha. rewrite wneg_value.
  replace (-x) with (0 - x) by ring. rewrite <- wsub_value.
  apply tnum_sub_sound; try assumption.
  pose proof (tnum_const_sound w 0) as Hzero. now rewrite wrap_0 in Hzero.
Qed.

Definition tnum_bitlen (h : Z) : Z := if h =? 0 then 0 else Z.succ (Z.log2 h).

Local Lemma tnum_bitlen_bound : forall h, 0 <= h ->
  0 <= tnum_bitlen h /\ h < 2 ^ tnum_bitlen h.
Proof.
  intros h Hh. unfold tnum_bitlen. destruct (h =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. subst h. cbn. lia.
  - apply Z.eqb_neq in Hz. pose proof (Z.log2_nonneg h).
    pose proof (Z.log2_spec h ltac:(lia)). lia.
Qed.

Definition tnum_upper (w : width) (h : Z) : tnum :=
  Tnum (wnot w (Z.ones (tnum_bitlen h))) 0.

(** Leading zero bits of an upper bound hold for every nonnegative smaller integer. *)
Theorem tnum_upper_sound : forall w h x,
  0 <= x <= h -> tnum_gamma w (tnum_upper w h) x.
Proof.
  intros w h x Hx. pose proof (tnum_bitlen_bound h ltac:(lia)) as [Hk Hbound].
  apply tnum_gamma_bits. split; intros i Hi Hbit.
  - cbn [tnum_upper zeros] in Hbit. rewrite tnum_not_bit in Hbit by exact Hi.
    apply negb_true_iff in Hbit.
    assert (Hhigh : tnum_bitlen h <= i).
    { destruct (Z_lt_ge_dec i (tnum_bitlen h)); [|lia].
      rewrite Z.ones_spec_low in Hbit by lia. discriminate. }
    rewrite <- (Z.mod_small x (2 ^ tnum_bitlen h) ltac:(lia)).
    apply Z.mod_pow2_bits_high. lia.
  - cbn [tnum_upper ones] in Hbit. rewrite Z.bits_0 in Hbit. discriminate.
Qed.

Definition tnum_udiv (w : width) (a b : tnum) : tnum :=
  if wrap w (ones b) =? 0 then tnum_top else tnum_upper w (tnum_max w a).

Definition tnum_urem (w : width) (a : tnum) : tnum := tnum_upper w (tnum_max w a).

(** A provably nonzero divisor preserves leading zeros of the dividend. *)
Theorem tnum_udiv_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_udiv w a b) (wudiv w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_udiv.
  destruct (wrap w (ones b) =? 0) eqn:Hnonzero; [apply tnum_top_sound|].
  apply Z.eqb_neq in Hnonzero.
  pose proof (tnum_unsigned_bounds w b y Hy Hb) as Hbounds.
  pose proof (wrap_is_word w (ones b)) as Hones.
  assert (Hynz : y <> 0) by (unfold tnum_min, is_word in *; lia).
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hdividend.
  rewrite wudiv_spec by assumption. apply tnum_upper_sound.
  split; [apply Z.div_pos; unfold is_word in *; lia|].
  eapply Z.le_trans; [|exact (proj2 Hdividend)].
  apply Z.div_le_upper_bound; unfold is_word in *; nia.
Qed.

(** Unsigned remainder preserves leading zeros even for the specified zero-divisor case. *)
Theorem tnum_urem_sound : forall w a x y,
  is_word w x -> is_word w y -> tnum_gamma w a x ->
  tnum_gamma w (tnum_urem w a) (wurem w x y).
Proof.
  intros w a x y Hx Hy Ha.
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hbounds. unfold tnum_urem.
  destruct (Z.eq_dec y 0) as [->|Hnz].
  - rewrite wurem_zero, (wrap_id w x Hx). apply tnum_upper_sound.
    unfold is_word in Hx. lia.
  - rewrite wurem_spec by assumption. apply tnum_upper_sound. split.
    + apply Z.mod_pos_bound. unfold is_word in Hy. lia.
    + eapply Z.le_trans; [|exact (proj2 Hbounds)].
      apply Z.mod_le; unfold is_word in *; lia.
Qed.

Definition tnum_linux_add (w : width) (a b : tnum) : tnum :=
  let v := tnum_min w a + tnum_min w b in
  let m := Z.lor (Z.lxor (v + (tnum_mask w a + tnum_mask w b)) v)
    (Z.lor (tnum_mask w a) (tnum_mask w b)) in
  Tnum (wrap w (Z.lnot (Z.lor v m))) (wrap w (Z.land v (Z.lnot m))).

(** The carry-based implementation agrees with the Linux closed form on consistent masks. *)
Theorem tnum_add_linux_agrees : forall w a b,
  tnum_empty w a = false -> tnum_empty w b = false ->
  tnum_add w a b = tnum_linux_add w a b.
Proof.
  intros w a b Ha Hb. unfold tnum_add, tnum_adc, tnum_adc_uncertain, tnum_linux_add.
  cbn [Z.b2z]. rewrite !Z.add_0_r, (tnum_max_value_mask w a Ha),
    (tnum_max_value_mask w b Hb).
  replace (tnum_min w a + tnum_mask w a + (tnum_min w b + tnum_mask w b)) with
    (tnum_min w a + tnum_min w b + (tnum_mask w a + tnum_mask w b)) by ring.
  rewrite Z.lxor_comm. reflexivity.
Qed.
