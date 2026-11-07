(** * Selectable known-bit multiplication

    Low-bit, staged and independent value/mask accumulators provide selectable product bounds.
    For example, meeting the last two choices contains every concrete product and refines both.
    Builds on: DomainsTnumArith, DomainsTnumShift and the public Bits arithmetic laws. *)

From Stdlib Require Import ZArith NArith Bool Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith BitsOp.
From Galois.Domains Require Import DomainsTnum DomainsTnumArith DomainsTnumShift.
Import Cost.Notations.

Local Open Scope Z_scope.

Definition tnum_trailing (w : width) (a : tnum) : Z := wctz w (wnot w (zeros a)).

(** Trailing-zero counts include the all-zero word's count equal to its width. *)
Theorem tnum_ctz_range : forall w x, 0 <= wctz w x <= Zpos w.
Proof.
  intros w x. destruct (Z.eq_dec (wrap w x) 0) as [Hz|Hnz].
  - rewrite <- (word_fun1_normalised bvctz wctz w x eq_refl), Hz, wctz_zero. lia.
  - rewrite <- (word_fun1_normalised bvctz wctz w x eq_refl).
    destruct (wctz_spec w _ (wrap_is_word w x) Hnz) as [Hset _].
    split.
    + destruct (Z_le_gt_dec 0 (wctz w (wrap w x))); [assumption|].
      rewrite Z.testbit_neg_r in Hset by lia. discriminate.
    + destruct (Z_lt_ge_dec (wctz w (wrap w x)) (Zpos w)); [lia|].
      rewrite (word_bits_high w (wrap w x) (wctz w (wrap w x))
        (wrap_is_word w x) ltac:(lia)) in Hset. discriminate.
Qed.

Lemma tnum_trailing_clear : forall w a x i,
  tnum_gamma w a x -> 0 <= i < tnum_trailing w a -> Z.testbit x i = false.
Proof.
  intros w a x i Ha Hi. apply tnum_gamma_bits in Ha. destruct Ha as [Hz _].
  pose proof (tnum_ctz_range w (wnot w (zeros a))) as Hrange.
  apply (Hz i ltac:(unfold tnum_trailing in Hi; lia)).
  assert (Hclear : Z.testbit (wnot w (zeros a)) i = false).
  { destruct (Z.eq_dec (wnot w (zeros a)) 0) as [Hnone|Hsome].
    - now rewrite Hnone, Z.bits_0.
    - apply (proj2 (wctz_spec w _ (wnot_is_word w _) Hsome)). exact Hi. }
  rewrite tnum_not_bit in Hclear by (unfold tnum_trailing in Hi; lia).
  now apply negb_false_iff in Hclear.
Qed.

Lemma tnum_trailing_factor : forall w a x,
  tnum_gamma w a x -> exists q, x = q * 2 ^ tnum_trailing w a.
Proof.
  intros w a x Ha. pose proof (tnum_ctz_range w (wnot w (zeros a))) as Hrange.
  assert (Hmod : x mod 2 ^ tnum_trailing w a = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
    destruct (Z_lt_ge_dec i (tnum_trailing w a)) as [Hlow|Hhigh].
    - rewrite Z.mod_pow2_bits_low by exact Hlow.
      eapply tnum_trailing_clear; [exact Ha|lia].
    - apply Z.mod_pow2_bits_high. unfold tnum_trailing in *. lia. }
  exists (x / 2 ^ tnum_trailing w a).
  pose proof (Z.div_mod x (2 ^ tnum_trailing w a)
    ltac:(pose proof (Z.pow_pos_nonneg 2 (tnum_trailing w a) ltac:(lia)
      ltac:(unfold tnum_trailing; lia)); lia)) as Heq.
  rewrite Hmod in Heq. lia.
Qed.

Definition tnum_mul_low (w : width) (a b : tnum) : tnum :=
  Tnum (wrap w (Z.ones (tnum_trailing w a + tnum_trailing w b))) 0.

(** The legacy low choice evaluates constant products and otherwise keeps trailing zeros. *)
Definition tnum_mul (w : width) (a b : tnum) : tnum :=
  match tnum_constant w a, tnum_constant w b with
  | Some x, Some y => tnum_const w (wmul w x y)
  | _, _ => tnum_mul_low w a b
  end.

(** Trailing-zero counts add under multiplication. *)
Theorem tnum_mul_low_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_low w a b) (wmul w x y).
Proof.
  intros w a b x y Ha Hb.
  destruct (tnum_trailing_factor w a x Ha) as [qa Hx].
  destruct (tnum_trailing_factor w b y Hb) as [qb Hy].
  pose proof (tnum_ctz_range w (wnot w (zeros a))) as Hra.
  pose proof (tnum_ctz_range w (wnot w (zeros b))) as Hrb.
  change (0 <= tnum_trailing w a <= Zpos w) in Hra.
  change (0 <= tnum_trailing w b <= Zpos w) in Hrb.
  apply tnum_gamma_bits. split; intros i Hi Hbit.
  - cbn [tnum_mul_low zeros] in Hbit. rewrite tnum_wrap_bit in Hbit by exact Hi.
    assert (Hlow : i < tnum_trailing w a + tnum_trailing w b).
    { destruct (Z_lt_ge_dec i (tnum_trailing w a + tnum_trailing w b)); [assumption|].
      rewrite Z.ones_spec_high in Hbit by lia. discriminate. }
    rewrite wmul_value, tnum_wrap_bit by exact Hi. rewrite Hx, Hy.
    replace (qa * 2 ^ tnum_trailing w a * (qb * 2 ^ tnum_trailing w b)) with
      ((qa * qb) * 2 ^ (tnum_trailing w a + tnum_trailing w b)) by
      (rewrite Z.pow_add_r by lia; ring).
    apply Z.mul_pow2_bits_low. exact Hlow.
  - cbn [tnum_mul_low ones] in Hbit. rewrite Z.bits_0 in Hbit. discriminate.
Qed.

(** The legacy constant-or-low rule contains every concrete word product. *)
Theorem tnum_mul_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_mul.
  destruct (tnum_constant w a) as [ca|] eqn:Hca,
    (tnum_constant w b) as [cb|] eqn:Hcb; try now apply tnum_mul_low_sound.
  rewrite (tnum_constant_value w a x ca Hx Ha Hca),
    (tnum_constant_value w b y cb Hy Hb Hcb).
  rewrite <- (wrap_id w (wmul w ca cb) (word_fun2_is_word bvmul wmul w ca cb eq_refl))
    at 2. apply tnum_const_sound.
Qed.

(** One stage visits one multiplier bit and performs at most one abstract addition. *)
Definition tnum_mul_step_c (w : width) (a b : tnum) (s : Z * tnum)
    : Cost.t ((Z * tnum) + tnum) :=
  let '(i, r) := s in
  Cost.step ;;
  Cost.ret (inl (Z.succ i,
    if Z.testbit (zeros b) i then r
    else
      let sum := tnum_add w r (tnum_shl_scalar w i a) in
      if Z.testbit (ones b) i then sum else tnum_join w r sum)).

(** The common binary-fuel driver supplies one visit per multiplier bit. *)
Definition tnum_mul_stages_c (w : width) (a b : tnum) : Cost.t tnum :=
  if tnum_empty w a || tnum_empty w b then Cost.ret (bot (tnum_lattice w)) else
  let* result := iterate (tnum_mul_step_c w a b) w (0, tnum_const w 0) in
  Cost.ret
    (match result with
    | inl s => snd s
    | inr r => r
    end).

Definition tnum_mul_stages (w : width) (a b : tnum) : tnum :=
  Cost.value (tnum_mul_stages_c w a b).

Lemma tnum_mul_prefix : forall y i, 0 <= i ->
  y mod 2 ^ (i + 1) = y mod 2 ^ i + Z.b2z (Z.testbit y i) * 2 ^ i.
Proof.
  intros y i Hi.
  pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) Hi) as Hpower.
  destruct (Z.testbit_spec y i Hi) as [l [h [Hl Heq]]].
  assert (Hlow : y mod 2 ^ i = l).
  { symmetry. apply Z.mod_unique with (q := Z.b2z (Z.testbit y i) + 2 * h).
    - left. exact Hl.
    - nia. }
  rewrite Hlow. symmetry. apply Z.mod_unique with (q := h).
  - left. rewrite Z.pow_add_r, Z.pow_1_r by lia.
    destruct (Z.testbit y i); cbn [Z.b2z]; lia.
  - rewrite Z.pow_add_r, Z.pow_1_r by lia. nia.
Qed.

Lemma tnum_mul_partial_add : forall w x y i, 0 <= i < Zpos w -> is_word w x ->
  wrap w (x * (y mod 2 ^ (i + 1))) =
    if Z.testbit y i then
      wadd w (wrap w (x * (y mod 2 ^ i))) (tnum_shl_scalar_value w i x)
    else wrap w (x * (y mod 2 ^ i)).
Proof.
  intros w x y i Hi Hx. rewrite tnum_mul_prefix by lia.
  destruct (Z.testbit y i); cbn [Z.b2z].
  - unfold tnum_shl_scalar_value. rewrite Z.min_l by lia.
    rewrite <- (wmul_wshl w x i Hx Hi).
    rewrite wadd_value, wmul_value, <- wrap_add. f_equal. ring.
  - f_equal. ring.
Qed.

Lemma tnum_mul_step_sound : forall w a b x y i r,
  0 <= i < Zpos w -> is_word w x -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w r (wrap w (x * (y mod 2 ^ i))) ->
  match Cost.value (tnum_mul_step_c w a b (i, r)) with
  | inl (j, q) => j = i + 1 /\ tnum_gamma w q (wrap w (x * (y mod 2 ^ (i + 1))))
  | inr _ => False
  end.
Proof.
  intros w a b x y i r Hi Hx Ha Hb Hr.
  pose proof (tnum_shl_scalar_sound w i a x ltac:(lia) Hx Ha) as Hshift.
  pose proof (tnum_add_sound w r _ _ _ Hr Hshift) as Hsum.
  apply tnum_gamma_bits in Hb. destruct Hb as [Hz Ho].
  change (Z.succ i = i + 1 /\
    tnum_gamma w
      (if Z.testbit (zeros b) i then r else
        if Z.testbit (ones b) i then tnum_add w r (tnum_shl_scalar w i a)
        else tnum_join w r (tnum_add w r (tnum_shl_scalar w i a)))
      (wrap w (x * (y mod 2 ^ (i + 1))))).
  split; [lia|]. rewrite tnum_mul_partial_add by assumption.
  destruct (Z.testbit (zeros b) i) eqn:Hbz.
  - rewrite (Hz i Hi Hbz). exact Hr.
  - destruct (Z.testbit (ones b) i) eqn:Hbo.
    + rewrite (Ho i Hi Hbo). exact Hsum.
    + apply tnum_join_sound. destruct (Z.testbit y i); auto.
Qed.

Lemma tnum_mul_runs_index : forall w a b n s result,
  runs (tnum_mul_step_c w a b) n s result ->
  match result with
  | inl s' => fst s' = fst s + Z.of_nat n
  | inr _ => False
  end.
Proof.
  intros w a b n s result Hrun.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH].
  - cbn. lia.
  - destruct s as [i q]. discriminate Hstop.
  - destruct s as [i q], next as [j q']. injection Hnext as Hj Hq.
    cbn [fst] in Hj. destruct result as [[k q'']|r]; [|exact IH].
    cbn [fst] in *. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma tnum_mul_runs_sound : forall w a b x y,
  is_word w x -> tnum_gamma w a x -> tnum_gamma w b y ->
  forall n s result, runs (tnum_mul_step_c w a b) n s result ->
  0 <= fst s -> fst s + Z.of_nat n <= Zpos w ->
  tnum_gamma w (snd s) (wrap w (x * (y mod 2 ^ fst s))) ->
  match result with
  | inl s' => tnum_gamma w (snd s') (wrap w (x * (y mod 2 ^ fst s')))
  | inr _ => False
  end.
Proof.
  intros w a b x y Hx Ha Hb n s result Hrun.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH];
    intros Hnonneg Hbound Hgamma.
  - exact Hgamma.
  - destruct s as [i q]. discriminate Hstop.
  - destruct s as [i q], next as [j q']. cbn [fst snd] in *.
    pose proof (tnum_mul_step_sound w a b x y i q ltac:(lia) Hx Ha Hb Hgamma) as Hstep.
    rewrite Hnext in Hstep. cbn [fst snd] in Hstep. destruct Hstep as [Hj Hq].
    apply IH; rewrite ?Hj; try lia.
    exact Hq.
Qed.

(** Staged multiplication contains every concrete word product, including empty-mask rejection. *)
Theorem tnum_mul_stages_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_stages w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_mul_stages, tnum_mul_stages_c.
  rewrite (tnum_empty_sound w a x Ha), (tnum_empty_sound w b y Hb).
  cbn [orb]. autorewrite with galois_cost.
  pose proof (iterate_value (tnum_mul_step_c w a b) w (0, tnum_const w 0)) as Hrun.
  pose proof (tnum_mul_runs_index w a b _ _ _ Hrun) as Hindex.
  assert (Hzero : tnum_gamma w (tnum_const w 0) (wrap w (x * (y mod 2 ^ 0)))).
  { rewrite Z.pow_0_r, Z.mod_1_r, Z.mul_0_r. apply tnum_const_sound. }
  pose proof (tnum_mul_runs_sound w a b x y Hx Ha Hb _ _ _ Hrun
    ltac:(cbn; lia) ltac:(cbn; rewrite positive_nat_Z; lia) Hzero) as Hsound.
  destruct (Cost.value (iterate (tnum_mul_step_c w a b) w (0, tnum_const w 0)))
    as [[i r]|r]; [|contradiction].
  cbn [fst snd] in Hindex, Hsound |- *.
  rewrite positive_nat_Z, Z.add_0_l in Hindex. subst i.
  rewrite <- modulus_value, (Z.mod_small y (modulus w) Hy) in Hsound.
  rewrite wmul_value. exact Hsound.
Qed.

(** Stage count reads the processed-bit index of the actual costed driver. *)
Definition tnum_mul_stage_count (w : width) (a b : tnum) : Z :=
  match Cost.value (iterate (tnum_mul_step_c w a b) w (0, tnum_const w 0)) with
  | inl s => fst s
  | inr _ => 0
  end.

(** There are at most width-many stages, each of which performs at most one addition. *)
Theorem tnum_mul_stage_bound : forall w a b, 0 <= tnum_mul_stage_count w a b <= Zpos w.
Proof.
  intros w a b. unfold tnum_mul_stage_count.
  pose proof (iterate_value (tnum_mul_step_c w a b) w (0, tnum_const w 0)) as Hrun.
  pose proof (tnum_mul_runs_index w a b _ _ _ Hrun) as Hindex.
  destruct (Cost.value (iterate (tnum_mul_step_c w a b) w (0, tnum_const w 0)))
    as [[i r]|r]; [|contradiction].
  cbn [fst] in Hindex |- *. rewrite positive_nat_Z in Hindex. lia.
Qed.

(** A zero-value cube permits precisely the bits selected by its uncertainty mask. *)
Definition tnum_uncertain (w : width) (m : Z) : tnum := Tnum (wnot w m) 0.

Lemma tnum_uncertain_sound : forall w m x,
  Z.land x m = x -> tnum_gamma w (tnum_uncertain w m) x.
Proof.
  intros w m x Hsub. apply tnum_gamma_bits. split; intros i Hi Hbit.
  - change (Z.testbit (wnot w m) i = true) in Hbit.
    rewrite tnum_not_bit in Hbit by exact Hi. apply negb_true_iff in Hbit.
    apply (f_equal (fun z => Z.testbit z i)) in Hsub.
    rewrite Z.land_spec, Hbit, andb_false_r in Hsub. now symmetry.
  - change (Z.testbit 0 i = true) in Hbit. now rewrite Z.bits_0 in Hbit.
Qed.

Lemma tnum_uncertain_zero : forall w m, tnum_gamma w (tnum_uncertain w m) 0.
Proof.
  intros w m. apply tnum_uncertain_sound. apply Z.land_0_l.
Qed.

Lemma tnum_uncertain_value : forall w a x,
  tnum_gamma w a x ->
  tnum_gamma w (tnum_uncertain w (wor w (tnum_min w a) (tnum_mask w a))) x.
Proof.
  intros w a x Ha. apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
  apply tnum_gamma_bits. split; intros i Hi Hbit.
  2: { change (Z.testbit 0 i = true) in Hbit. now rewrite Z.bits_0 in Hbit. }
  change (Z.testbit (wnot w (wor w (tnum_min w a) (tnum_mask w a))) i = true) in Hbit.
  rewrite tnum_not_bit, tnum_or_bit, tnum_mask_bit in Hbit by exact Hi.
  unfold tnum_min in Hbit. rewrite tnum_wrap_bit in Hbit by exact Hi.
  specialize (Hz i Hi). specialize (Ho i Hi).
  destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
    cbn in *; intuition discriminate.
Qed.

(** The mask accumulator covers the product prefix minus the known-value product prefix. *)
Definition tnum_mul_residual (w : width) (a b : tnum) (x y i : Z) : Z :=
  x * (y mod 2 ^ i) - tnum_min w a * (tnum_min w b mod 2 ^ i).

Lemma tnum_mul_residual_step : forall w a b x y i,
  0 <= i < Zpos w ->
  tnum_mul_residual w a b x y (i + 1) =
    tnum_mul_residual w a b x y i +
      (x * Z.b2z (Z.testbit y i) -
        tnum_min w a * Z.b2z (Z.testbit (ones b) i)) * 2 ^ i.
Proof.
  intros w a b x y i Hi. unfold tnum_mul_residual.
  rewrite !tnum_mul_prefix by lia.
  assert (Hbit : Z.testbit (tnum_min w b) i = Z.testbit (ones b) i)
    by (apply tnum_wrap_bit; exact Hi).
  rewrite Hbit. ring.
Qed.

Definition tnum_mul_acc_done (w : width) (b : tnum) (i : Z) : bool :=
  (Z.shiftr (tnum_min w b) i =? 0) && (Z.shiftr (tnum_mask w b) i =? 0).

Lemma tnum_shift_clear : forall z i j,
  0 <= i -> i <= j -> Z.shiftr z i = 0 -> Z.testbit z j = false.
Proof.
  intros z i j Hi Hj Hzero.
  apply (f_equal (fun x => Z.testbit x (j - i))) in Hzero.
  rewrite Z.shiftr_spec, Z.bits_0 in Hzero by lia.
  now replace (j - i + i) with j in Hzero by ring.
Qed.

Lemma tnum_low_complete : forall z i,
  0 <= i -> (forall j, i <= j -> Z.testbit z j = false) -> z mod 2 ^ i = z.
Proof.
  intros z i Hi Hhigh. apply Z.bits_inj'. intros j Hj.
  destruct (Z_lt_ge_dec j i) as [Hlow|Hge].
  - now rewrite Z.mod_pow2_bits_low.
  - rewrite Z.mod_pow2_bits_high by lia. symmetry. apply Hhigh. lia.
Qed.

Lemma tnum_mul_acc_done_sound : forall w b y i,
  is_word w y -> tnum_gamma w b y -> 0 <= i ->
  tnum_mul_acc_done w b i = true ->
  y mod 2 ^ i = y /\ tnum_min w b mod 2 ^ i = tnum_min w b.
Proof.
  intros w b y i Hy Hb Hi Hdone. unfold tnum_mul_acc_done in Hdone.
  apply andb_true_iff in Hdone as [Hv Hm]. apply Z.eqb_eq in Hv, Hm.
  apply tnum_gamma_bits in Hb. destruct Hb as [Hz Ho]. split; apply tnum_low_complete;
    try exact Hi.
  - intros j Hj. destruct (Z_lt_ge_dec j (Zpos w)) as [Hlow|Hhigh].
    + pose proof (tnum_shift_clear _ i j Hi Hj Hv) as Hvbit.
      pose proof (tnum_shift_clear _ i j Hi Hj Hm) as Hmbit.
      unfold tnum_min in Hvbit. rewrite tnum_wrap_bit in Hvbit by lia.
      rewrite tnum_mask_bit in Hmbit by lia.
      specialize (Hz j ltac:(lia)). specialize (Ho j ltac:(lia)).
      destruct (Z.testbit (zeros b) j), (Z.testbit (ones b) j), (Z.testbit y j);
        cbn in *; intuition discriminate.
    + apply (word_bits_high w y j Hy). lia.
  - intros j Hj. now apply (tnum_shift_clear _ i j Hi Hj Hv).
Qed.

(** The accumulator uses the multiplier value and mask as its stopping condition.
    Known multiplier bits add the shifted multiplicand mask.
    Unknown multiplier bits add the shifted union of multiplicand value and mask. *)
Definition tnum_mul_acc_step_c (w : width) (a b : tnum) (s : Z * tnum)
    : Cost.t ((Z * tnum) + tnum) :=
  let '(i, r) := s in
  Cost.step ;;
  if tnum_mul_acc_done w b i then Cost.ret (inr r) else
  Cost.ret (inl (i + 1,
    if Z.testbit (zeros b) i then r else
    let m := if Z.testbit (ones b) i then tnum_mask w a
      else wor w (tnum_min w a) (tnum_mask w a) in
    tnum_add w r (tnum_shl_scalar w i (tnum_uncertain w m)))).

Lemma tnum_mul_acc_increment : forall w a b x y i r q delta,
  0 <= i < Zpos w -> is_word w delta ->
  tnum_gamma w r (wrap w (tnum_mul_residual w a b x y i)) ->
  tnum_gamma w q delta ->
  tnum_gamma w (tnum_add w r (tnum_shl_scalar w i q))
    (wrap w (tnum_mul_residual w a b x y i + delta * 2 ^ i)).
Proof.
  intros w a b x y i r q delta Hi Hdelta Hr Hq.
  pose proof (tnum_add_sound w r (tnum_shl_scalar w i q) _ _
    Hr (tnum_shl_scalar_sound w i q delta ltac:(lia) Hdelta Hq)) as Hsum.
  unfold tnum_shl_scalar_value in Hsum. rewrite Z.min_l in Hsum by lia.
  rewrite <- (wmul_wshl w delta i Hdelta Hi), wadd_value, wmul_value,
    <- wrap_add in Hsum. exact Hsum.
Qed.

Lemma tnum_mul_acc_next : forall w a b x y i r,
  0 <= i < Zpos w -> is_word w x -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w r (wrap w (tnum_mul_residual w a b x y i)) ->
  tnum_gamma w
    (if Z.testbit (zeros b) i then r else
      let m := if Z.testbit (ones b) i then tnum_mask w a
        else wor w (tnum_min w a) (tnum_mask w a) in
      tnum_add w r (tnum_shl_scalar w i (tnum_uncertain w m)))
    (wrap w (tnum_mul_residual w a b x y (i + 1))).
Proof.
  intros w a b x y i r Hi Hx Ha Hb Hr.
  destruct (tnum_decompose w a x Hx Ha) as [c [Hsub Hxc]].
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hbounds.
  pose proof (wrap_is_word w (ones a)) as Hvalue.
  apply tnum_gamma_bits in Hb. destruct Hb as [Hz Ho].
  rewrite tnum_mul_residual_step by exact Hi.
  destruct (Z.testbit (zeros b) i) eqn:Hbz.
  - rewrite (Hz i Hi Hbz).
    assert (Hbo : Z.testbit (ones b) i = false).
    { destruct (Z.testbit (ones b) i) eqn:Hbo; [|reflexivity].
      specialize (Ho i Hi Hbo). specialize (Hz i Hi Hbz). congruence. }
    rewrite Hbo. cbn [Z.b2z]. replace (_ + (x * 0 - _ * 0) * _) with
      (tnum_mul_residual w a b x y i) by ring. exact Hr.
  - destruct (Z.testbit (ones b) i) eqn:Hbo.
    + rewrite (Ho i Hi Hbo). cbn [Z.b2z].
      replace (x * 1 - tnum_min w a * 1) with c by lia.
      apply tnum_mul_acc_increment; try assumption.
      * change (0 <= tnum_min w a < modulus w) in Hvalue.
        unfold is_word in *. lia.
      * now apply tnum_uncertain_sound.
    + cbn [Z.b2z]. destruct (Z.testbit y i).
      * cbn [Z.b2z]. replace (x * 1 - tnum_min w a * 0) with x by ring.
        apply tnum_mul_acc_increment; try assumption. now apply tnum_uncertain_value.
      * cbn [Z.b2z]. replace (x * 0 - tnum_min w a * 0) with 0 by ring.
        apply tnum_mul_acc_increment; try assumption.
        -- apply zero_is_word.
        -- apply tnum_uncertain_zero.
Qed.

(** Prefix induction proves the accumulator independently of the staged multiplier. *)
Theorem tnum_mul_acc_runs_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  forall n s result, runs (tnum_mul_acc_step_c w a b) n s result ->
  0 <= fst s -> fst s + Z.of_nat n <= Zpos w ->
  tnum_gamma w (snd s) (wrap w (tnum_mul_residual w a b x y (fst s))) ->
  match result with
  | inl s' =>
    fst s' = fst s + Z.of_nat n /\
    tnum_gamma w (snd s') (wrap w (tnum_mul_residual w a b x y (fst s')))
  | inr r =>
    tnum_gamma w r (wrap w (x * y - tnum_min w a * tnum_min w b))
  end.
Proof.
  intros w a b x y Hx Hy Ha Hb n s result Hrun.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH];
    intros Hi Hbound Hr.
  - cbn. split; [lia|exact Hr].
  - destruct s as [i q]. cbn [fst snd] in *.
    cbn [tnum_mul_acc_step_c] in Hstop. autorewrite with galois_cost in Hstop.
    destruct (tnum_mul_acc_done w b i) eqn:Hdone; [|discriminate].
    injection Hstop as <-.
    destruct (tnum_mul_acc_done_sound w b y i Hy Hb Hi Hdone) as [Hlow Hvlow].
    unfold tnum_mul_residual in Hr. now rewrite Hlow, Hvlow in Hr.
  - destruct s as [i q], next as [j q']. cbn [fst snd] in *.
    cbn [tnum_mul_acc_step_c] in Hnext. autorewrite with galois_cost in Hnext.
    destruct (tnum_mul_acc_done w b i) eqn:Hdone; [discriminate|].
    injection Hnext as Hj Hq. subst j q'.
    specialize (IH ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hbound; lia)
      (tnum_mul_acc_next w a b x y i q ltac:(rewrite Nat2Z.inj_succ in Hbound; lia)
        Hx Ha Hb Hr)).
    destruct result as [[k q'']|r]; [|exact IH]. cbn [fst snd] in *.
    destruct IH as [Hk Hgamma]. split; [rewrite Nat2Z.inj_succ; lia|exact Hgamma].
Qed.

(** The Listing-4-style implementation initializes a value product and a zero mask accumulator.
    It adds the mask accumulator to that product once after processing active multiplier bits. *)
Definition tnum_mul_acc_c (w : width) (a b : tnum) : Cost.t tnum :=
  if tnum_empty w a || tnum_empty w b then Cost.ret (bot (tnum_lattice w)) else
  let value_acc := tnum_const w (wmul w (tnum_min w a) (tnum_min w b)) in
  let* result := iterate (tnum_mul_acc_step_c w a b) w (0, tnum_const w 0) in
  let mask_acc :=
    match result with
    | inl s => snd s
    | inr r => r
    end in
  Cost.ret (tnum_add w value_acc mask_acc).

Definition tnum_mul_acc (w : width) (a b : tnum) : tnum :=
  Cost.value (tnum_mul_acc_c w a b).

(** The independently accumulated uncertainty contains every residual concrete product. *)
Theorem tnum_mul_acc_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_acc w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb.
  pose proof (iterate_value (tnum_mul_acc_step_c w a b) w (0, tnum_const w 0)) as Hrun.
  assert (Hzero : tnum_gamma w (tnum_const w 0)
    (wrap w (tnum_mul_residual w a b x y 0))).
  { unfold tnum_mul_residual. rewrite !Z.mod_1_r, !Z.mul_0_r, Z.sub_0_r.
    apply tnum_const_sound. }
  pose proof (tnum_mul_acc_runs_sound w a b x y Hx Hy Ha Hb _ _ _ Hrun
    ltac:(cbn; lia) ltac:(cbn; rewrite positive_nat_Z; lia) Hzero) as Hsound.
  unfold tnum_mul_acc, tnum_mul_acc_c.
  rewrite (tnum_empty_sound w a x Ha), (tnum_empty_sound w b y Hb).
  cbn [orb]. autorewrite with galois_cost.
  assert (Hmask : tnum_gamma w
    (match Cost.value (iterate (tnum_mul_acc_step_c w a b) w (0, tnum_const w 0)) with
     | inl s => snd s
     | inr r => r
     end) (wrap w (x * y - tnum_min w a * tnum_min w b))).
  { destruct (Cost.value (iterate (tnum_mul_acc_step_c w a b) w (0, tnum_const w 0)))
      as [[i r]|r]; [|exact Hsound].
    cbn [fst snd] in Hsound |- *. destruct Hsound as [Hi Hgamma].
    rewrite positive_nat_Z, Z.add_0_l in Hi. subst i.
    unfold tnum_mul_residual in Hgamma. rewrite <- modulus_value,
      (Z.mod_small y (modulus w) Hy),
      (Z.mod_small (tnum_min w b) (modulus w) (wrap_is_word w _)) in Hgamma.
    exact Hgamma. }
  pose proof (tnum_add_sound w
    (tnum_const w (wmul w (tnum_min w a) (tnum_min w b))) _ _ _
    (tnum_const_sound w (wmul w (tnum_min w a) (tnum_min w b))) Hmask) as Hsum.
  rewrite wadd_value, wmul_value, wrap_wrap, <- wrap_add in Hsum.
  replace (tnum_min w a * tnum_min w b +
    (x * y - tnum_min w a * tnum_min w b)) with (x * y) in Hsum by ring.
  rewrite wmul_value. exact Hsum.
Qed.

(** Multiplier policy is executable data and requires no semantic proof to run. *)
Inductive tnum_mul_choice : Type :=
  | MulLow
  | MulStages
  | MulAcc
  | MulBoth.

Definition tnum_mul_with_c (choice : tnum_mul_choice) (w : width) (a b : tnum)
    : Cost.t tnum :=
  match choice with
  | MulLow => Cost.step ;; Cost.ret (tnum_mul w a b)
  | MulStages => tnum_mul_stages_c w a b
  | MulAcc => tnum_mul_acc_c w a b
  | MulBoth =>
    let* stages := tnum_mul_stages_c w a b in
    let* acc := tnum_mul_acc_c w a b in
    Cost.ret (tnum_meet w stages acc)
  end.

Definition tnum_mul_with (choice : tnum_mul_choice) (w : width) (a b : tnum) : tnum :=
  Cost.value (tnum_mul_with_c choice w a b).

(** Every multiplier choice contains every concrete word product. *)
Theorem tnum_mul_with_sound : forall choice w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_with choice w a b) (wmul w x y).
Proof.
  intros choice w a b x y Hx Hy Ha Hb. destruct choice.
  - apply tnum_mul_sound; assumption.
  - apply tnum_mul_stages_sound; assumption.
  - apply tnum_mul_acc_sound; assumption.
  - unfold tnum_mul_with, tnum_mul_with_c. autorewrite with galois_cost.
    apply tnum_meet_sound.
    + now apply tnum_mul_stages_sound.
    + now apply tnum_mul_acc_sound.
Qed.

(** Meeting the two multipliers denotes their intersection for arbitrary masks. *)
Theorem tnum_mul_both_gamma : forall w a b z,
  tnum_gamma w (tnum_mul_with MulBoth w a b) z <->
  tnum_gamma w (tnum_mul_with MulStages w a b) z /\
    tnum_gamma w (tnum_mul_with MulAcc w a b) z.
Proof.
  intros w a b z. unfold tnum_mul_with, tnum_mul_with_c.
  autorewrite with galois_cost. apply tnum_meet_gamma.
Qed.
