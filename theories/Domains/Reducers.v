(** * Value reducers

    Reducers exchange facts between abstractions of the same concrete word.
    For example, a known-bit payload can refine an interval endpoint.

    Main results
    - [left_sound] The first exchange retains every value shared by the input pair.
    - [right_sound] The second exchange retains every value shared by the input pair.
    - [reduce_complexity] Reduction has the published combined-size asymptotic budget,
      O(A.size a + B.size b + 1).

    Builds on: ReducersSig and Tagged. *)

From Stdlib Require Import NArith ZArith Zpow_facts Lia Bool.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Bits Require Import Word Testbit.
From Galois.Domains Require Import ValueSig BitsLang WordSig KnownBitsSig WrappedSig
  IntervalSig CongruenceSig ThresholdsSig ReducersSig Tagged.
Import ComplexityNotations.

Local Open Scope Z_scope.

(** The reducer mask is the usual unsigned word normalization. *)
Lemma reducer_tnum_wrap : forall w z, tnum_wrap w z = Word.wrap w z.
Proof.
  intros w z. symmetry. rewrite Word.wrap_mod. unfold tnum_wrap, Word.modulus.
  symmetry. apply Z.land_ones. lia.
Qed.

(** Complementing a normalized zero mask leaves an unsigned upper endpoint. *)
Lemma reducer_bits_upper_word : forall w b,
  Word.is_word w (Z.lxor (tnum_wrap w (zeros b)) (Z.ones (Zpos w))).
Proof.
  intros w b; rewrite reducer_tnum_wrap.
  apply word_of_bits; intros i Hi.
  rewrite Z.lxor_spec, (word_bits_high w _ i (wrap_is_word w _) Hi).
  rewrite Z.ones_spec_high by lia; reflexivity.
Qed.

(** Every represented word lies between the two known-bit hull endpoints. *)
Lemma reducer_bits_bounds : forall w b z,
  Word.is_word w z -> Z.land z (Word.wrap w (zeros b)) = 0 ->
  Z.land (Word.wrap w (ones b)) (Z.lnot z) = 0 ->
  tnum_wrap w (ones b) <= z <= Z.lxor (tnum_wrap w (zeros b)) (Z.ones (Zpos w)).
Proof.
  intros w b z Hword Hzero Hone; rewrite !reducer_tnum_wrap.
  split.
  - enough (Hdiff : Z.ldiff (Word.wrap w (ones b)) z = 0).
    { exact (proj2 (Z.ldiff_le _ _ (proj1 Hword) Hdiff)). }
    rewrite Z.ldiff_land; exact Hone.
  - pose proof (reducer_bits_upper_word w b) as Hupper.
    rewrite reducer_tnum_wrap in Hupper.
    enough (Hdiff : Z.ldiff z (Z.lxor (Word.wrap w (zeros b)) (Z.ones (Zpos w))) = 0).
    { exact (proj2 (Z.ldiff_le _ _ (proj1 Hupper) Hdiff)). }
    apply Z.bits_inj'; intros i Hi.
    rewrite Z.ldiff_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
    + rewrite Z.ones_spec_low by lia.
      rewrite xorb_true_r, negb_involutive.
      pose proof (f_equal (fun v => Z.testbit v i) Hzero) as Hbit.
      cbn beta in Hbit.
      rewrite Z.land_spec, Z.bits_0 in Hbit; exact Hbit.
    + rewrite (word_bits_high w z i Hword ltac:(lia)); reflexivity.
Qed.

(** Clipping a raw interval retains each normalized word that it contains. *)
Lemma reducer_clip_sound : forall w a z,
  Word.is_word w z ->
  (match a with IBot => False | I lo hi => in_bnd lo hi z end) ->
  match interval_word_clip w a with IBot => False | I lo hi => in_bnd lo hi z end.
Proof.
  intros w [|[|lo|] [|hi|]] z Hword Hin;
    cbn [in_bnd] in Hin; try tauto.
  all: unfold Word.is_word, Word.modulus in Hword.
  all: unfold interval_word_clip; rewrite ?Z.ones_equiv.
  all: try match goal with
    | |- context [if Z.leb ?l ?h then _ else _] => destruct (Z.leb l h) eqn:Hclip
    end; cbn [in_bnd].
  all: try unfold in_bnd in *.
  all: try apply Z.leb_gt in Hclip; lia.
Qed.

(** A successful clipped interval has ordered word-valued endpoints. *)
Lemma reducer_clip_bounds : forall w a lo hi,
  interval_word_clip w a = I (Fin lo) (Fin hi) ->
  0 <= lo <= hi /\ hi < Word.modulus w.
Proof.
  intros w [|[|l|] [|h|]] lo hi Hclip; unfold interval_word_clip in Hclip;
    try discriminate.
  all: try match type of Hclip with
    | context [if Z.leb ?l ?h then _ else _] => destruct (Z.leb l h) eqn:Horder
    end; try discriminate.
  all: inversion Hclip; subst; apply Z.leb_le in Horder;
    rewrite Z.ones_equiv in *; unfold Word.modulus; lia.
Qed.

(** Inward residue rounding retains every member of the residue class. *)
Lemma reducer_residue_round : forall m r lo hi z,
  m <> 0 -> lo <= z <= hi -> (m | z - r) ->
  lo + (r - lo) mod Z.abs m <= z <= hi - (hi - r) mod Z.abs m.
Proof.
  intros m r lo hi z Hnonzero Hbounds Hdiv.
  assert (Hpositive : 0 < Z.abs m) by (apply Z.abs_pos; exact Hnonzero).
  apply Z.divide_abs_l in Hdiv; destruct Hdiv as [q Hq].
  assert (Hlower : (r - lo) mod Z.abs m = (z - lo) mod Z.abs m).
  { replace (z - lo) with ((r - lo) + q * Z.abs m) by lia.
    rewrite Z.mod_add by lia; reflexivity. }
  assert (Hupper : (hi - r) mod Z.abs m = (hi - z) mod Z.abs m).
  { replace (hi - r) with ((hi - z) + q * Z.abs m) by lia.
    rewrite Z.mod_add by lia; reflexivity. }
  rewrite Hlower, Hupper.
  pose proof (Z.mod_le (z - lo) (Z.abs m) ltac:(lia) Hpositive).
  pose proof (Z.mod_le (hi - z) (Z.abs m) ltac:(lia) Hpositive).
  lia.
Qed.

(** Equal high parts of interval endpoints fix every intermediate high bit. *)
Lemma reducer_prefix_agrees : forall lo hi z i,
  0 <= lo -> lo <= z <= hi ->
  Z.log2 (Z.lxor lo hi) + 1 <= i ->
  Z.testbit z i = Z.testbit lo i.
Proof.
  intros lo hi z i Hlo Hbounds Hi.
  set (k := Z.log2 (Z.lxor lo hi) + 1).
  assert (Hk : 0 <= k) by (unfold k; pose proof (Z.log2_nonneg (Z.lxor lo hi)); lia).
  assert (Hend : Z.shiftr lo k = Z.shiftr hi k).
  { apply Z.lxor_eq; rewrite <- Z.shiftr_lxor.
    apply Z.shiftr_eq_0.
    - apply Z.lxor_nonneg; lia.
    - unfold k; lia. }
  assert (Hmid : Z.shiftr z k = Z.shiftr lo k).
  { rewrite !Z.shiftr_div_pow2 in * by exact Hk.
    assert (Hpow : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_le_mono lo z (2 ^ k) Hpow (proj1 Hbounds)).
    pose proof (Z.div_le_mono z hi (2 ^ k) Hpow (proj2 Hbounds)).
    lia. }
  pose proof (f_equal (fun v => Z.testbit v (i - k)) Hmid) as Hbit.
  cbn beta in Hbit.
  rewrite !Z.shiftr_spec in Hbit by (unfold k; lia).
  replace (i - k + k) with i in Hbit by lia; exact Hbit.
Qed.

(** The common prefix masks retain every integer between their endpoints. *)
Lemma reducer_prefix_masks : forall w lo hi z,
  0 <= lo -> lo <= z <= hi ->
  let m := Z.ones (Z.log2 (Z.lxor lo hi) + 1) in
  Z.land z (Word.wrap w (Z.land (Z.lnot (Z.lor lo m)) (Z.ones (Zpos w)))) = 0 /\
  Z.land (Word.wrap w (Z.land lo (Z.lnot m))) (Z.lnot z) = 0.
Proof.
  intros w lo hi z Hlo Hbounds; cbv zeta.
  set (k := Z.log2 (Z.lxor lo hi) + 1).
  assert (Hk : 0 <= k) by (unfold k; pose proof (Z.log2_nonneg (Z.lxor lo hi)); lia).
  split; apply Z.bits_inj'; intros i Hi;
    rewrite Z.land_spec, testbit_wrap, Z.bits_0 by exact Hi;
    destruct (i <? Zpos w) eqn:Hwidth;
    rewrite ?andb_true_l, ?andb_false_l, ?andb_false_r; try reflexivity.
  all: apply Z.ltb_lt in Hwidth.
  all: rewrite !Z.land_spec, !Z.lnot_spec, ?Z.lor_spec by lia.
  all: destruct (Z_lt_ge_dec i k) as [Hlow|Hhigh].
  all: try (rewrite !Z.ones_spec_low by lia;
    destruct (Z.testbit z i), (Z.testbit lo i); reflexivity).
  all: rewrite (Z.ones_spec_high k i) by lia.
  all: try rewrite (Z.ones_spec_low (Zpos w) i) by lia.
  all: rewrite (reducer_prefix_agrees lo hi z i Hlo Hbounds ltac:(unfold k in *; lia)).
  all: destruct (Z.testbit lo i); reflexivity.
Qed.

(** A nonwrapping normalized arc uses the ordinary interval between its endpoints. *)
Lemma reducer_arc_bounds : forall w lo hi z,
  Word.is_word w z -> tnum_wrap w lo <= tnum_wrap w hi ->
  (z - lo) mod Word.modulus w <= (hi - lo) mod Word.modulus w ->
  tnum_wrap w lo <= z <= tnum_wrap w hi.
Proof.
  intros w lo hi z Hword Horder Harc.
  rewrite (reducer_tnum_wrap w lo), (reducer_tnum_wrap w hi) in *.
  pose proof (Word.wrap_is_word w lo) as Hlo.
  pose proof (Word.wrap_is_word w hi) as Hhi.
  pose proof (Word.modulus_pos w) as Hpositive.
  rewrite (Zminus_mod z lo (Word.modulus w)),
    (Zminus_mod hi lo (Word.modulus w)) in Harc.
  rewrite <- (Word.wrap_mod w z), <- (Word.wrap_mod w lo), <- (Word.wrap_mod w hi) in Harc.
  rewrite (Word.wrap_id w z Hword) in Harc.
  assert (Hend : (Word.wrap w hi - Word.wrap w lo) mod Word.modulus w =
    Word.wrap w hi - Word.wrap w lo) by (apply Z.mod_small; unfold Word.is_word in *; lia).
  rewrite Hend in Harc.
  destruct (Z_le_dec (Word.wrap w lo) z) as [Hafter|Hbefore].
  - rewrite Z.mod_small in Harc by (unfold Word.is_word in *; lia); lia.
  - assert (Hback : (z - Word.wrap w lo) mod Word.modulus w =
      z - Word.wrap w lo + Word.modulus w).
    { symmetry; apply Z.mod_unique with (q := -1).
      - left; unfold Word.is_word in *; lia.
      - lia. }
    rewrite Hback in Harc; unfold Word.is_word in *; lia.
Qed.

(** Common-prefix extraction retains every member of the source arc. *)
Lemma reducer_arc_prefix_sound : forall w a z,
  Word.is_word w z ->
  (match a with
   | WBot => False
   | WFull => True
   | WItv lo hi => (z - lo) mod Word.modulus w <= (hi - lo) mod Word.modulus w
   end) ->
  Z.land z (Word.wrap w (zeros (arc_prefix w a))) = 0 /\
  Z.land (Word.wrap w (ones (arc_prefix w a))) (Z.lnot z) = 0.
Proof.
  intros w [| |lo hi] z Hword Harc; [contradiction| |].
  - change (Z.land z (Word.wrap w 0) = 0 /\ Z.land (Word.wrap w 0) (Z.lnot z) = 0).
    rewrite Word.wrap_0, Z.land_0_r, Z.land_0_l; split; reflexivity.
  - unfold arc_prefix.
    destruct (Z.leb (tnum_wrap w lo) (tnum_wrap w hi)) eqn:Horder.
    + cbn [zeros ones].
      apply reducer_prefix_masks.
      * rewrite reducer_tnum_wrap; apply (proj1 (Word.wrap_is_word w lo)).
      * apply reducer_arc_bounds; [exact Hword|now apply Z.leb_le|exact Harc].
    + change (Z.land z (Word.wrap w 0) = 0 /\ Z.land (Word.wrap w 0) (Z.lnot z) = 0).
      rewrite Word.wrap_0, Z.land_0_r, Z.land_0_l; split; reflexivity.
Qed.

(** The counter potential pays for carries while a bit count is incremented. *)
Fixpoint reducer_counter_ones (p : positive) : N :=
  match p with
  | xH => 1%N
  | xO q => reducer_counter_ones q
  | xI q => (1 + reducer_counter_ones q)%N
  end.

(** Binary increment has constant amortized cost under the one-bit potential. *)
Lemma reducer_succ_credit : forall p,
  (Std.Pos.T_succ p + reducer_counter_ones (Pos.succ p) <=
    2 + reducer_counter_ones p)%N.
Proof.
  induction p as [p IH|p IH|]; time_unfold Std.Pos.T_succ; time_cbn; lia.
Qed.

(** Computing a positive bit count makes only linearly many amortized increments. *)
Lemma reducer_size_credit : forall p,
  (Fun.Pos.T_size p + reducer_counter_ones (Pos.size p) <=
    3 * N.of_nat (Pos.size_nat p))%N.
Proof.
  induction p as [p IH|p IH|]; time_unfold Fun.Pos.T_size; time_cbn.
  all: try pose proof (reducer_succ_credit (Pos.size p)) as Hsucc.
  all: lia.
Qed.

(** Integer logarithm scans its input bits with a binary counter. *)
Lemma reducer_log2_time : forall z,
  (Fun.Z.T_log2 z <= 4 * N.of_nat (Z.size_nat z + 1))%N.
Proof.
  intros [|[p|p|]|p]; time_unfold Fun.Z.T_log2; time_cbn.
  all: try pose proof (reducer_size_credit p) as Hsize.
  all: rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ; lia.
Qed.

(** Unsigned word membership bounds the stored integer bits. *)
Lemma reducer_word_bits : forall w z, Word.is_word w z ->
  (Z.size_nat z <= Pos.to_nat w)%nat.
Proof.
  intros w [|z|z] Hword; unfold Word.is_word, Word.modulus in Hword;
    cbn [Z.size_nat]; try lia.
  apply Zpower2_Psize; rewrite positive_nat_Z; exact (proj2 Hword).
Qed.

(** Positive bit counts fit within the value of the positive integer. *)
Lemma reducer_positive_bits : forall p, (Pos.size_nat p <= Pos.to_nat p)%nat.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.size_nat];
    rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
Qed.

(** A nonnegative integer has no more bits than its value. *)
Lemma reducer_nonnegative_bits : forall z, 0 <= z -> (Z.size_nat z <= Z.to_nat z)%nat.
Proof.
  intros [|p|p] Hnonnegative; cbn [Z.size_nat Z.to_nat]; try lia.
  apply reducer_positive_bits.
Qed.

(** A word's common-prefix cutoff is a positive index no greater than its width. *)
Lemma reducer_log2_width : forall w z, Word.is_word w z ->
  0 <= Z.log2 z + 1 <= Zpos w.
Proof.
  intros w z Hword; pose proof (Z.log2_nonneg z).
  destruct (Z.eq_dec z 0) as [->|Hnonzero]; [cbn [Z.log2]; lia|].
  unfold Word.is_word, Word.modulus in Hword.
  destruct Hword as [Hnonnegative Hupper].
  apply Z.log2_lt_pow2 in Hupper as Hlog; [lia|lia].
Qed.

(** The magnitude bit count is unchanged by negation. *)
Lemma reducer_opp_bits : forall z, Z.size_nat (- z) = Z.size_nat z.
Proof.
  intros []; reflexivity.
Qed.

(** Absolute value preserves the stored magnitude bits. *)
Lemma reducer_abs_bits : forall z, Z.size_nat (Z.abs z) = Z.size_nat z.
Proof. intros []; reflexivity. Qed.

(** Every integer magnitude lies below the power of two given by its stored bits. *)
Lemma reducer_abs_bits_bound : forall z, Z.abs z < 2 ^ Z.of_nat (Z.size_nat z).
Proof.
  intros [|p|p]; cbn [Z.abs Z.size_nat]; try lia; apply Zpower2_Psize; lia.
Qed.

(** A magnitude bound gives a corresponding upper bound on stored bits. *)
Lemma reducer_bits_of_abs_bound : forall z n,
  Z.abs z < 2 ^ Z.of_nat n -> (Z.size_nat z <= n)%nat.
Proof.
  intros [|p|p] n Hbound; cbn [Z.abs Z.size_nat] in *; try lia;
    now apply Zpower2_Psize in Hbound.
Qed.

(** Addition needs at most the operand bits and one carry bit. *)
Lemma reducer_sum_bits : forall x y,
  (Z.size_nat (x + y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros x y; apply reducer_bits_of_abs_bound.
  pose proof (reducer_abs_bits_bound x) as Hx.
  pose proof (reducer_abs_bits_bound y) as Hy.
  pose proof (Z.abs_triangle x y) as Hsum.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (Z.size_nat x)) ltac:(lia) ltac:(lia)) as Hxp.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (Z.size_nat y)) ltac:(lia) ltac:(lia)) as Hyp.
  rewrite !Nat2Z.inj_add, !Z.pow_add_r, Z.pow_1_r by lia; nia.
Qed.

(** Subtraction has the same storage bound as addition. *)
Lemma reducer_sub_bits : forall x y,
  (Z.size_nat (x - y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros x y; pose proof (reducer_sum_bits x (- y)) as Hsum.
  rewrite reducer_opp_bits in Hsum; exact Hsum.
Qed.

(** A remainder modulo a nonzero magnitude fits within that magnitude's bits. *)
Lemma reducer_modulo_bits : forall x m, m <> 0 ->
  (Z.size_nat (x mod Z.abs m) <= Z.size_nat m)%nat.
Proof.
  intros x m Hm; assert (Hpositive : 0 < Z.abs m) by (apply Z.abs_pos; exact Hm).
  pose proof (Z.mod_pos_bound x (Z.abs m) Hpositive) as Hrange.
  rewrite <- (reducer_abs_bits m); apply Std.Z.size_nat_mono; lia.
Qed.

(** Two operands within a positive bit budget give a quadratic remainder clock. *)
Lemma reducer_modulo_time_budget : forall x y s,
  (Z.size_nat x <= s)%nat -> (Z.size_nat y <= s)%nat -> (1 <= s)%nat ->
  (Std.Z.T_modulo x y <= 256 * N.of_nat (s ^ 2))%N.
Proof.
  intros x y s Hx Hy Hpositive.
  pose proof (Std.Z.T_modulo_le x y) as Htime.
  rewrite Nat2N.inj_add in Htime.
  set (n := N.of_nat s).
  rewrite Nat.pow_2_r, Nat2N.inj_mul; fold n.
  assert (HxN : (N.of_nat (Z.size_nat x) <= n)%N) by (unfold n; lia).
  assert (HyN : (N.of_nat (Z.size_nat y) <= n)%N) by (unfold n; lia).
  assert (Hn : (1 <= n)%N) by (unfold n; lia).
  clearbody n.
  assert (Hproduct : ((N.of_nat (Z.size_nat x) + 1) *
    (N.of_nat (Z.size_nat x) + N.of_nat (Z.size_nat y) + 2) <= 8 * (n * n))%N).
  { replace (8 * (n * n))%N with ((2 * n) * (4 * n))%N by (clear; ring).
    apply N.mul_le_mono; lia. }
  replace (16 * (N.of_nat (Z.size_nat x) + 1) *
    (N.of_nat (Z.size_nat x) + N.of_nat (Z.size_nat y) + 2) + 1)%N with
    (16 * ((N.of_nat (Z.size_nat x) + 1) *
      (N.of_nat (Z.size_nat x) + N.of_nat (Z.size_nat y) + 2)) + 1)%N in Htime by (clear; ring).
  assert (Hsquare : (1 <= n * n)%N).
  { change (1 * 1 <= n * n)%N; apply N.mul_le_mono; exact Hn. }
  clear -Htime Hproduct Hsquare; lia.
Qed.

(** A power of two needs its exponent and one additional stored bit. *)
Lemma reducer_pow2_bits : forall n, 0 <= n ->
  (Z.size_nat (2 ^ n) <= Z.to_nat n + 1)%nat.
Proof.
  intros n Hn.
  destruct (2 ^ n) as [|p|p] eqn:Hpower; cbn [Z.size_nat]; try lia.
  - apply Zpower2_Psize.
    rewrite Nat2Z.inj_add, Z2Nat.id by exact Hn.
    rewrite <- Hpower; apply Z.pow_lt_mono_r; lia.
Qed.

(** An all-ones mask is a normalized word of the requested width. *)
Lemma reducer_ones_word : forall w, Word.is_word w (Z.ones (Zpos w)).
Proof.
  intro w; unfold Word.is_word, Word.modulus; rewrite Z.ones_equiv.
  pose proof (Word.modulus_pos w); unfold Word.modulus in *; lia.
Qed.

(** Making an all-ones mask performs linearly many bit operations. *)
Lemma reducer_ones_time : forall n, 0 <= n ->
  (Word.Z.T_ones n <= 16 * N.of_nat (Z.to_nat n + 1))%N.
Proof.
  intros n Hn.
  pose proof (Std.Z.T_shiftl_le 1 n) as Hshift.
  pose proof (Std.Z.T_pred_le (Z.shiftl 1 n)) as Hpred.
  pose proof (reducer_pow2_bits n Hn) as Hbits; rewrite <- Z.shiftl_1_l in Hbits.
  change (Std.Z.T_shiftl 1 n <= 6 * Z.abs_N n + 1)%N in Hshift.
  assert (Habs : Z.abs_N n = N.of_nat (Z.to_nat n)).
  { destruct n; cbn [Z.abs_N Z.to_nat]; try reflexivity; lia. }
  rewrite Habs in Hshift.
  time_unfold Word.Z.T_ones; rewrite Nat2N.inj_add; nia.
Qed.

(** The masked normalization clock is linear in width and raw integer bits. *)
Lemma reducer_wrap_time : forall w z,
  (T_tnum_wrap w z <= 32 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z.
  pose proof (reducer_ones_time (Zpos w) ltac:(lia)) as Hones.
  pose proof (reducer_word_bits w _ (reducer_ones_word w)) as Hbits.
  pose proof (Std.Z.T_land_le z (Z.ones (Zpos w))) as Hland.
  time_unfold T_tnum_wrap; time_cbn.
  change (Word.Z.T_ones (Zpos w) <= 16 * N.of_nat (Pos.to_nat w + 1))%N in Hones.
  rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Masked normalization produces an unsigned word. *)
Lemma reducer_wrap_word : forall w z, Word.is_word w (tnum_wrap w z).
Proof.
  intros w z; rewrite reducer_tnum_wrap; apply Word.wrap_is_word.
Qed.

(** The xor of two unsigned words has no bits beyond their shared width. *)
Lemma reducer_xor_word : forall w a b,
  Word.is_word w a -> Word.is_word w b -> Word.is_word w (Z.lxor a b).
Proof.
  intros w a b Ha Hb; apply word_of_bits; intros i Hi.
  rewrite Z.lxor_spec, (word_bits_high w a i Ha Hi), (word_bits_high w b i Hb Hi).
  reflexivity.
Qed.

(** The union of two unsigned masks remains an unsigned mask. *)
Lemma reducer_or_word : forall w a b,
  Word.is_word w a -> Word.is_word w b -> Word.is_word w (Z.lor a b).
Proof.
  intros w a b Ha Hb; apply word_of_bits; intros i Hi.
  rewrite Z.lor_spec, (word_bits_high w a i Ha Hi), (word_bits_high w b i Hb Hi).
  reflexivity.
Qed.

(** Conjunction with an unsigned mask preserves its finite width. *)
Lemma reducer_and_word : forall w a b,
  Word.is_word w a -> Word.is_word w (Z.land a b).
Proof.
  intros w a b Ha; apply word_of_bits; intros i Hi.
  rewrite Z.land_spec, (word_bits_high w a i Ha Hi); reflexivity.
Qed.

(** A prefix mask whose cutoff is below the width fits within that word. *)
Lemma reducer_mask_word : forall w n, 0 <= n <= Zpos w -> Word.is_word w (Z.ones n).
Proof.
  intros w n Hn; apply word_of_bits; intros i Hi.
  apply Z.ones_spec_high; lia.
Qed.

(** Complementing a word needs at most one additional magnitude bit. *)
Lemma reducer_complement_bits : forall w z, Word.is_word w z ->
  (Z.size_nat (Z.lnot z) <= Pos.to_nat w + 1)%nat.
Proof.
  intros w z Hword.
  replace (Z.lnot z) with (- (z + 1)) by (unfold Z.lnot; lia).
  rewrite reducer_opp_bits.
  pose proof (reducer_pow2_bits (Zpos w) ltac:(lia)) as Hpower.
  eapply Nat.le_trans; [apply Std.Z.size_nat_mono|exact Hpower].
  unfold Word.is_word, Word.modulus in Hword; lia.
Qed.

(** Bitwise complement has linear cost in the input magnitude bits. *)
Lemma reducer_complement_time : forall z,
  (Z.T_lnot z <= 8 * N.of_nat (Z.size_nat z + 1))%N.
Proof.
  intro z; pose proof (Std.Z.T_pred_le (- z)) as Hpred.
  rewrite reducer_opp_bits in Hpred.
  time_unfold Z.T_lnot; time_unfold Std.Z.T_opp; time_cbn.
  rewrite Nat2N.inj_add; nia.
Qed.

(** Both endpoints emitted by the known-bit hull fit within the word width. *)
Lemma reducer_hull_bits : forall w b,
  (wrapped_bits (bits_hull w b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w b.
  pose proof (reducer_word_bits w _ (reducer_wrap_word w (ones b))) as Hlo.
  pose proof (reducer_word_bits w _ (reducer_bits_upper_word w b)) as Hhi.
  unfold bits_hull; destruct (Z.leb _ _); cbn [wrapped_bits]; lia.
Qed.

(** Common-prefix extraction emits two normalized word masks. *)
Lemma reducer_arc_prefix_words : forall w a,
  Word.is_word w (zeros (arc_prefix w a)) /\
  Word.is_word w (ones (arc_prefix w a)).
Proof.
  intros w [| |lo hi]; cbn [arc_prefix zeros ones];
    try (split; apply Word.zero_is_word).
  destruct (Z.leb _ _); cbn [zeros ones];
    [|split; apply Word.zero_is_word].
  split.
  - rewrite Z.land_comm; apply reducer_and_word, reducer_ones_word.
  - apply reducer_and_word, reducer_wrap_word.
Qed.

(** The two common-prefix masks occupy at most twice the word width. *)
Lemma reducer_arc_prefix_bits : forall w a,
  (tnum_bits (arc_prefix w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a; destruct (reducer_arc_prefix_words w a) as [Hzero Hone].
  pose proof (reducer_word_bits w _ Hzero); pose proof (reducer_word_bits w _ Hone).
  unfold tnum_bits; lia.
Qed.

(** Constructing the known-bit hull is linear in width and the two raw masks. *)
Lemma reducer_hull_time : forall w b,
  (T_bits_hull w b <= 128 * N.of_nat (Pos.to_nat w + tnum_bits b + 1))%N.
Proof.
  intros w b.
  pose proof (reducer_wrap_time w (zeros b)) as Hzero.
  pose proof (reducer_wrap_time w (ones b)) as Hone.
  pose proof (reducer_ones_time (Zpos w) ltac:(lia)) as Hmask.
  pose proof (reducer_word_bits w _ (reducer_wrap_word w (zeros b))) as Hzerobits.
  pose proof (reducer_word_bits w _ (reducer_wrap_word w (ones b))) as Honebits.
  pose proof (reducer_word_bits w _ (reducer_ones_word w)) as Hmaskbits.
  pose proof (Std.Z.T_lxor_le (tnum_wrap w (zeros b)) (Z.ones (Zpos w))) as Hxor.
  pose proof (Std.Z.T_leb_le (tnum_wrap w (ones b))
    (Z.lxor (tnum_wrap w (zeros b)) (Z.ones (Zpos w)))) as Hcompare.
  time_unfold T_bits_hull; time_unfold T_zeros; time_unfold T_ones; time_cbn.
  unfold tnum_bits; change (Z.to_nat (Zpos w)) with (Pos.to_nat w) in Hmask.
  rewrite !Nat2N.inj_add in *; nia.
Qed.

(** A nonnegative bit index bounded by the width also has bounded storage. *)
Lemma reducer_index_bits : forall w n, 0 <= n <= Zpos w ->
  (Z.to_nat n <= Pos.to_nat w /\ Z.size_nat n <= Pos.to_nat w)%nat.
Proof.
  intros w n [Hnonnegative Hupper].
  pose proof (reducer_nonnegative_bits n Hnonnegative).
  pose proof (Z2Nat.id n Hnonnegative); pose proof (positive_nat_Z w); lia.
Qed.

(** Extracting the common prefix is linear in width and the raw arc endpoint bits. *)
Lemma reducer_arc_prefix_time : forall w a,
  (T_arc_prefix w a <= 512 * N.of_nat (Pos.to_nat w + wrapped_bits a + 1))%N.
Proof.
  intros w [| |lo hi]; time_unfold T_arc_prefix; time_cbn;
    cbn [wrapped_bits]; try (rewrite Nat2N.inj_add; nia).
  set (l := tnum_wrap w lo); set (h := tnum_wrap w hi).
  pose proof (reducer_wrap_time w lo) as Hwraplo.
  pose proof (reducer_wrap_time w hi) as Hwraphi.
  pose proof (reducer_wrap_word w lo) as Hlword; fold l in Hlword.
  pose proof (reducer_wrap_word w hi) as Hhword; fold h in Hhword.
  pose proof (reducer_word_bits w l Hlword) as Hlbits.
  pose proof (reducer_word_bits w h Hhword) as Hhbits.
  pose proof (Std.Z.T_leb_le l h) as Hcompare.
  destruct (Z.leb l h); [|rewrite !Nat2N.inj_add in *; nia].
  set (d := Z.lxor l h).
  pose proof (reducer_xor_word w l h Hlword Hhword) as Hdword; fold d in Hdword.
  pose proof (reducer_word_bits w d Hdword) as Hdbits.
  pose proof (reducer_log2_width w d Hdword) as Hcutoff.
  pose proof (Z.log2_nonneg d) as Hlog0.
  pose proof (reducer_index_bits w (Z.log2 d) ltac:(lia)) as [_ Hlogbits].
  pose proof (reducer_index_bits w (Z.log2 d + 1) Hcutoff) as [Hindex _].
  set (m := Z.ones (Z.log2 d + 1)).
  pose proof (reducer_mask_word w (Z.log2 d + 1) Hcutoff) as Hmword.
  fold m in Hmword.
  pose proof (reducer_word_bits w m Hmword) as Hmbits.
  pose proof (reducer_or_word w l m Hlword Hmword) as Hunionword.
  pose proof (reducer_word_bits w _ Hunionword) as Hunionbits.
  pose proof (reducer_complement_bits w m Hmword) as Hnotmbits.
  pose proof (reducer_complement_bits w _ Hunionword) as Hnotunionbits.
  pose proof (reducer_word_bits w _ (reducer_ones_word w)) as Hmaskbits.
  pose proof (Std.Z.T_lxor_le l h) as Hxor.
  pose proof (reducer_log2_time d) as Hlog.
  pose proof (Std.Z.T_add_le (Z.log2 d) 1) as Hsucc.
  pose proof (reducer_ones_time (Z.log2 d + 1) (proj1 Hcutoff)) as Hprefixmask.
  pose proof (Std.Z.T_lor_le l m) as Hunion.
  pose proof (reducer_complement_time m) as Hnotm.
  pose proof (reducer_complement_time (Z.lor l m)) as Hnotunion.
  pose proof (reducer_ones_time (Zpos w) ltac:(lia)) as Hmask.
  pose proof (Std.Z.T_land_le (Z.lnot (Z.lor l m)) (Z.ones (Zpos w))) as Hzeros.
  pose proof (Std.Z.T_land_le l (Z.lnot m)) as Hones.
  fold d m.
  change (Std.Z.T_add (Z.log2 d) 1 <=
    3 * N.of_nat (Z.size_nat (Z.log2 d) + 1) + 1)%N in Hsucc.
  change (Z.to_nat (Zpos w)) with (Pos.to_nat w) in Hmask.
  rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Width equality reads no more bits than the numeric value of the left width. *)
Lemma reducer_width_time : forall w v,
  (Std.Pos.T_eqb w v <= N.of_nat (Pos.to_nat w))%N.
Proof.
  intros w v; eapply N.le_trans; [apply Std.Pos.T_eqb_le|].
  apply time_of_nat_le, reducer_positive_bits.
Qed.

(** Positive comparison stops after traversing either operand's digits. *)
Lemma reducer_compare_right_time : forall c p q,
  (Std.Pos.T_compare_cont c p q <= N.of_nat (Pos.size_nat q))%N.
Proof.
  intros c p q; revert p c.
  induction q as [q IH | q IH |]; intros [p | p |] c; time_step.
Qed.

(** A nonnegative left operand can be compared against an upper-bounded right one
    using at most the word width, even when either raw magnitude is very large. *)
Lemma reducer_upper_compare_time : forall w x y, 0 <= x -> y < Word.modulus w ->
  (Std.Z.T_leb x y <= N.of_nat (Pos.to_nat w) + 4)%N.
Proof.
  intros w [|p|p] [|q|q] Hnonnegative Hupper; try lia.
  all: time_unfold Std.Z.T_leb; time_unfold Std.Z.T_compare;
    try time_unfold Std.Pos.T_compare; time_cbn; try lia.
  pose proof (reducer_compare_right_time Eq p q) as Hcompare.
  pose proof (reducer_word_bits w (Zpos q) ltac:(unfold Word.is_word; lia)) as Hbits.
  cbn [Z.size_nat] in Hbits; nia.
Qed.

(** Word clipping compares raw endpoints against width-bounded sentinels. *)
Lemma reducer_clip_time : forall w a,
  (T_interval_word_clip w a <= 128 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intros w a.
  pose proof (reducer_ones_time (Zpos w) ltac:(lia)) as Hmask.
  change (Z.to_nat (Zpos w)) with (Pos.to_nat w) in Hmask.
  pose proof (reducer_word_bits w _ (reducer_ones_word w)) as Hmaskbits.
  pose proof (reducer_ones_word w) as Hword; unfold Word.is_word in Hword.
  destruct a as [|[|lo|] [|hi|]]; time_unfold T_interval_word_clip; time_cbn.
  all: try match goal with
    | |- context [Std.Z.T_leb ?x ?y] =>
      pose proof (reducer_upper_compare_time w x y ltac:(lia) ltac:(lia)) as Hcompare
    end.
  all: time_pose; cbn [Z.size_nat] in *; rewrite !Nat2N.inj_add in *; nia.
Qed.

(** The interval extracted from known bits has width-bounded finite endpoints. *)
Lemma reducer_bits_interval_bits : forall w b,
  (interval_bits (bits_interval w b) <= Pos.to_nat w)%nat.
Proof.
  intros w b.
  pose proof (reducer_word_bits w _ (reducer_wrap_word w (ones b))) as Hlo.
  pose proof (reducer_word_bits w _ (reducer_bits_upper_word w b)) as Hhi.
  unfold bits_interval, bits_hull; destruct (Z.leb _ _); cbn [interval_bits]; lia.
Qed.

(** Converting the known-bit hull to an interval adds only a constant charge. *)
Lemma reducer_bits_interval_time : forall w b,
  (T_bits_interval w b <= 256 * N.of_nat (Pos.to_nat w + tnum_bits b + 1))%N.
Proof.
  intros w b; pose proof (reducer_hull_time w b) as Hhull.
  time_unfold T_bits_interval; destruct (bits_hull w b); time_cbn.
  all: rewrite !Nat2N.inj_add in *; nia.
Qed.

(** The interval common prefix emits at most two word-sized masks. *)
Lemma reducer_interval_prefix_bits : forall w a,
  (tnum_bits (interval_prefix w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a; unfold interval_prefix.
  destruct (interval_word_clip w a) as [|[|lo|] [|hi|]];
    first [exact (Nat.le_0_l _) | apply reducer_arc_prefix_bits].
Qed.

(** Clipping makes interval-prefix extraction linear in the word width. *)
Lemma reducer_interval_prefix_time : forall w a,
  (T_interval_prefix w a <= 2048 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intros w a; pose proof (reducer_clip_time w a) as Hcliptime.
  time_unfold T_interval_prefix.
  destruct (interval_word_clip w a) as [|[|lo|] [|hi|]] eqn:Hclip; time_cbn;
    try (rewrite !Nat2N.inj_add in *; nia).
  pose proof (reducer_clip_bounds w a lo hi Hclip) as Hbounds.
  pose proof (reducer_word_bits w lo ltac:(unfold Word.is_word; lia)) as Hlobits.
  pose proof (reducer_word_bits w hi ltac:(unfold Word.is_word; lia)) as Hhibits.
  pose proof (reducer_arc_prefix_time w (WItv lo hi)) as Hprefix.
  cbn [wrapped_bits] in Hprefix; rewrite !Nat2N.inj_add in *; nia.
Qed.

(** The residue extracted from a clipped interval stores at most one word. *)
Lemma reducer_interval_congr_bits : forall w a,
  (congr_bits (interval_congr (interval_word_clip w a)) <= Pos.to_nat w + 1)%nat.
Proof.
  intros w a.
  destruct (interval_word_clip w a) as [|[|lo|] [|hi|]] eqn:Hclip;
    cbn [interval_congr congr_bits Z.size_nat Pos.size_nat]; try lia.
  pose proof (reducer_clip_bounds w a lo hi Hclip) as Hbounds.
  pose proof (reducer_word_bits w lo ltac:(unfold Word.is_word; lia)) as Hbits.
  destruct (lo =? hi); cbn [congr_bits Z.size_nat Pos.size_nat]; lia.
Qed.

(** Singleton extraction compares only already clipped endpoints. *)
Lemma reducer_interval_congr_time : forall w a,
  (T_interval_congr (interval_word_clip w a) <= 16 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intros w a.
  destruct (interval_word_clip w a) as [|[|lo|] [|hi|]] eqn:Hclip;
    time_unfold T_interval_congr; time_cbn; try (rewrite !Nat2N.inj_add; nia).
  pose proof (reducer_clip_bounds w a lo hi Hclip) as Hbounds.
  pose proof (reducer_word_bits w lo ltac:(unfold Word.is_word; lia)) as Hbits.
  time_pose; rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Canonical word intervals are either bottom or ordered finite word endpoints. *)
Definition reducer_interval_range (w : positive) (a : itv) : Prop :=
  match a with
  | IBot => True
  | I (Fin lo) (Fin hi) => 0 <= lo <= hi /\ hi < Word.modulus w
  | _ => False
  end.

Module ReducerIntervalFacts (T : THRESHOLDS) (S : INTERVAL_SCALAR_OPS T).
  (** Scalar payload clipping always produces a canonical word interval. *)
  Lemma clip_range : forall w a,
    reducer_interval_range w (interval_payload_clip S.interval_meet w a).
  Proof.
    intros w [|[|lo|] [|hi|]].
    all: unfold interval_payload_clip, S.interval_meet, S.bound_max, S.bound_min,
      S.bounds_nonempty, S.bound_leb; cbn beta iota zeta.
    all: repeat match goal with
      | |- context [if ?c then _ else _] => destruct c eqn:?; cbn beta iota zeta
      end.
    all: repeat match goal with
      | H : (?x <=? ?y) = true |- _ => apply Z.leb_le in H
      | H : (?x <=? ?y) = false |- _ => apply Z.leb_gt in H
      end.
    all: cbn [reducer_interval_range]; pose proof (Word.modulus_pos w); lia.
  Qed.

  (** Clipping fixes ordered endpoints already in the word range. *)
  Lemma clip_finite : forall w lo hi, 0 <= lo <= hi -> hi < Word.modulus w ->
    interval_payload_clip S.interval_meet w (I (Fin lo) (Fin hi)) = I (Fin lo) (Fin hi).
  Proof.
    intros w lo hi Hbounds Hupper.
    unfold interval_payload_clip, S.interval_meet, S.bound_max, S.bound_min,
      S.bounds_nonempty, S.bound_leb; cbn beta iota zeta.
    assert (Hhi : (hi <=? Word.modulus w - 1) = true) by (apply Z.leb_le; lia).
    rewrite Hhi.
    destruct (lo <=? 0) eqn:Hlo; cbn beta iota zeta.
    - apply Z.leb_le in Hlo; assert (lo = 0) by lia; subst lo.
      assert (Horder : (0 <=? hi) = true) by (apply Z.leb_le; lia).
      rewrite Horder; reflexivity.
    - assert (Horder : (lo <=? hi) = true) by (apply Z.leb_le; lia).
      rewrite Horder; reflexivity.
  Qed.

  (** Finite scalar maximum agrees with integer maximum. *)
  Lemma bound_max_finite : forall x y,
    S.bound_max (Fin x) (Fin y) = Fin (Z.max x y).
  Proof.
    intros x y; unfold S.bound_max, S.bound_leb; destruct (x <=? y) eqn:Horder.
    - apply Z.leb_le in Horder; rewrite Z.max_r by exact Horder; reflexivity.
    - apply Z.leb_gt in Horder; rewrite Z.max_l by lia; reflexivity.
  Qed.

  (** Finite scalar minimum agrees with integer minimum. *)
  Lemma bound_min_finite : forall x y,
    S.bound_min (Fin x) (Fin y) = Fin (Z.min x y).
  Proof.
    intros x y; unfold S.bound_min, S.bound_leb; destruct (x <=? y) eqn:Horder.
    - apply Z.leb_le in Horder; rewrite Z.min_l by exact Horder; reflexivity.
    - apply Z.leb_gt in Horder; rewrite Z.min_r by lia; reflexivity.
  Qed.

  (** The direct word clip agrees with the scalar payload clip. *)
  Lemma word_clip_agrees : forall w a,
    interval_payload_clip S.interval_meet w a = interval_word_clip w a.
  Proof.
    intros w a.
    assert (Hmask : Z.ones (Zpos w) = Word.modulus w - 1)
      by (rewrite Z.ones_equiv; unfold Word.modulus; lia).
    destruct a as [|[|lo|] [|hi|]].
    all: unfold interval_payload_clip, interval_word_clip, S.interval_meet;
      cbn beta iota zeta; rewrite ?bound_max_finite, ?bound_min_finite.
    all: unfold S.bound_max, S.bound_min, S.bound_leb, S.bounds_nonempty;
      cbn beta iota zeta; rewrite ?Hmask; try reflexivity.
    all: try match goal with
      | |- context [Z.max ?x 0] => rewrite (Z.max_comm x 0)
      end.
    all: try match goal with
      | |- context [Z.min ?x (Word.modulus ?width - 1)] =>
        rewrite (Z.min_comm x (Word.modulus width - 1))
      end.
    all: reflexivity.
  Qed.

  (** Every canonical interval is fixed by scalar clipping. *)
  Lemma clip_canonical : forall w a, reducer_interval_range w a ->
    interval_payload_clip S.interval_meet w a = a.
  Proof.
    intros w [|[|lo|] [|hi|]] Hrange;
      cbn [reducer_interval_range] in Hrange; try contradiction.
    - reflexivity.
    - apply clip_finite; lia.
  Qed.

  (** Scalar clipping is idempotent. *)
  Lemma clip_idempotent : forall w a,
    interval_payload_clip S.interval_meet w (interval_payload_clip S.interval_meet w a) =
      interval_payload_clip S.interval_meet w a.
  Proof. intros; apply clip_canonical, clip_range. Qed.

  (** The direct word clip has the same canonical endpoint invariant. *)
  Lemma word_clip_range : forall w a, reducer_interval_range w (interval_word_clip w a).
  Proof. intros; rewrite <- word_clip_agrees; apply clip_range. Qed.

  (** Meeting two canonical word intervals preserves their endpoint bounds. *)
  Lemma meet_range : forall w a b, reducer_interval_range w a ->
    reducer_interval_range w b -> reducer_interval_range w (S.interval_meet a b).
  Proof.
    intros w [|[|lo|] [|hi|]] [|[|lo'|] [|hi'|]] Ha Hb;
      cbn [reducer_interval_range] in Ha, Hb; try contradiction.
    all: unfold S.interval_meet, S.bound_max, S.bound_min,
      S.bounds_nonempty, S.bound_leb; cbn beta iota zeta.
    all: repeat match goal with
      | |- context [if ?c then _ else _] => destruct c eqn:?; cbn beta iota zeta
      end.
    all: repeat match goal with
      | H : (?x <=? ?y) = true |- _ => apply Z.leb_le in H
      | H : (?x <=? ?y) = false |- _ => apply Z.leb_gt in H
      end.
    all: cbn [reducer_interval_range]; lia.
  Qed.
End ReducerIntervalFacts.

(** The order used by tagged word domains. *)
Definition reducer_tagged_leb {P} (pleb : positive -> P -> P -> bool)
    (pis_bot : positive -> P -> bool) (a b : tagged P) : bool :=
  match a, b with
  | TBot, _ => true
  | _, TAny => true
  | TVal w p, TVal v q => if Pos.eqb w v then pleb w p q else pis_bot w p
  | TVal w p, TBot => pis_bot w p
  | _, _ => false
  end.

Module WrappedBitsCode (L : WORD_LANGUAGE_OPS) (A0 : WORD_PAYLOAD_OPS L with Definition p := wrapped)
    (B0 : WORD_PAYLOAD_OPS L with Definition p := tnum)
    (A : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged A0.p)
    (B : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged B0.p)
    <: REDUCTION_STEPS_OPS BitsLangCode A B.
  Definition to_left (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w (A0.pmeet w a (bits_hull w b)), TVal v b) else x
    | _ => x
    end.
  Definition to_right (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w a, TVal v (B0.pmeet w b (arc_prefix w a))) else x
    | _ => x
    end.
  Definition reduce (x : A.t * B.t) : A.t * B.t := to_right (to_left x).
End WrappedBitsCode.

Module WrappedBits (L : WORD_LANGUAGE) (C : TNUM_CONFIG) (A0 : WRAPPED L)
    (B0 : KNOWN_BITS L C)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged A0.p
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged B0.p
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: REDUCTION_STEPS BitsLang A B.
  Include WrappedBitsCode L A0 B0 A B.

  (** The least and greatest known-bit members enclose every represented word. *)
  Lemma hull_sound : forall w b z, L.is_word w z -> B0.pgamma w b z ->
    A0.pgamma w (bits_hull w b) z.
  Proof.
    intros w b z Hword Hbits.
    apply B0.gamma_tnum in Hbits; unfold B0.tnum_gamma in Hbits.
    destruct Hbits as [Hzero Hone].
    pose proof (reducer_bits_bounds w b z Hword Hzero Hone) as Hbounds.
    pose proof (Word.wrap_is_word w (ones b)) as Hlo.
    rewrite <- reducer_tnum_wrap in Hlo.
    pose proof (reducer_bits_upper_word w b) as Hhi.
    apply A0.gamma_arc; unfold bits_hull.
    destruct (Z.leb (tnum_wrap w (ones b))
      (Z.lxor (tnum_wrap w (zeros b)) (Z.ones (Zpos w)))) eqn:Horder.
    - change (Word.is_word w z /\
        (z - tnum_wrap w (ones b)) mod Word.modulus w <=
        (Z.lxor (tnum_wrap w (zeros b)) (Z.ones (Zpos w)) -
          tnum_wrap w (ones b)) mod Word.modulus w).
      split; [exact Hword|].
      rewrite !Z.mod_small by (unfold Word.is_word in *; lia); lia.
    - apply Z.leb_gt in Horder; lia.
  Qed.

  (** The arc common prefix contains every represented word. *)
  Lemma prefix_sound : forall w a z, L.is_word w z -> A0.pgamma w a z ->
    B0.pgamma w (arc_prefix w a) z.
  Proof.
    intros w a z Hword Harc; apply A0.gamma_arc in Harc.
    apply B0.gamma_tnum; unfold B0.tnum_gamma.
    apply reducer_arc_prefix_sound; [exact Hword|].
    destruct a; unfold A0.arc_gamma, A0.offset in Harc; tauto.
  Qed.

  Lemma left_frame : forall x, snd (to_left x) = snd x.
  Proof.
    intros [[|w a|] [|v b|]]; cbn [to_left]; try reflexivity.
    destruct (Pos.eqb w v); reflexivity.
  Qed.
  Lemma right_frame : forall x, fst (to_right x) = fst x.
  Proof.
    intros [[|w a|] [|v b|]]; cbn [to_right]; try reflexivity.
    destruct (Pos.eqb w v); reflexivity.
  Qed.
  Lemma left_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_left (a, b))) c.
  Proof.
    intros [|w a|] [|v b|] [u z] Ha Hb; cbn [to_left fst]; try exact Ha.
    destruct (Pos.eqb w v) eqn:Hwidth; cbn [fst]; [|exact Ha].
    apply Pos.eqb_eq in Hwidth; subst v.
    change (u = w /\ L.is_word w z /\ A0.pgamma w a z) in Ha.
    change (u = w /\ L.is_word w z /\ B0.pgamma w b z) in Hb.
    destruct Ha as [Hu [Hword Ha]]; destruct Hb as [_ [_ Hb]].
    change (u = w /\ L.is_word w z /\
      A0.pgamma w (A0.pmeet w a (bits_hull w b)) z).
    split; [exact Hu|]; split; [exact Hword|].
    apply A0.pgamma_meet; [exact Ha|now apply hull_sound].
  Qed.
  Lemma right_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    B.gamma (snd (to_right (a, b))) c.
  Proof.
    intros [|w a|] [|v b|] [u z] Ha Hb; cbn [to_right snd]; try exact Hb.
    destruct (Pos.eqb w v) eqn:Hwidth; cbn [snd]; [|exact Hb].
    apply Pos.eqb_eq in Hwidth; subst v.
    change (u = w /\ L.is_word w z /\ A0.pgamma w a z) in Ha.
    change (u = w /\ L.is_word w z /\ B0.pgamma w b z) in Hb.
    destruct Ha as [_ [Hword Ha]]; destruct Hb as [Hu [_ Hb]].
    change (u = w /\ L.is_word w z /\
      B0.pgamma w (B0.pmeet w b (arc_prefix w a)) z).
    split; [exact Hu|]; split; [exact Hword|].
    apply B0.pgamma_meet; [exact Hb|now apply prefix_sound].
  Qed.
  Lemma left_lower : forall a b, A.leb (fst (to_left (a, b))) a = true.
  Proof.
    intros [|w a|] [|v b|]; cbn [to_left fst]; try apply A.leb_refl.
    destruct (Pos.eqb w v); cbn [fst]; [|apply A.leb_refl].
    unfold A.leb, reducer_tagged_leb.
    rewrite Pos.eqb_refl.
    apply A0.pmeet_lb_l.
  Qed.
  Lemma right_lower : forall a b, B.leb (snd (to_right (a, b))) b = true.
  Proof.
    intros [|w a|] [|v b|]; cbn [to_right snd]; try apply B.leb_refl.
    destruct (Pos.eqb w v) eqn:Hwv; cbn [snd]; [|apply B.leb_refl].
    apply Pos.eqb_eq in Hwv; subst v.
    unfold B.leb, reducer_tagged_leb.
    rewrite Pos.eqb_refl.
    apply B0.pmeet_lb_l.
  Qed.
  Lemma reduce_steps : forall x, reduce x = to_right (to_left x).
  Proof.
    reflexivity.
  Qed.
  Lemma to_left_def : forall w a b, to_left (TVal w a, TVal w b) =
    (TVal w (A0.pmeet w a (bits_hull w b)), TVal w b).
  Proof.
    intros; unfold to_left, to_right; rewrite Pos.eqb_refl; reflexivity.
  Qed.
  Lemma to_right_def : forall w a b, to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (B0.pmeet w b (arc_prefix w a))).
  Proof.
    intros; unfold to_left, to_right; rewrite Pos.eqb_refl; reflexivity.
  Qed.
  Lemma reduce_fixes_other_pairs : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    to_left x = x /\ to_right x = x.
  Proof.
    intros [[|w a|] [|v b|]] Hshape; cbn [to_left to_right];
      try (split; reflexivity).
    destruct (Pos.eqb w v) eqn:Hwv; [|split; reflexivity].
    apply Pos.eqb_eq in Hwv; subst v.
    exfalso; apply (Hshape w a b); reflexivity.
  Qed.

  Lemma reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
  Proof.
    intros a b; unfold reduce; split.
    - rewrite right_frame; apply left_lower.
    - destruct (to_left (a, b)) as [a' b'] eqn:Hleft.
      pose proof (left_frame (a, b)) as Hframe.
      rewrite Hleft in Hframe; cbn in Hframe; subst b'.
      apply right_lower.
  Qed.

  (** The two sound exchanges retain the common concrete value. *)
  Lemma reduce_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (reduce (a, b))) c /\ B.gamma (snd (reduce (a, b))) c.
  Proof.
    intros a b c Ha Hb; unfold reduce; split.
    - rewrite right_frame; now apply left_sound.
    - pose proof (left_sound a b c Ha Hb) as Hleft.
      pose proof (left_frame (a, b)) as Hframe.
      destruct (to_left (a, b)) as [a' b']; cbn in Hframe, Hleft; subst b'.
      now apply right_sound.
  Qed.
End WrappedBits.

Module IntervalCongrCode (L : WORD_LANGUAGE_OPS) (A0 : WORD_PAYLOAD_OPS L with Definition p := itv)
    (B0 : WORD_PAYLOAD_OPS L with Definition p := congr)
    (A : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged A0.p)
    (B : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged B0.p)
    <: REDUCTION_STEPS_OPS BitsLangCode A B.
  (** Normalize the derived interval before passing it to the payload meet. *)
  Definition to_left (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v
      then (TVal w (A0.pmeet w a (interval_word_clip w (congr_interval w a b))), TVal v b)
      else x
    | _ => x
    end.
  Definition to_right (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v
      then (TVal w a, TVal v (B0.pmeet w b (interval_congr (interval_word_clip w a))))
      else x
    | _ => x
    end.
  Definition reduce (x : A.t * B.t) : A.t * B.t := to_right (to_left x).
End IntervalCongrCode.

Module IntervalCongr (L : WORD_LANGUAGE) (T : THRESHOLDS)
    (S : INTERVAL_SCALAR_OPS T) (A0 : INTERVAL_PAYLOAD_PINNED L T S)
    (B0 : CONGRUENCE L)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged A0.p
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged B0.p
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: REDUCTION_STEPS BitsLang A B.
  Include IntervalCongrCode L A0 B0 A B.
  Module PrecisionFacts := ReducerIntervalFacts T S.

  (** Normalizing a meet operand preserves the exact pinned payload result. *)
  Lemma meet_word_clip_right : forall w a b,
    A0.pmeet w a (interval_word_clip w b) = A0.pmeet w a b.
  Proof.
    intros w a b; rewrite !A0.pmeet_def, <- PrecisionFacts.word_clip_agrees,
      PrecisionFacts.clip_idempotent; reflexivity.
  Qed.

  (** Inward rounding preserves each interval member in the supplied residue class. *)
  Lemma round_sound : forall w a b z, A0.pgamma w a z -> B0.pgamma w b z ->
    A0.pgamma w (congr_interval w a b) z.
  Proof.
    intros w a b z Ha Hb.
    apply A0.pgamma_def in Ha; destruct Ha as [Hword Ha].
    pose proof (reducer_clip_sound w a z Hword Ha) as Hclip.
    apply B0.gamma_def in Hb; unfold B0.congr_gamma in Hb.
    destruct b as [|m r]; [contradiction|].
    destruct Hb as [_ Hdiv].
    apply A0.pgamma_def; split; [exact Hword|].
    unfold congr_interval.
    destruct (interval_word_clip w a) as [|lo hi]; [contradiction|].
    destruct (m =? 0) eqn:Hmodulus.
    - apply Z.eqb_eq in Hmodulus; subst m.
      destruct Hdiv as [q Hq]; unfold in_bnd; lia.
    - apply Z.eqb_neq in Hmodulus.
      destruct lo as [|lo|], hi as [|hi|]; unfold in_bnd in *; try tauto.
      + split; [constructor|].
        exact (proj2 (reducer_residue_round m r z hi z Hmodulus ltac:(lia) Hdiv)).
      + apply reducer_residue_round; assumption.
      + split; [|constructor].
        exact (proj1 (reducer_residue_round m r lo z z Hmodulus ltac:(lia) Hdiv)).
  Qed.

  (** A clipped singleton yields an exact congruence for each represented word. *)
  Lemma singleton_sound : forall w a z, A0.pgamma w a z ->
    B0.pgamma w (interval_congr (interval_word_clip w a)) z.
  Proof.
    intros w a z Ha; apply A0.pgamma_def in Ha; destruct Ha as [Hword Ha].
    pose proof (reducer_clip_sound w a z Hword Ha) as Hclip.
    apply B0.gamma_def; unfold interval_congr.
    destruct (interval_word_clip w a) as [|[|lo|] [|hi|]];
      try contradiction; unfold B0.congr_gamma;
      try (split; [exact Hword|exists z; lia]).
    destruct (lo =? hi) eqn:Hpoint; unfold B0.congr_gamma.
    - apply Z.eqb_eq in Hpoint; subst hi.
      split; [exact Hword|exists 0; unfold in_bnd in Hclip; lia].
    - split; [exact Hword|exists z; lia].
  Qed.


  Lemma left_frame : forall x, snd (to_left x) = snd x.
  Proof.
    intros [[|w a|] [|v b|]]; cbn [to_left]; try reflexivity.
    destruct (Pos.eqb w v); reflexivity.
  Qed.
  Lemma right_frame : forall x, fst (to_right x) = fst x.
  Proof.
    intros [[|w a|] [|v b|]]; cbn [to_right]; try reflexivity.
    destruct (Pos.eqb w v); reflexivity.
  Qed.
  Lemma left_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_left (a, b))) c.
  Proof.
    intros [|w a|] [|v b|] [u z] Ha Hb; cbn [to_left fst]; try exact Ha.
    destruct (Pos.eqb w v) eqn:Hwidth; cbn [fst]; [|exact Ha].
    apply Pos.eqb_eq in Hwidth; subst v.
    change (u = w /\ L.is_word w z /\ A0.pgamma w a z) in Ha.
    change (u = w /\ L.is_word w z /\ B0.pgamma w b z) in Hb.
    destruct Ha as [Hu [Hword Ha]]; destruct Hb as [_ [_ Hb]].
    rewrite meet_word_clip_right.
    change (u = w /\ L.is_word w z /\
      A0.pgamma w (A0.pmeet w a (congr_interval w a b)) z).
    split; [exact Hu|]; split; [exact Hword|].
    apply A0.pgamma_meet; [exact Ha|now apply round_sound].
  Qed.
  Lemma right_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    B.gamma (snd (to_right (a, b))) c.
  Proof.
    intros [|w a|] [|v b|] [u z] Ha Hb; cbn [to_right snd]; try exact Hb.
    destruct (Pos.eqb w v) eqn:Hwidth; cbn [snd]; [|exact Hb].
    apply Pos.eqb_eq in Hwidth; subst v.
    change (u = w /\ L.is_word w z /\ A0.pgamma w a z) in Ha.
    change (u = w /\ L.is_word w z /\ B0.pgamma w b z) in Hb.
    destruct Ha as [_ [Hword Ha]]; destruct Hb as [Hu [_ Hb]].
    change (u = w /\ L.is_word w z /\
      B0.pgamma w (B0.pmeet w b (interval_congr (interval_word_clip w a))) z).
    split; [exact Hu|]; split; [exact Hword|].
    apply B0.pgamma_meet; [exact Hb|now apply singleton_sound].
  Qed.
  Lemma left_lower : forall a b, A.leb (fst (to_left (a, b))) a = true.
  Proof.
    intros [|w a|] [|v b|]; cbn [to_left fst]; try apply A.leb_refl.
    destruct (Pos.eqb w v); cbn [fst]; [|apply A.leb_refl].
    unfold A.leb, reducer_tagged_leb.
    rewrite Pos.eqb_refl.
    apply A0.pmeet_lb_l.
  Qed.
  Lemma right_lower : forall a b, B.leb (snd (to_right (a, b))) b = true.
  Proof.
    intros [|w a|] [|v b|]; cbn [to_right snd]; try apply B.leb_refl.
    destruct (Pos.eqb w v) eqn:Hwv; cbn [snd]; [|apply B.leb_refl].
    apply Pos.eqb_eq in Hwv; subst v.
    unfold B.leb, reducer_tagged_leb.
    rewrite Pos.eqb_refl.
    apply B0.pmeet_lb_l.
  Qed.
  Lemma reduce_steps : forall x, reduce x = to_right (to_left x).
  Proof.
    reflexivity.
  Qed.
  Lemma to_left_def : forall w a b, to_left (TVal w a, TVal w b) =
    (TVal w (A0.pmeet w a (congr_interval w a b)), TVal w b).
  Proof.
    intros; unfold to_left; rewrite Pos.eqb_refl, meet_word_clip_right; reflexivity.
  Qed.
  Lemma to_right_def : forall w a b, to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (B0.pmeet w b (interval_congr (interval_word_clip w a)))).
  Proof.
    intros; unfold to_left, to_right; rewrite Pos.eqb_refl; reflexivity.
  Qed.
  Lemma reduce_fixes_other_pairs : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    to_left x = x /\ to_right x = x.
  Proof.
    intros [[|w a|] [|v b|]] Hshape; cbn [to_left to_right];
      try (split; reflexivity).
    destruct (Pos.eqb w v) eqn:Hwv; [|split; reflexivity].
    apply Pos.eqb_eq in Hwv; subst v.
    exfalso; apply (Hshape w a b); reflexivity.
  Qed.

  Lemma reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
  Proof.
    intros a b; unfold reduce; split.
    - rewrite right_frame; apply left_lower.
    - destruct (to_left (a, b)) as [a' b'] eqn:Hleft.
      pose proof (left_frame (a, b)) as Hframe.
      rewrite Hleft in Hframe; cbn in Hframe; subst b'.
      apply right_lower.
  Qed.


  Lemma reduce_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (reduce (a, b))) c /\ B.gamma (snd (reduce (a, b))) c.
  Proof.
    intros a b c Ha Hb; unfold reduce; split.
    - rewrite right_frame; now apply left_sound.
    - pose proof (left_sound a b c Ha Hb) as Hleft.
      pose proof (left_frame (a, b)) as Hframe.
      destruct (to_left (a, b)) as [a' b']; cbn in Hframe, Hleft; subst b'.
      now apply right_sound.
  Qed.
End IntervalCongr.

Module IntervalBitsCode (L : WORD_LANGUAGE_OPS) (A0 : WORD_PAYLOAD_OPS L with Definition p := itv)
    (B0 : WORD_PAYLOAD_OPS L with Definition p := tnum)
    (A : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged A0.p)
    (B : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged B0.p)
    <: REDUCTION_STEPS_OPS BitsLangCode A B.
  Definition to_left (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w (A0.pmeet w a (bits_interval w b)), TVal v b) else x
    | _ => x
    end.
  Definition to_right (x : A.t * B.t) : A.t * B.t :=
    match x with
    | (TVal w a, TVal v b) =>
      if Pos.eqb w v then (TVal w a, TVal v (B0.pmeet w b (interval_prefix w a))) else x
    | _ => x
    end.
  Definition reduce (x : A.t * B.t) : A.t * B.t := to_right (to_left x).
End IntervalBitsCode.

Module IntervalBits (L : WORD_LANGUAGE) (C : TNUM_CONFIG) (T : THRESHOLDS)
    (S : INTERVAL_SCALAR_OPS T) (A0 : INTERVAL_PAYLOAD_PINNED L T S)
    (B0 : KNOWN_BITS L C)
    (A : VALUE_DOMAIN BitsLang with Definition t := tagged A0.p
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN BitsLang with Definition t := tagged B0.p
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: REDUCTION_STEPS BitsLang A B.
  Include IntervalBitsCode L A0 B0 A B.

  (** The known-bit hull supplies sound finite interval endpoints. *)
  Lemma hull_sound : forall w b z, L.is_word w z -> B0.pgamma w b z ->
    A0.pgamma w (bits_interval w b) z.
  Proof.
    intros w b z Hword Hbits.
    apply B0.gamma_tnum in Hbits; unfold B0.tnum_gamma in Hbits.
    destruct Hbits as [Hzero Hone].
    pose proof (reducer_bits_bounds w b z Hword Hzero Hone) as Hbounds.
    apply A0.pgamma_def; split; [exact Hword|].
    unfold bits_interval, bits_hull.
    destruct (Z.leb (tnum_wrap w (ones b))
      (Z.lxor (tnum_wrap w (zeros b)) (Z.ones (Zpos w)))) eqn:Horder.
    - exact Hbounds.
    - apply Z.leb_gt in Horder; lia.
  Qed.

  (** Word clipping and prefix extraction retain each interval member. *)
  Lemma prefix_sound : forall w a z, A0.pgamma w a z ->
    B0.pgamma w (interval_prefix w a) z.
  Proof.
    intros w a z Ha; apply A0.pgamma_def in Ha; destruct Ha as [Hword Ha].
    pose proof (reducer_clip_sound w a z Hword Ha) as Hmember.
    apply B0.gamma_tnum; unfold B0.tnum_gamma, interval_prefix.
    destruct (interval_word_clip w a) as [|[|lo|] [|hi|]] eqn:Hclip;
      try (change (Z.land z (Word.wrap w 0) = 0 /\
        Z.land (Word.wrap w 0) (Z.lnot z) = 0);
        rewrite Word.wrap_0, Z.land_0_r, Z.land_0_l; split; reflexivity).
    apply reducer_arc_prefix_sound; [exact Hword|].
    pose proof (reducer_clip_bounds w a lo hi Hclip) as Hbounds.
    unfold in_bnd in Hmember.
    change ((z - lo) mod Word.modulus w <= (hi - lo) mod Word.modulus w).
    rewrite !Z.mod_small by (unfold Word.is_word in *; lia); lia.
  Qed.


  Lemma left_frame : forall x, snd (to_left x) = snd x.
  Proof.
    intros [[|w a|] [|v b|]]; cbn [to_left]; try reflexivity.
    destruct (Pos.eqb w v); reflexivity.
  Qed.
  Lemma right_frame : forall x, fst (to_right x) = fst x.
  Proof.
    intros [[|w a|] [|v b|]]; cbn [to_right]; try reflexivity.
    destruct (Pos.eqb w v); reflexivity.
  Qed.
  Lemma left_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_left (a, b))) c.
  Proof.
    intros [|w a|] [|v b|] [u z] Ha Hb; cbn [to_left fst]; try exact Ha.
    destruct (Pos.eqb w v) eqn:Hwidth; cbn [fst]; [|exact Ha].
    apply Pos.eqb_eq in Hwidth; subst v.
    change (u = w /\ L.is_word w z /\ A0.pgamma w a z) in Ha.
    change (u = w /\ L.is_word w z /\ B0.pgamma w b z) in Hb.
    destruct Ha as [Hu [Hword Ha]]; destruct Hb as [_ [_ Hb]].
    change (u = w /\ L.is_word w z /\
      A0.pgamma w (A0.pmeet w a (bits_interval w b)) z).
    split; [exact Hu|]; split; [exact Hword|].
    apply A0.pgamma_meet; [exact Ha|now apply hull_sound].
  Qed.
  Lemma right_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    B.gamma (snd (to_right (a, b))) c.
  Proof.
    intros [|w a|] [|v b|] [u z] Ha Hb; cbn [to_right snd]; try exact Hb.
    destruct (Pos.eqb w v) eqn:Hwidth; cbn [snd]; [|exact Hb].
    apply Pos.eqb_eq in Hwidth; subst v.
    change (u = w /\ L.is_word w z /\ A0.pgamma w a z) in Ha.
    change (u = w /\ L.is_word w z /\ B0.pgamma w b z) in Hb.
    destruct Ha as [_ [Hword Ha]]; destruct Hb as [Hu [_ Hb]].
    change (u = w /\ L.is_word w z /\
      B0.pgamma w (B0.pmeet w b (interval_prefix w a)) z).
    split; [exact Hu|]; split; [exact Hword|].
    apply B0.pgamma_meet; [exact Hb|now apply prefix_sound].
  Qed.
  Lemma left_lower : forall a b, A.leb (fst (to_left (a, b))) a = true.
  Proof.
    intros [|w a|] [|v b|]; cbn [to_left fst]; try apply A.leb_refl.
    destruct (Pos.eqb w v); cbn [fst]; [|apply A.leb_refl].
    unfold A.leb, reducer_tagged_leb.
    rewrite Pos.eqb_refl.
    apply A0.pmeet_lb_l.
  Qed.
  Lemma right_lower : forall a b, B.leb (snd (to_right (a, b))) b = true.
  Proof.
    intros [|w a|] [|v b|]; cbn [to_right snd]; try apply B.leb_refl.
    destruct (Pos.eqb w v) eqn:Hwv; cbn [snd]; [|apply B.leb_refl].
    apply Pos.eqb_eq in Hwv; subst v.
    unfold B.leb, reducer_tagged_leb.
    rewrite Pos.eqb_refl.
    apply B0.pmeet_lb_l.
  Qed.
  Lemma reduce_steps : forall x, reduce x = to_right (to_left x).
  Proof.
    reflexivity.
  Qed.
  Lemma to_left_def : forall w a b, to_left (TVal w a, TVal w b) =
    (TVal w (A0.pmeet w a (bits_interval w b)), TVal w b).
  Proof.
    intros; unfold to_left, to_right; rewrite Pos.eqb_refl; reflexivity.
  Qed.
  Lemma to_right_def : forall w a b, to_right (TVal w a, TVal w b) =
    (TVal w a, TVal w (B0.pmeet w b (interval_prefix w a))).
  Proof.
    intros; unfold to_left, to_right; rewrite Pos.eqb_refl; reflexivity.
  Qed.
  Lemma reduce_fixes_other_pairs : forall x, (forall w a b, x <> (TVal w a, TVal w b)) ->
    to_left x = x /\ to_right x = x.
  Proof.
    intros [[|w a|] [|v b|]] Hshape; cbn [to_left to_right];
      try (split; reflexivity).
    destruct (Pos.eqb w v) eqn:Hwv; [|split; reflexivity].
    apply Pos.eqb_eq in Hwv; subst v.
    exfalso; apply (Hshape w a b); reflexivity.
  Qed.

  Lemma reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
  Proof.
    intros a b; unfold reduce; split.
    - rewrite right_frame; apply left_lower.
    - destruct (to_left (a, b)) as [a' b'] eqn:Hleft.
      pose proof (left_frame (a, b)) as Hframe.
      rewrite Hleft in Hframe; cbn in Hframe; subst b'.
      apply right_lower.
  Qed.


  Lemma reduce_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (reduce (a, b))) c /\ B.gamma (snd (reduce (a, b))) c.
  Proof.
    intros a b c Ha Hb; unfold reduce; split.
    - rewrite right_frame; now apply left_sound.
    - pose proof (left_sound a b c Ha Hb) as Hleft.
      pose proof (left_frame (a, b)) as Hframe.
      destruct (to_left (a, b)) as [a' b']; cbn in Hframe, Hleft; subst b'.
      now apply right_sound.
  Qed.
End IntervalBits.

Module WrappedBitsT (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG)
    (A0 : WRAPPED_T L)
    (B0 : KNOWN_BITS_T L C)
    (A : VALUE_DOMAIN_T BitsLangT with Definition t := tagged A0.p
      with Definition size := tagged_size A0.psize
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN_T BitsLangT with Definition t := tagged B0.p
      with Definition size := tagged_size B0.psize
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: WRAPPED_BITS_ALL A B.
  Include WrappedBits L C A0 B0 A B.
  TimeFun to_left.
  TimeFun to_right.
  TimeFun reduce.
  Definition c_exchange : N := 1024 * (A0.c_payload + B0.c_payload + 1).
  Definition c_reduce : N := (c_exchange + 1) * (c_exchange + 1).
  Definition k_exchange : N := 1.
  Lemma T_to_left_le : forall a b, (T_to_left (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros [|w a|] [|v b|]; time_unfold T_to_left; time_cbn;
      unfold A.size, B.size, tagged_size, c_exchange;
      rewrite ?A0.psize_bits, ?B0.psize_bits, ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (reducer_width_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; [|nia].
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_hull_time w b) as Hhull.
    pose proof (reducer_hull_bits w b) as Hbits.
    pose proof (A0.T_pmeet_le w a (bits_hull w b)) as Hmeet.
    rewrite !A0.psize_bits in Hmeet.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_to_right_le : forall a b, (T_to_right (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros [|w a|] [|v b|]; time_unfold T_to_right; time_cbn;
      unfold A.size, B.size, tagged_size, c_exchange;
      rewrite ?A0.psize_bits, ?B0.psize_bits, ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (reducer_width_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; [|nia].
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_arc_prefix_time w a) as Hprefix.
    pose proof (reducer_arc_prefix_bits w a) as Hbits.
    pose proof (B0.T_pmeet_le w b (arc_prefix w a)) as Hmeet.
    rewrite !B0.psize_bits in Hmeet.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma left_size : forall a b,
    (N.of_nat (A.size (fst (to_left (a, b))) + B.size b) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros [|w a|] [|v b|]; unfold to_left; cbn [fst];
      unfold A.size, B.size, tagged_size, c_exchange;
      try (rewrite !Nat2N.inj_add; time_cbn; nia).
    destruct (Pos.eqb w v) eqn:Hsame; time_cbn;
      rewrite ?A0.psize_bits, ?B0.psize_bits, ?Nat2N.inj_add; try nia.
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_hull_bits w b) as Hbits.
    pose proof (A0.pmeet_size w a (bits_hull w b)) as Hmeet.
    rewrite !A0.psize_bits in Hmeet.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma right_size : forall a b,
    (N.of_nat (A.size a + B.size (snd (to_right (a, b)))) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros [|w a|] [|v b|]; unfold to_right; cbn [snd];
      unfold A.size, B.size, tagged_size, c_exchange;
      try (rewrite !Nat2N.inj_add; time_cbn; nia).
    destruct (Pos.eqb w v) eqn:Hsame; time_cbn;
      rewrite ?A0.psize_bits, ?B0.psize_bits, ?Nat2N.inj_add; try nia.
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_arc_prefix_bits w a) as Hbits.
    pose proof (B0.pmeet_size w b (arc_prefix w a)) as Hmeet.
    rewrite !B0.psize_bits in Hmeet.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_reduce_le : forall a b,
    (T_reduce (a, b) <= c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros a b.
    pose proof (T_to_left_le a b) as Hleft.
    pose proof (left_size a b) as Hsize.
    pose proof (left_frame (a, b)) as Hframe.
    destruct (to_left (a, b)) as [a' b'] eqn:Hstep.
    cbn [fst snd] in Hsize, Hframe; subst b'.
    pose proof (T_to_right_le a' b) as Hright.
    time_unfold T_reduce; cbn beta iota zeta; rewrite Hstep.
    unfold c_reduce; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma reduce_size_le : forall a b,
    (N.of_nat (A.size (fst (reduce (a, b))) + B.size (snd (reduce (a, b)))) <=
      c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros a b; unfold reduce; rewrite right_frame.
    pose proof (left_size a b) as Hleft.
    pose proof (left_frame (a, b)) as Hframe.
    destruct (to_left (a, b)) as [a' b'] eqn:Hstep.
    cbn [fst snd] in Hleft, Hframe; subst b'.
    pose proof (right_size a' b) as Hright.
    cbn [fst]; unfold c_reduce; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  Proof.
    exact reduce_sound.
  Qed.
  Lemma steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  Proof.
    exact reduce_lower.
  Qed.
  Lemma T_reduce_split : forall x, (T_reduce x <=
    k_exchange * (T_to_left x + T_to_right (to_left x) + 1))%N.
  Proof.
    intro x; unfold k_exchange; time_step.
  Qed.
  Lemma reduce_complexity :
    T_reduce (a, b) ∈ 𝑂(N.of_nat (A.size a + B.size b + 1)) for (a, b).
  Proof.
    exists c_reduce; intros [a b] _; cbn [fst snd].
    pose proof (T_reduce_le a b); nia.
  Qed.
End WrappedBitsT.

Module IntervalCongrT (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T)
    (A0 : INTERVAL_PAYLOAD_PINNED_T L T S)
    (B0 : CONGRUENCE_T L)
    (A : VALUE_DOMAIN_T BitsLangT with Definition t := tagged A0.p
      with Definition size := tagged_size A0.psize
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN_T BitsLangT with Definition t := tagged B0.p
      with Definition size := tagged_size B0.psize
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: INTERVAL_CONGR_ALL A B.
  Include IntervalCongr L T S A0 B0 A B.
  Module IntervalFacts := ReducerIntervalFacts T S.
  TimeFun to_left.
  TimeFun to_right.
  TimeFun reduce.
  Definition c_exchange : N := 131072 * (A0.c_payload + 1) * (A0.c_payload + 1) *
    (A0.c_payload + 1) * (B0.c_payload + 1).
  Definition c_reduce : N := (c_exchange + 1) * (c_exchange + 1).
  Definition k_exchange : N := 1.

  (** Canonical interval storage is bounded by joining its endpoint constants. *)
  Lemma canonical_payload_size : forall w a, reducer_interval_range w a ->
    (N.of_nat (A0.psize w a) <= 16 * (A0.c_payload + 1) * (A0.c_payload + 1) *
      N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros w [|[|lo|] [|hi|]] Hrange;
      cbn [reducer_interval_range] in Hrange; try contradiction.
    - rewrite <- (A0.pbot_def w).
      eapply N.le_trans; [apply A0.pbot_size|].
      apply N.mul_le_mono_r; nia.
    - assert (Hlo : Word.is_word w lo) by (unfold Word.is_word; lia).
      assert (Hhi : Word.is_word w hi) by (unfold Word.is_word; lia).
      pose proof (reducer_word_bits w lo Hlo) as Hlobits.
      pose proof (reducer_word_bits w hi Hhi) as Hhibits.
      assert (Hjoin : A0.pjoin w (A0.pconst w lo) (A0.pconst w hi) = I (Fin lo) (Fin hi)).
      { rewrite A0.pjoin_def, !A0.pconst_def.
        unfold L.wrap; rewrite !Word.wrap_id by assumption.
        rewrite !IntervalFacts.clip_finite by lia.
        unfold S.interval_join, S.bound_min, S.bound_max, S.bound_leb; cbn beta iota zeta.
        assert (Horder : (lo <=? hi) = true) by (apply Z.leb_le; lia).
        rewrite Horder; reflexivity. }
      pose proof (A0.pjoin_size w (A0.pconst w lo) (A0.pconst w hi)) as Hjoin_size.
      rewrite Hjoin in Hjoin_size; rewrite !Nat2N.inj_add in Hjoin_size.
      assert (Hliteral : forall z, (Z.size_nat z <= Pos.to_nat w)%nat ->
        (N.of_nat (A0.psize w (A0.pconst w z)) <=
          4 * A0.c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
      { intros z Hz; pose proof (A0.pconst_size w z) as Hsize.
        assert (Hbudget : (N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2) <=
          4 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
        { rewrite !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add; nia. }
        nia. }
      pose proof (Hliteral lo Hlobits) as Hlosize.
      pose proof (Hliteral hi Hhibits) as Hhisize.
      assert (Hwidth : (1 <= N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
      { rewrite Nat.pow_2_r, Nat2N.inj_mul, Nat2N.inj_add; nia. }
      clear -Hjoin_size Hlosize Hhisize Hwidth; nia.
  Qed.

  (** Every payload meet is canonical because its two operands are clipped. *)
  Lemma meet_payload_range : forall w a b, reducer_interval_range w (A0.pmeet w a b).
  Proof.
    intros w a b; rewrite A0.pmeet_def; apply IntervalFacts.meet_range;
      apply IntervalFacts.clip_range.
  Qed.

  (** Residue rounding charges the width and the two raw congruence integers quadratically. *)
  Lemma congr_interval_time : forall w a b,
    (T_congr_interval w a b <=
      4096 * N.of_nat ((Pos.to_nat w + congr_bits b + 1) ^ 2))%N.
  Proof.
    intros w a b.
    pose proof (reducer_clip_time w a) as Hcliptime.
    pose proof (IntervalFacts.word_clip_range w a) as Hrange.
    time_unfold T_congr_interval.
    destruct (interval_word_clip w a) as [|[|lo|] [|hi|]] eqn:Hclip;
      cbn [reducer_interval_range] in Hrange; try contradiction.
    all: destruct b as [|m r]; time_cbn; unfold congr_bits;
      try (rewrite ?Nat.pow_2_r, ?Nat2N.inj_mul, ?Nat2N.inj_add in *; nia).
    pose proof (reducer_word_bits w lo ltac:(unfold Word.is_word; lia)) as Hlobits.
    pose proof (reducer_word_bits w hi ltac:(unfold Word.is_word; lia)) as Hhibits.
    pose proof (Std.Z.T_eqb_le m 0) as Heqb.
    destruct (m =? 0) eqn:Hmodulus; time_cbn.
    - clear Hrange Hclip.
      rewrite ?Nat.pow_2_r, ?Nat2N.inj_mul, ?Nat2N.inj_add in *; nia.
    - apply Z.eqb_neq in Hmodulus.
      pose proof (reducer_sub_bits r lo) as Hlowerbits.
      pose proof (reducer_sub_bits hi r) as Hupperbits.
      pose proof (reducer_modulo_bits (r - lo) m Hmodulus) as Hlowmod.
      pose proof (reducer_modulo_bits (hi - r) m Hmodulus) as Hhighmod.
      set (s := (Pos.to_nat w + (Z.size_nat m + Z.size_nat r) + 1)%nat).
      assert (Hs : (1 <= s)%nat) by (unfold s; lia).
      assert (Hmodlo : (Std.Z.T_modulo (r - lo) (Z.abs m) <=
        256 * N.of_nat (s ^ 2))%N).
      { apply reducer_modulo_time_budget; rewrite ?reducer_abs_bits; unfold s; lia. }
      assert (Hmodhi : (Std.Z.T_modulo (hi - r) (Z.abs m) <=
        256 * N.of_nat (s ^ 2))%N).
      { apply reducer_modulo_time_budget; rewrite ?reducer_abs_bits; unfold s; lia. }
      assert (Hsublo : (Std.Z.T_sub r lo <= 3 * N.of_nat s)%N).
      { pose proof (Std.Z.T_sub_le r lo); unfold s; rewrite !Nat2N.inj_add in *; lia. }
      assert (Hsubhi : (Std.Z.T_sub hi r <= 3 * N.of_nat s)%N).
      { pose proof (Std.Z.T_sub_le hi r); unfold s; rewrite !Nat2N.inj_add in *; lia. }
      assert (Haddlo : (Std.Z.T_add lo ((r - lo) mod Z.abs m) <= 3 * N.of_nat s)%N).
      { pose proof (Std.Z.T_add_le lo ((r - lo) mod Z.abs m)).
        unfold s; rewrite !Nat2N.inj_add in *; lia. }
      assert (Hsubend : (Std.Z.T_sub hi ((hi - r) mod Z.abs m) <= 3 * N.of_nat s)%N).
      { pose proof (Std.Z.T_sub_le hi ((hi - r) mod Z.abs m)).
        unfold s; rewrite !Nat2N.inj_add in *; lia. }
      assert (Heqb_bound : (Std.Z.T_eqb m 0 <= N.of_nat s)%N).
      { unfold s; rewrite !Nat2N.inj_add; lia. }
      assert (Hclip_bound : (T_interval_word_clip w a <= 128 * N.of_nat s)%N).
      { unfold s; rewrite !Nat2N.inj_add in *; lia. }
      pose proof (Std.Z.T_abs_le m) as Habs.
      fold s; clearbody s.
      assert (Hlinear : (N.of_nat s <= N.of_nat (s ^ 2))%N).
      { clear -Hs; rewrite Nat.pow_2_r, Nat2N.inj_mul; nia. }
      clear -Hmodlo Hmodhi Hsublo Hsubhi Haddlo Hsubend Heqb_bound Hclip_bound Habs Hlinear Hs.
      rewrite ?Nat.pow_2_r, ?Nat.mul_1_r in *; lia.
  Qed.

  Lemma T_to_left_le : forall a b, (T_to_left (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    set (bound := (16 * (A0.c_payload + 1) * (A0.c_payload + 1))%N).
    assert (Hconstant : (A0.c_payload * bound + A0.c_payload + 8192 <= c_exchange)%N)
      by (unfold bound, c_exchange; nia).
    intros [|w a|] [|v b|]; time_unfold T_to_left; time_cbn;
      unfold A.size, B.size, tagged_size;
      try (rewrite ?Nat2N.inj_add; time_cbn; nia).
    pose proof (reducer_width_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; time_cbn;
      rewrite ?Nat2N.inj_add; try nia.
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (congr_interval_time w a b) as Hround.
    rewrite <- B0.psize_congr in Hround.
    pose proof (reducer_clip_time w (congr_interval w a b)) as Hclip.
    pose proof (A0.T_pmeet_le w a (interval_word_clip w (congr_interval w a b))) as Hmeet.
    pose proof (canonical_payload_size w (interval_word_clip w (congr_interval w a b))
      (IntervalFacts.word_clip_range w (congr_interval w a b))) as Hsize.
    fold bound in Hsize.
    assert (Hbudget : (N.of_nat ((Pos.to_nat w + 1) ^ 2) <=
      N.of_nat (B0.psize w b))%N).
    { rewrite B0.psize_congr, !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add; nia. }
    assert (Hderived : (N.of_nat (A0.psize w (interval_word_clip w (congr_interval w a b))) <=
      bound * N.of_nat (B0.psize w b))%N).
    { eapply N.le_trans; [exact Hsize|]. apply N.mul_le_mono_l; exact Hbudget. }
    clear Hsize Hbudget; clearbody bound.
    rewrite !Nat2N.inj_add in *.
    match goal with |- (_ <= ?coefficient * ?size)%N => set (total := size) end.
    assert (Hleft_budget : (N.of_nat (A0.psize w a) + 1 <= total)%N)
      by (unfold total; lia).
    assert (Hright_budget : (N.of_nat (B0.psize w b) <= total)%N)
      by (unfold total; lia).
    assert (Hwidth_budget : (N.of_nat (Pos.to_nat w) + 1 <= total)%N)
      by (unfold total; lia).
    assert (Hderived_total : (N.of_nat (A0.psize w (interval_word_clip w (congr_interval w a b))) <=
      bound * total)%N).
    { eapply N.le_trans; [exact Hderived|]. apply N.mul_le_mono_l; exact Hright_budget. }
    assert (Hmeet_total : (A0.T_pmeet w a (interval_word_clip w (congr_interval w a b)) <=
      (A0.c_payload * bound + A0.c_payload) * total)%N).
    { eapply N.le_trans; [exact Hmeet|].
      replace ((A0.c_payload * bound + A0.c_payload) * total)%N with
        (A0.c_payload * (bound * total + total))%N by (clear; ring).
      apply N.mul_le_mono_l; lia. }
    assert (Hround_total : (T_congr_interval w a b <= 4096 * total)%N).
    { eapply N.le_trans; [exact Hround|]. apply N.mul_le_mono_l; exact Hright_budget. }
    assert (Hclip_total : (T_interval_word_clip w (congr_interval w a b) <= 128 * total)%N).
    { eapply N.le_trans; [exact Hclip|]. apply N.mul_le_mono_l; exact Hwidth_budget. }
    clearbody total.
    eapply N.le_trans with (m := ((A0.c_payload * bound + A0.c_payload + 8192) * total)%N).
    - rewrite N.mul_add_distr_r.
      clear -Hmeet_total Hround_total Hclip_total Hwidth Hwidth_budget; lia.
    - apply N.mul_le_mono_r; exact Hconstant.
  Qed.
  Lemma T_to_right_le : forall a b, (T_to_right (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    assert (Hconstant : (256 * (B0.c_payload + 1) <= c_exchange)%N)
      by (unfold c_exchange; nia).
    intros [|w a|] [|v b|]; time_unfold T_to_right; time_cbn;
      unfold A.size, B.size, tagged_size;
      try (rewrite ?Nat2N.inj_add; time_cbn; nia).
    pose proof (reducer_width_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; time_cbn;
      rewrite ?Nat2N.inj_add; try nia.
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_clip_time w a) as Hclip.
    pose proof (reducer_interval_congr_time w a) as Hsingleton.
    pose proof (reducer_interval_congr_bits w a) as Hbits.
    pose proof (B0.T_pmeet_le w b (interval_congr (interval_word_clip w a))) as Hmeet.
    assert (Hderived : (N.of_nat (B0.psize w (interval_congr (interval_word_clip w a))) <=
      4 * N.of_nat (B0.psize w b))%N).
    { rewrite !B0.psize_congr, !Nat.pow_2_r.
      rewrite !Nat2N.inj_mul, !Nat2N.inj_add; nia. }
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma left_size : forall a b,
    (N.of_nat (A.size (fst (to_left (a, b))) + B.size b) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    set (bound := (16 * (A0.c_payload + 1) * (A0.c_payload + 1))%N).
    assert (Hconstant : (2 * bound + 1 <= c_exchange)%N)
      by (unfold bound, c_exchange; nia).
    intros [|w a|] [|v b|]; unfold to_left; cbn [fst];
      unfold A.size, B.size, tagged_size;
      try (rewrite ?Nat2N.inj_add; time_cbn; nia).
    destruct (Pos.eqb w v) eqn:Hsame; time_cbn;
      rewrite ?Nat2N.inj_add; try nia.
    apply Pos.eqb_eq in Hsame; subst v.
    rewrite meet_word_clip_right.
    pose proof (canonical_payload_size w (A0.pmeet w a (congr_interval w a b))
      (meet_payload_range w a (congr_interval w a b))) as Houtput.
    fold bound in Houtput.
    assert (Hbudget : (N.of_nat ((Pos.to_nat w + 1) ^ 2) <=
      N.of_nat (B0.psize w b))%N).
    { rewrite B0.psize_congr, !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add; nia. }
    assert (Hresult : (N.of_nat (A0.psize w (A0.pmeet w a (congr_interval w a b))) <=
      bound * N.of_nat (B0.psize w b))%N).
    { eapply N.le_trans; [exact Houtput|]. apply N.mul_le_mono_l; exact Hbudget. }
    clearbody bound; clear -Hconstant Hresult; nia.
  Qed.
  Lemma right_size : forall a b,
    (N.of_nat (A.size a + B.size (snd (to_right (a, b)))) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    assert (Hconstant : (1 <= c_exchange)%N) by (unfold c_exchange; nia).
    assert (Hpayload : (8 * (B0.c_payload + 1) <= c_exchange)%N)
      by (unfold c_exchange; nia).
    intros [|w a|] [|v b|]; unfold to_right; cbn [snd];
      unfold A.size, B.size, tagged_size;
      try (rewrite !Nat2N.inj_add; time_cbn; nia).
    destruct (Pos.eqb w v) eqn:Hsame; time_cbn;
      rewrite ?Nat2N.inj_add; try nia.
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_interval_congr_bits w a) as Hbits.
    pose proof (B0.pmeet_size w b (interval_congr (interval_word_clip w a))) as Hmeet.
    assert (Hderived : (N.of_nat (B0.psize w (interval_congr (interval_word_clip w a))) <=
      4 * N.of_nat (B0.psize w b))%N).
    { rewrite !B0.psize_congr, !Nat.pow_2_r.
      rewrite !Nat2N.inj_mul, !Nat2N.inj_add; nia. }
    rewrite !Nat2N.inj_add in Hmeet; nia.
  Qed.
  Lemma T_reduce_le : forall a b,
    (T_reduce (a, b) <= c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros a b.
    pose proof (T_to_left_le a b) as Hleft.
    pose proof (left_size a b) as Hsize.
    pose proof (left_frame (a, b)) as Hframe.
    destruct (to_left (a, b)) as [a' b'] eqn:Hstep.
    cbn [fst snd] in Hsize, Hframe; subst b'.
    pose proof (T_to_right_le a' b) as Hright.
    time_unfold T_reduce; cbn beta iota zeta; rewrite Hstep.
    unfold c_reduce; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma reduce_size_le : forall a b,
    (N.of_nat (A.size (fst (reduce (a, b))) + B.size (snd (reduce (a, b)))) <=
      c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros a b; unfold reduce; rewrite right_frame.
    pose proof (left_size a b) as Hleft.
    pose proof (left_frame (a, b)) as Hframe.
    destruct (to_left (a, b)) as [a' b'] eqn:Hstep.
    cbn [fst snd] in Hleft, Hframe; subst b'.
    pose proof (right_size a' b) as Hright.
    cbn [fst]; unfold c_reduce; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  Proof.
    exact reduce_sound.
  Qed.
  Lemma steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  Proof.
    exact reduce_lower.
  Qed.
  Lemma T_reduce_split : forall x, (T_reduce x <=
    k_exchange * (T_to_left x + T_to_right (to_left x) + 1))%N.
  Proof.
    intro x; unfold k_exchange; time_step.
  Qed.
  Lemma reduce_complexity :
    T_reduce (a, b) ∈ 𝑂(N.of_nat (A.size a + B.size b + 1)) for (a, b).
  Proof.
    exists c_reduce; intros [a b] _; cbn [fst snd].
    pose proof (T_reduce_le a b); nia.
  Qed.
End IntervalCongrT.

(** The interval payload stores its width and its raw endpoint bits, as the interval
    component's own plan law [psize_def] states. Without this pin a lawful payload can store the
    exchanged interval in quadratic space, as
    [ReducerIntervalSizeCounterexample.no_linear_precision_left_size] shows. *)
Module IntervalBitsT (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T)
    (A0 : INTERVAL_PAYLOAD_PINNED_T L T S
      with Definition psize :=
        fun (w : positive) (a : itv) => (Pos.to_nat w + interval_bits a + 1)%nat)
    (B0 : KNOWN_BITS_T L C)
    (A : VALUE_DOMAIN_T BitsLangT with Definition t := tagged A0.p
      with Definition size := tagged_size A0.psize
      with Definition leb := reducer_tagged_leb A0.pleb A0.pis_bot
      with Definition gamma := tagged_gamma L.is_word A0.pgamma)
    (B : VALUE_DOMAIN_T BitsLangT with Definition t := tagged B0.p
      with Definition size := tagged_size B0.psize
      with Definition leb := reducer_tagged_leb B0.pleb B0.pis_bot
      with Definition gamma := tagged_gamma L.is_word B0.pgamma)
    <: INTERVAL_BITS_ALL A B.
  Include IntervalBits L C T S A0 B0 A B.
  TimeFun to_left.
  TimeFun to_right.
  TimeFun reduce.
  Definition c_exchange : N := 1024 * (A0.c_payload + B0.c_payload + 1).
  Definition c_reduce : N := (c_exchange + 1) * (c_exchange + 1).
  Definition k_exchange : N := 1.
  Lemma T_to_left_le : forall a b, (T_to_left (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros [|w a|] [|v b|]; time_unfold T_to_left; time_cbn;
      unfold A.size, B.size, tagged_size, c_exchange, A0.psize;
      rewrite ?B0.psize_bits, ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (reducer_width_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; [|nia].
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_bits_interval_time w b) as Hhull.
    pose proof (reducer_bits_interval_bits w b) as Hbits.
    pose proof (A0.T_pmeet_le w a (bits_interval w b)) as Hmeet.
    unfold A0.psize in Hmeet.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_to_right_le : forall a b, (T_to_right (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros [|w a|] [|v b|]; time_unfold T_to_right; time_cbn;
      unfold A.size, B.size, tagged_size, c_exchange, A0.psize;
      rewrite ?B0.psize_bits, ?Nat2N.inj_add; time_cbn; try nia.
    pose proof (reducer_width_time w v) as Hwidth.
    destruct (Pos.eqb w v) eqn:Hsame; [|nia].
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_interval_prefix_time w a) as Hprefix.
    pose proof (reducer_interval_prefix_bits w a) as Hbits.
    pose proof (B0.T_pmeet_le w b (interval_prefix w a)) as Hmeet.
    rewrite !B0.psize_bits in Hmeet.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma left_size : forall a b,
    (N.of_nat (A.size (fst (to_left (a, b))) + B.size b) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros [|w a|] [|v b|]; unfold to_left; cbn [fst];
      unfold A.size, B.size, tagged_size, c_exchange, A0.psize;
      try (rewrite !Nat2N.inj_add; time_cbn; nia).
    destruct (Pos.eqb w v) eqn:Hsame; time_cbn;
      rewrite ?B0.psize_bits, ?Nat2N.inj_add; try nia.
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_bits_interval_bits w b) as Hbits.
    pose proof (A0.pmeet_size w a (bits_interval w b)) as Hmeet.
    unfold A0.psize in Hmeet.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma right_size : forall a b,
    (N.of_nat (A.size a + B.size (snd (to_right (a, b)))) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros [|w a|] [|v b|]; unfold to_right; cbn [snd];
      unfold A.size, B.size, tagged_size, c_exchange, A0.psize;
      try (rewrite !Nat2N.inj_add; time_cbn; nia).
    destruct (Pos.eqb w v) eqn:Hsame; time_cbn;
      rewrite ?B0.psize_bits, ?Nat2N.inj_add; try nia.
    apply Pos.eqb_eq in Hsame; subst v.
    pose proof (reducer_interval_prefix_bits w a) as Hbits.
    pose proof (B0.pmeet_size w b (interval_prefix w a)) as Hmeet.
    rewrite !B0.psize_bits in Hmeet.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_reduce_le : forall a b,
    (T_reduce (a, b) <= c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros a b.
    pose proof (T_to_left_le a b) as Hleft.
    pose proof (left_size a b) as Hsize.
    pose proof (left_frame (a, b)) as Hframe.
    destruct (to_left (a, b)) as [a' b'] eqn:Hstep.
    cbn [fst snd] in Hsize, Hframe; subst b'.
    pose proof (T_to_right_le a' b) as Hright.
    time_unfold T_reduce; cbn beta iota zeta; rewrite Hstep.
    unfold c_reduce; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma reduce_size_le : forall a b,
    (N.of_nat (A.size (fst (reduce (a, b))) + B.size (snd (reduce (a, b)))) <=
      c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros a b; unfold reduce; rewrite right_frame.
    pose proof (left_size a b) as Hleft.
    pose proof (left_frame (a, b)) as Hframe.
    destruct (to_left (a, b)) as [a' b'] eqn:Hstep.
    cbn [fst snd] in Hleft, Hframe; subst b'.
    pose proof (right_size a' b) as Hright.
    cbn [fst]; unfold c_reduce; rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  Proof.
    exact reduce_sound.
  Qed.
  Lemma steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  Proof.
    exact reduce_lower.
  Qed.
  Lemma T_reduce_split : forall x, (T_reduce x <=
    k_exchange * (T_to_left x + T_to_right (to_left x) + 1))%N.
  Proof.
    intro x; unfold k_exchange; time_step.
  Qed.
  Lemma reduce_complexity :
    T_reduce (a, b) ∈ 𝑂(N.of_nat (A.size a + B.size b + 1)) for (a, b).
  Proof.
    exists c_reduce; intros [a b] _; cbn [fst snd].
    pose proof (T_reduce_le a b); nia.
  Qed.
End IntervalBitsT.
