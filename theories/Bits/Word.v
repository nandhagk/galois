(** * Fixed-width words

    Words are integers reduced modulo a power of two.
    For example, wrapping 260 at width eight gives 4.

    Main results
    - [modulus_value] The modulus is two to the width, with [modulus_log2], [modulus_pos],
      [modulus_nonzero], [half_pos], [modulus_half] and [width_lt_modulus].
    - [wrap_mod] Wrapping is remainder modulo the word modulus, with [wrap_is_word], [wrap_id] and
      [wrap_wrap], and [signed_value] gives the signed reading after normalising.
    - [wrap_add] Wrapping commutes with the ring operations, with [wrap_0], [wrap_1], [wrap_opp],
      [wrap_sub], [wrap_mul], [wrap_add_modulus] and [wrap_narrow], and zero and one are words, as
      [zero_is_word] and [one_is_word] state.
    - [integer_size_le] The moduli, masks and raw integers have size bounded by the width, with
      [modulus_size_le] and [ones_size_le].
    - [modulus_time_le] The primitive clocks are linear or quadratic in the width and the raw
      integer size, with [pow_two_time_le], [ones_time_le], [wrap_time_le], [wrap_time_quad_le],
      [half_time_le], [signed_time_le], [signed_time_quad_le], [msb_time_le] and
      [msb_time_quad_le].
    - [modulus_complexity] Modulus construction is linear in the width, O(w).
    - [wrap_complexity] Wrapping has the linear class in the width and the raw integer size,
      O(w + |z|).

    Builds on: Stdlib integer arithmetic and Argent time derivation. *)

From Stdlib Require Import ZArith NArith Lia.
From Argent Require Import Time Tactics Std Complexity.
Import ComplexityNotations.

Open Scope Z_scope.

(** Widths are strictly positive binary integers. *)
Definition width := positive.

(** The modulus is the first integer outside the unsigned word range. *)
Definition modulus (w : width) : Z := 2 ^ Zpos w.

(** The word modulus is two raised to its positive bit width. *)
Theorem modulus_value : forall w, modulus w = 2 ^ Zpos w.
Proof.
  intro w. reflexivity.
Qed.

(** The binary logarithm of the word modulus is its bit width. *)
Theorem modulus_log2 : forall w, Z.log2 (modulus w) = Zpos w.
Proof.
  intro w. rewrite modulus_value. apply Z.log2_pow2. lia.
Qed.

(** Wrapping keeps the low bits of an integer by masking them. *)
Definition wrap (w : width) (z : Z) : Z := Z.land z (Z.ones (Zpos w)).

(** Wrapping is integer remainder modulo the word modulus for arbitrary integers. *)
Theorem wrap_mod : forall w z, wrap w z = z mod modulus w.
Proof.
  intros w z. unfold wrap, modulus. apply Z.land_ones. lia.
Qed.

(** An unsigned word lies between zero and the modulus. *)
Definition is_word (w : width) (z : Z) : Prop := 0 <= z < modulus w.

(** A dynamic word records its width and its integer value. *)
Definition word : Type := (width * Z)%type.

(** Half the modulus is the weight of the sign bit. *)
Definition half (w : width) : Z := 2 ^ (Zpos w - 1).

(** The most significant bit is read after wrapping. *)
Definition msb (w : width) (z : Z) : bool := Z.testbit (wrap w z) (Zpos w - 1).

(** The signed view interprets the highest bit as a negative weight. *)
Definition signed (w : width) (z : Z) : Z :=
  let z' := wrap w z in if z' <? half w then z' else z' - modulus w.

Module Pos.
  TimeFun Pos.testbit.
End Pos.

Module N.
  TimeFun N.testbit.
End N.

Module Z.
  TimeFun Z.ones.
  TimeFun Z.size_nat.
  TimeFun Z.odd.
  TimeFun Z.pow_pos.
  TimeFun Z.pow.
  TimeFun Z.testbit.
End Z.

TimeFun modulus.
TimeFun wrap.
TimeFun half.
TimeFun msb.
TimeFun signed.

(** Signed interpretation chooses its branch after normalizing an arbitrary integer. *)
Theorem signed_value : forall w x,
  signed w x = if wrap w x <? half w then wrap w x else wrap w x - modulus w.
Proof.
  intros w x. reflexivity.
Qed.

(** Every word modulus is positive. *)
Theorem modulus_pos : forall w, 0 < modulus w.
Proof.
  intros w. unfold modulus. apply Z.pow_pos_nonneg; lia.
Qed.

(** No word modulus is zero. *)
Theorem modulus_nonzero : forall w, modulus w <> 0.
Proof.
  intros w. pose proof (modulus_pos w). lia.
Qed.

(** The weight of the sign bit is positive. *)
Theorem half_pos : forall w, 0 < half w.
Proof.
  intros w. apply Z.pow_pos_nonneg; lia.
Qed.

(** The word modulus is twice the sign-bit weight. *)
Theorem modulus_half : forall w, modulus w = 2 * half w.
Proof.
  intros w. unfold modulus, half.
  replace (Zpos w) with (Z.succ (Zpos w - 1)) at 1 by lia.
  apply Z.pow_succ_r. lia.
Qed.

(** The bit width itself fits in an unsigned word. *)
Theorem width_lt_modulus : forall w, Zpos w < modulus w.
Proof.
  intros w. apply Z.pow_gt_lin_r; lia.
Qed.

(** Wrapping always produces an unsigned word. *)
Theorem wrap_is_word : forall w z, is_word w (wrap w z).
Proof.
  intros w z. rewrite wrap_mod. apply Z.mod_pos_bound. apply modulus_pos.
Qed.

(** Wrapping fixes every unsigned word. *)
Theorem wrap_id : forall w z, is_word w z -> wrap w z = z.
Proof.
  intros w z Hword. rewrite wrap_mod. apply Z.mod_small. exact Hword.
Qed.

(** Wrapping an already wrapped value has no effect. *)
Theorem wrap_wrap : forall w z, wrap w (wrap w z) = wrap w z.
Proof.
  intros w z. apply wrap_id. apply wrap_is_word.
Qed.

(** Zero fits in every word width. *)
Theorem zero_is_word : forall w, is_word w 0.
Proof.
  intros w. pose proof (modulus_pos w). unfold is_word. lia.
Qed.

(** One fits in every word width. *)
Theorem one_is_word : forall w, is_word w 1.
Proof.
  intros w. pose proof (width_lt_modulus w). unfold is_word. lia.
Qed.

(** Wrapping preserves zero. *)
Theorem wrap_0 : forall w, wrap w 0 = 0.
Proof.
  intros w. apply wrap_id. apply zero_is_word.
Qed.

(** Wrapping preserves one. *)
Theorem wrap_1 : forall w, wrap w 1 = 1.
Proof.
  intros w. apply wrap_id. apply one_is_word.
Qed.

(** Negation may normalize its operand before the final wrap. *)
Theorem wrap_opp : forall w x, wrap w (- wrap w x) = wrap w (- x).
Proof.
  intros w x. rewrite !wrap_mod. replace (- x) with (0 - x) by ring.
  rewrite Zminus_mod, Z.mod_0_l by apply modulus_nonzero.
  reflexivity.
Qed.

(** Subtraction may normalize both operands before the final wrap. *)
Theorem wrap_sub : forall w x y,
  wrap w (x - y) = wrap w (wrap w x - wrap w y).
Proof.
  intros w x y. rewrite !wrap_mod. apply Zminus_mod.
Qed.

(** Adding an integer multiple of the modulus does not change a wrapped value. *)
Theorem wrap_add_modulus : forall w x k, wrap w (x + k * modulus w) = wrap w x.
Proof.
  intros w x k. rewrite !wrap_mod. apply Z.mod_add. apply modulus_nonzero.
Qed.

(** Addition can wrap its operands before computing. *)
Theorem wrap_add : forall w x y,
  wrap w (x + y) = wrap w (wrap w x + wrap w y).
Proof.
  intros w x y. rewrite !wrap_mod. apply Z.add_mod. apply modulus_nonzero.
Qed.

(** Multiplication can wrap its operands before computing. *)
Theorem wrap_mul : forall w x y,
  wrap w (x * y) = wrap w (wrap w x * wrap w y).
Proof.
  intros w x y. rewrite !wrap_mod. apply Z.mul_mod. apply modulus_nonzero.
Qed.

(** Narrowing after a wider wrap keeps the same low bits. *)
Theorem wrap_narrow : forall w w2 z,
  (w <= w2)%positive -> wrap w (wrap w2 z) = wrap w z.
Proof.
  intros w w2 z Hwidth.
  assert (Hle : Zpos w <= Zpos w2) by (apply Pos2Z.pos_le_pos; exact Hwidth).
  rewrite !wrap_mod. unfold modulus.
  replace (Zpos w2) with (Zpos w + (Zpos w2 - Zpos w)) at 1 by lia.
  rewrite Z.pow_add_r by lia.
  apply Z.mod_mod_divide.
  exists (2 ^ (Zpos w2 - Zpos w)). ring.
Qed.

(** * Time contracts *)

(** A nonnegative integer below a power of two has at most that many bits. *)
Theorem integer_size_le : forall z n,
  (0 <= z < 2 ^ Z.of_nat n)%Z -> (Z.size_nat z <= n)%nat.
Proof.
  intros z n. destruct z as [|p|p]; intros Hrange; cbn [Z.size_nat]; try lia.
  apply Pos.size_nat_least. apply Nat2Z.inj_lt.
  rewrite positive_nat_Z, Nat2Z.inj_pow. exact (proj2 Hrange).
Qed.

(** The modulus needs one bit beyond the word width. *)
Theorem modulus_size_le : forall w, (Z.size_nat (modulus w) <= Pos.to_nat w + 1)%nat.
Proof.
  intro w. apply integer_size_le. split; [pose proof (modulus_pos w); lia|].
  unfold modulus. rewrite Nat2Z.inj_add, positive_nat_Z.
  apply Z.pow_lt_mono_r; lia.
Qed.

(** The width mask has no bits above the word width. *)
Theorem ones_size_le : forall w, (Z.size_nat (Z.ones (Zpos w)) <= Pos.to_nat w)%nat.
Proof.
  intro w. apply integer_size_le. rewrite positive_nat_Z, Z.ones_equiv, <- Z.sub_1_r.
  pose proof (modulus_pos w) as Hpos. unfold modulus in Hpos. lia.
Qed.

(** Doubling has constant cost, so a power of two is linear in its exponent. *)
Theorem pow_two_time_le : forall n, (0 <= n)%Z ->
  (Z.T_pow 2 n <= 5 * N.of_nat (Z.to_nat n) + 2)%N.
Proof.
  intros n Hnonnegative. destruct n as [|p|p]; [time_step| |lia].
  pose proof (Pos.T_iter_le (Z.mul 2) (fun x => Z.T_mul 2 x)
    (fun _ => True) 3 1 p (fun _ _ => I)
    (fun x _ => Z.T_mul_two_le x) I) as Hiter.
  time_unfold Z.T_pow. time_unfold Z.T_pow_pos.
  change (Z.to_nat (Zpos p)) with (Pos.to_nat p).
  rewrite positive_nat_N. time_cbn_all. lia.
Qed.

(** Constructing the word modulus takes linear time in the width. *)
Theorem modulus_time_le : forall w, (T_modulus w <= 8 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (pow_two_time_le (Zpos w) ltac:(lia)) as Hpow.
  time_unfold T_modulus. change (Z.to_nat (Zpos w)) with (Pos.to_nat w) in Hpow.
  rewrite Nat2N.inj_add. time_cbn_all. lia.
Qed.

(** Building the width mask takes linear time in the width. *)
Theorem ones_time_le : forall w, (Z.T_ones (Zpos w) <= 16 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (Z.T_shiftl_le 1 (Zpos w)) as Hshift.
  pose proof (Z.T_pred_le (Z.shiftl 1 (Zpos w))) as Hpred.
  assert (Hsize : (N.of_nat (Z.size_nat (Z.shiftl 1 (Zpos w))) <=
    N.of_nat (Pos.to_nat w + 1))%N).
  { apply time_of_nat_le. rewrite Z.shiftl_1_l. apply modulus_size_le. }
  time_unfold Z.T_ones. rewrite Nat2N.inj_add in *.
  time_cbn_all. rewrite positive_nat_N in *. nia.
Qed.

(** Wrapping reads the width mask and the raw integer, so it is linear in both sizes. *)
Theorem wrap_time_le : forall w z,
  (T_wrap w z <= 32 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z. pose proof (ones_time_le w) as Hmask.
  pose proof (Z.T_land_le z (Z.ones (Zpos w))) as Hland.
  pose proof (time_of_nat_le _ _ (ones_size_le w)) as Hsize.
  time_unfold T_wrap. rewrite ?Nat2N.inj_add in *. time_cbn_all. nia.
Qed.

(** Wrapping also fits the quadratic bound in the width and the raw integer size. *)
Theorem wrap_time_quad_le : forall w z,
  (T_wrap w z <= 64 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
Proof.
  intros w z. pose proof (wrap_time_le w z) as Hlinear.
  assert (Hsquare : (N.of_nat (Pos.to_nat w + Z.size_nat z + 1) <=
    N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N).
  { apply time_of_nat_le. rewrite Nat.pow_2_r. nia. }
  lia.
Qed.

(** Every normalized word fits its declared bit width. *)
Lemma word_size_le : forall w z, is_word w z -> (Z.size_nat z <= Pos.to_nat w)%nat.
Proof.
  intros w z Hword. apply integer_size_le.
  rewrite positive_nat_Z. exact Hword.
Qed.

(** Wrapping always produces a value within its declared bit width. *)
Lemma wrap_size_le : forall w z, (Z.size_nat (wrap w z) <= Pos.to_nat w)%nat.
Proof.
  intros w z. apply word_size_le, wrap_is_word.
Qed.

(** Half the modulus fits within the declared word width. *)
Lemma half_size_le : forall w, (Z.size_nat (half w) <= Pos.to_nat w)%nat.
Proof.
  intro w. apply word_size_le. unfold is_word.
  pose proof (half_pos w). pose proof (modulus_half w). lia.
Qed.

(** A symmetric power-of-two interval bounds the magnitude bit length. *)
Lemma integer_abs_size_le : forall z n,
  (- (2 ^ Z.of_nat n) < z < 2 ^ Z.of_nat n)%Z -> (Z.size_nat z <= n)%nat.
Proof.
  intros z n. destruct z as [|p|p]; intros Hrange; cbn [Z.size_nat]; try lia.
  - apply (integer_size_le (Zpos p) n). lia.
  - apply (integer_size_le (Zpos p) n). lia.
Qed.

(** Signed interpretation has at most the declared width many magnitude bits. *)
Lemma signed_size_le : forall w z, (Z.size_nat (signed w z) <= Pos.to_nat w)%nat.
Proof.
  intros w z. apply integer_abs_size_le. rewrite positive_nat_Z.
  fold (modulus w). pose proof (wrap_is_word w z) as Hrange.
  pose proof (half_pos w) as Hhalf. pose proof (modulus_half w) as Hmodulus.
  unfold signed, is_word in *.
  destruct (wrap w z <? half w) eqn:Hcompare.
  - apply Z.ltb_lt in Hcompare. lia.
  - apply Z.ltb_ge in Hcompare. lia.
Qed.

(** A positive integer's bit length does not exceed its numeric value. *)
Lemma positive_size_value : forall w, (Pos.size_nat w <= Pos.to_nat w)%nat.
Proof.
  intro w. induction w as [w IH|w IH|]; cbn [Pos.size_nat];
    rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
Qed.

(** The half modulus is linear in the width. *)
Theorem half_time_le : forall w,
  (T_half w <= 32 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (pow_two_time_le (Zpos w - 1) ltac:(lia)) as Hpow.
  pose proof (Z.T_sub_le (Zpos w) 1) as Hsub.
  assert (Hwidth : (N.of_nat (Pos.size_nat w) <= N.of_nat (Pos.to_nat w))%N).
  { apply time_of_nat_le. apply positive_size_value. }
  assert (Hexponent : (N.of_nat (Z.to_nat (Zpos w - 1)) <=
    N.of_nat (Pos.to_nat w))%N).
  { apply time_of_nat_le. apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia. rewrite positive_nat_Z. lia. }
  time_unfold T_half. change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in Hsub.
  rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
Qed.

(** Signed reading is at most quadratic in the width and the raw integer size. *)
Theorem signed_time_quad_le : forall w z,
  (T_signed w z <= 128 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
Proof.
  intros w z. pose proof (wrap_time_quad_le w z) as Hwrap.
  pose proof (half_time_le w) as Hhalf.
  pose proof (modulus_time_le w) as Hmodulus.
  pose proof (Z.T_ltb_le (wrap w z) (half w)) as Hcompare.
  pose proof (Z.T_sub_le (wrap w z) (modulus w)) as Hsubtract.
  pose proof (time_of_nat_le _ _ (wrap_size_le w z)) as Hsize.
  pose proof (time_of_nat_le _ _ (modulus_size_le w)) as Hmodsize.
  time_unfold T_signed. destruct (wrap w z <? half w)%Z;
    rewrite !Nat2N.inj_add, !Nat2N.inj_pow in *; time_cbn_all; nia.
Qed.

(** Bit lookup reads the positive input's bits while decrementing its index. *)
Lemma positive_testbit_time_bound : forall p n,
  (Pos.T_testbit p n <=
    N.of_nat ((Pos.size_nat p + 1) * (N.size_nat n + 2)))%N.
Proof.
  intro p. induction p as [p IH|p IH|]; intros [|n];
    time_unfold Pos.T_testbit; cbn [Pos.size_nat N.size_nat].
  all: try (specialize (IH (Pos.pred_N n)); pose proof (Pos.T_pred_N_le n) as Hpred;
    assert (Hsize : (N.of_nat (N.size_nat (Pos.pred_N n)) <=
      N.of_nat (Pos.size_nat n))%N) by
      (apply time_of_nat_le; apply N.size_nat_pred_N)).
  all: rewrite ?Nat2N.inj_mul, ?Nat2N.inj_add in *; time_cbn_all; nia.
Qed.

(** Nonnegative integer bit lookup is bounded by the input and index bit lengths. *)
Lemma integer_testbit_time_bound : forall a n, (0 <= a)%Z -> (0 <= n)%Z ->
  (Z.T_testbit a n <=
    4 * N.of_nat ((Z.size_nat a + 1) * (Z.size_nat n + 1)))%N.
Proof.
  intros a n Ha Hn. destruct a as [|a|a], n as [|n|n]; try lia;
    time_unfold Z.T_testbit; cbn [Z.size_nat]; time_simpl; time_cbn; try lia.
  pose proof (positive_testbit_time_bound a (Npos n)) as Hbit.
  cbn [N.size_nat] in Hbit.
  rewrite ?Nat2N.inj_mul, ?Nat2N.inj_add in *; time_cbn_all; nia.
Qed.

(** Reading the sign bit is at most quadratic in the width and the raw integer size. *)
Theorem msb_time_quad_le : forall w z,
  (T_msb w z <= 128 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
Proof.
  intros w z. pose proof (wrap_time_quad_le w z) as Hwrap.
  pose proof (Z.T_sub_le (Zpos w) 1) as Hsubtract.
  pose proof (integer_testbit_time_bound (wrap w z) (Zpos w - 1)
    (proj1 (wrap_is_word w z)) ltac:(lia)) as Hbit.
  pose proof (time_of_nat_le _ _ (wrap_size_le w z)) as Hsize.
  pose proof (time_of_nat_le _ _ (positive_size_value w)) as Hwidth.
  assert (Hindex : (N.of_nat (Z.size_nat (Zpos w - 1)) <=
    N.of_nat (Pos.to_nat w))%N).
  { apply time_of_nat_le. eapply Nat.le_trans.
    - apply (Z.size_nat_mono (Zpos w - 1) (Zpos w)). lia.
    - apply positive_size_value. }
  time_unfold T_msb. change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in Hsubtract.
  rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_pow in *.
  time_cbn_all. nia.
Qed.

(** Modulus construction is linear in the width. *)
Theorem modulus_complexity :
  T_modulus w ∈ 𝑂(N.of_nat (Pos.to_nat w)) for w.
Proof.
  apply bigO_intro with (c := 8%N). intros w _.
  pose proof (modulus_time_le w) as Hmodulus.
  rewrite Nat2N.inj_add in Hmodulus. time_cbn_all. lia.
Qed.

(** Wrapping has the linear class in the width and the raw integer size. *)
Theorem wrap_complexity :
  T_wrap w z ∈ 𝑂(N.of_nat (Pos.to_nat w + Z.size_nat z)) for (w, z).
Proof.
  apply bigO_intro with (c := 32%N). intros [w z] _. cbn [fst snd].
  pose proof (wrap_time_le w z) as Hwrap.
  rewrite Nat2N.inj_add in Hwrap. time_cbn_all. lia.
Qed.

(** Signed reading is linear in the width and the raw integer size. *)
Theorem signed_time_le : forall w z,
  (T_signed w z <= 128 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z. pose proof (wrap_time_le w z) as Hwrap.
  pose proof (half_time_le w) as Hhalf.
  pose proof (modulus_time_le w) as Hmodulus.
  pose proof (Z.T_ltb_le (wrap w z) (half w)) as Hcompare.
  pose proof (Z.T_sub_le (wrap w z) (modulus w)) as Hsubtract.
  pose proof (time_of_nat_le _ _ (wrap_size_le w z)) as Hsize.
  pose proof (time_of_nat_le _ _ (modulus_size_le w)) as Hmodsize.
  time_unfold T_signed. destruct (wrap w z <? half w)%Z;
    rewrite !Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** Reading the sign bit costs the word size times the bit length of the width. *)
Theorem msb_time_le : forall w z,
  (T_msb w z <= 128 * N.of_nat
    ((Pos.to_nat w + Z.size_nat z + 1) * (Pos.size_nat w + 1)))%N.
Proof.
  intros w z. pose proof (wrap_time_le w z) as Hwrap.
  pose proof (Z.T_sub_le (Zpos w) 1) as Hsubtract.
  pose proof (integer_testbit_time_bound (wrap w z) (Zpos w - 1)
    (proj1 (wrap_is_word w z)) ltac:(lia)) as Hbit.
  pose proof (time_of_nat_le _ _ (wrap_size_le w z)) as Hsize.
  assert (Hindex : (N.of_nat (Z.size_nat (Zpos w - 1)) <=
    N.of_nat (Pos.size_nat w))%N).
  { apply time_of_nat_le. apply (Z.size_nat_mono (Zpos w - 1) (Zpos w)). lia. }
  time_unfold T_msb. change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in Hsubtract.
  rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *.
  time_cbn_all. nia.
Qed.
