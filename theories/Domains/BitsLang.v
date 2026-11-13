(** * Bit-vector language

    Operators evaluate fixed-width words and literals retain their widths.
    For example, an eight-bit literal is wrapped before evaluation returns it.
    Builds on: LangSig and bit-vector operations. *)

From Stdlib Require Import List ZArith NArith Bool Lia Ring.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word Fun Testbit Op Arith.
From Galois.Domains Require Import LangSig WordSig.
Import List.ListNotations.

Module WordAlgebra.
  Local Open Scope Z_scope.

  (** Bitwise conjunction with zero returns zero. *)
  Lemma const_zero_bits : forall w x, is_word w x -> wand w 0 x = 0.
  Proof.
    intros w x Hx. apply (word_ext w); [apply wand_is_word|apply zero_is_word|].
    intros i Hi. rewrite testbit_wand by (auto using zero_is_word; lia).
    now rewrite !Z.bits_0.
  Qed.

  (** Bitwise disjunction with the all-ones word returns that word. *)
  Lemma const_ones_bits : forall w x,
    is_word w x -> wor w (modulus w - 1) x = modulus w - 1.
  Proof.
    intros w x Hx. apply (word_ext w); [apply wor_is_word|apply ones_is_word|].
    intros i Hi. rewrite testbit_wor by (auto using ones_is_word; lia).
    rewrite all_ones_bits by exact Hi.
    destruct (i <? Zpos w) eqn:Hlow; cbn; [reflexivity|].
    apply Z.ltb_ge in Hlow. exact (word_bits_high w x i Hx Hlow).
  Qed.

  (** Multiplication, shifts and unsigned remainder preserve a zero left operand. *)
  Lemma const_zero_ops : forall w y, is_word w y ->
    wmul w 0 y = 0 /\ wshl w 0 y = 0 /\ wlshr w 0 y = 0 /\
    washr w 0 y = 0 /\ wurem w 0 y = 0.
  Proof.
    intros w y Hy.
    assert (Hpow : 2 ^ wrap w y <> 0).
    { pose proof (wrap_is_word w y) as [Hnonnegative Hupper].
      apply Z.pow_nonzero; lia. }
    rewrite wmul_value, wshl_value, wlshr_value, washr_value, wurem_mod.
    rewrite wrap_0, msb_zero, signed_zero, Z.mul_0_l, wrap_0.
    rewrite Z.div_0_l by exact Hpow. rewrite wrap_0.
    split; [reflexivity|].
    destruct (Zpos w <=? wrap w y); cbn; repeat split; try reflexivity.
    all: destruct (Z.eq_dec (wrap w y) 0) as [-> | Hz];
      [reflexivity|now apply Z.mod_0_l].
  Qed.

  (** Adding and then subtracting the same operand recovers a word. *)
  Lemma const_add_inverse : forall w x y,
    is_word w x -> wsub w (wadd w x y) y = x.
  Proof.
    intros w x y Hx. rewrite wsub_value, wadd_value, wrap_sub, wrap_wrap, <- wrap_sub.
    replace (x + y - y) with x by ring. now apply wrap_id.
  Qed.

  (** Adding back a subtracted operand recovers a word. *)
  Lemma const_sub_inverse_left : forall w x y,
    is_word w x -> wadd w (wsub w x y) y = x.
  Proof.
    intros w x y Hx. rewrite wadd_value, wsub_value, wrap_add, wrap_wrap, <- wrap_add.
    replace (x - y + y) with x by ring. now apply wrap_id.
  Qed.

  (** Subtracting the difference recovers the right operand. *)
  Lemma const_sub_inverse_right : forall w x y,
    is_word w y -> wsub w x (wsub w x y) = y.
  Proof.
    intros w x y Hy. rewrite !wsub_value, wrap_sub, wrap_wrap, <- wrap_sub.
    replace (x - (x - y)) with y by ring. now apply wrap_id.
  Qed.

  (** Applying xor with the same word twice recovers the first word. *)
  Lemma const_xor_inverse : forall w x y,
    is_word w x -> wxor w (wxor w x y) y = x.
  Proof.
    intros w x y Hx. rewrite <- wxor_assoc, wxor_self.
    apply (word_ext w); [apply wxor_is_word|exact Hx|].
    intros i Hi. rewrite testbit_wxor by (auto using zero_is_word; lia).
    now rewrite Z.bits_0, xorb_false_r.
  Qed.

  (** Word negation is an involution on normalized words. *)
  Lemma const_neg_inverse : forall w x,
    is_word w x -> wneg w (wneg w x) = x.
  Proof.
    intros w x Hx. rewrite !wneg_value, wrap_opp.
    replace (- - x) with x by ring. now apply wrap_id.
  Qed.

End WordAlgebra.

Module WordTime.

  (** A nonnegative integer below a power of two has at most that many bits. *)
  Lemma integer_size_bound z n :
    (0 <= z < 2 ^ Z.of_nat n)%Z -> (Z.size_nat z <= n)%nat.
  Proof.
    destruct z as [|p|p]; intros Hrange; cbn [Z.size_nat]; try lia.
    apply Pos.size_nat_least. apply Nat2Z.inj_lt.
    rewrite positive_nat_Z, Nat2Z.inj_pow. exact (proj2 Hrange).
  Qed.

  (** Every normalized word fits its declared bit width. *)
  Lemma word_size_bound w z : is_word w z -> (Z.size_nat z <= Pos.to_nat w)%nat.
  Proof.
    intros Hword. apply integer_size_bound.
    rewrite positive_nat_Z. exact Hword.
  Qed.

  (** Wrapping always produces a word within its declared bit width. *)
  Lemma word_wrap_size_bound w z : (Z.size_nat (wrap w z) <= Pos.to_nat w)%nat.
  Proof.
    apply word_size_bound, wrap_is_word.
  Qed.

  (** The modulus needs one bit beyond the word width. *)
  Lemma word_modulus_size_bound w : (Z.size_nat (modulus w) <= Pos.to_nat w + 1)%nat.
  Proof.
    apply integer_size_bound. split; [pose proof (modulus_pos w); lia|].
    unfold modulus. rewrite Nat2Z.inj_add, positive_nat_Z.
    apply Z.pow_lt_mono_r; lia.
  Qed.

  (** Half the modulus fits within the declared word width. *)
  Lemma word_half_size_bound w : (Z.size_nat (half w) <= Pos.to_nat w)%nat.
  Proof.
    apply word_size_bound. unfold is_word.
    pose proof (half_pos w). pose proof (modulus_half w). lia.
  Qed.

  (** A symmetric power-of-two interval also bounds signed magnitudes. *)
  Lemma integer_abs_size_bound z n :
    (- (2 ^ Z.of_nat n) < z < 2 ^ Z.of_nat n)%Z -> (Z.size_nat z <= n)%nat.
  Proof.
    destruct z as [|p|p]; intros Hrange; cbn [Z.size_nat]; try lia.
    - apply (integer_size_bound (Zpos p) n). lia.
    - apply (integer_size_bound (Zpos p) n). lia.
  Qed.

  (** Signed interpretations have at most the declared width many magnitude bits. *)
  Lemma word_signed_size_bound w z : (Z.size_nat (signed w z) <= Pos.to_nat w)%nat.
  Proof.
    apply integer_abs_size_bound. rewrite positive_nat_Z.
    fold (modulus w). pose proof (signed_range w z).
    pose proof (half_pos w). pose proof (modulus_half w). lia.
  Qed.

  (** Integer negation preserves magnitude bit length. *)
  Lemma integer_opp_size z : Z.size_nat (- z) = Z.size_nat z.
  Proof.
    destruct z; reflexivity.
  Qed.

  (** A positive integer's bit length does not exceed its numeric value. *)
  Lemma positive_size_value w : (Pos.size_nat w <= Pos.to_nat w)%nat.
  Proof.
    induction w as [w IH|w IH|]; cbn [Pos.size_nat];
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
  Qed.

  (** Doubling has constant cost, so constructing a power of two is linear in its exponent. *)
  Lemma word_pow_two_time_bound n : (0 <= n)%Z ->
    (Word.Z.T_pow 2 n <= 5 * N.of_nat (Z.to_nat n) + 2)%N.
  Proof.
    intros Hnonnegative. destruct n as [|p|p]; [time_step| |lia].
    pose proof (Pos.T_iter_le (Z.mul 2) (fun x => Z.T_mul 2 x)
      (fun _ => True) 3 1 p (fun _ _ => I)
      (fun x _ => Z.T_mul_two_le x) I) as Hiter.
    time_unfold Word.Z.T_pow. time_unfold Word.Z.T_pow_pos.
    change (Z.to_nat (Zpos p)) with (Pos.to_nat p).
    rewrite positive_nat_N. time_cbn_all. lia.
  Qed.

  (** Constructing the word modulus takes linear time in the width. *)
  Lemma word_modulus_time_bound w :
    (T_modulus w <= 8 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    pose proof (word_pow_two_time_bound (Zpos w) ltac:(lia)) as Hpow.
    time_unfold T_modulus. change (Z.to_nat (Zpos w)) with (Pos.to_nat w) in Hpow.
    rewrite Nat2N.inj_add. time_cbn_all. lia.
  Qed.

  (** The half modulus charges subtraction of the width and a power-of-two construction. *)
  Lemma word_half_time_bound w :
    (T_half w <= 32 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    pose proof (word_pow_two_time_bound (Zpos w - 1) ltac:(lia)) as Hpow.
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

  (** Modular wrapping charges the width and the raw integer's bit length quadratically. *)
  Lemma word_wrap_time_bound w z :
    (T_wrap w z <= 64 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    pose proof (word_modulus_time_bound w) as Hmodulus.
    pose proof (Z.T_modulo_le z (modulus w)) as Hremainder.
    assert (Hsize : (N.of_nat (Z.size_nat (modulus w)) <=
      N.of_nat (Pos.to_nat w + 1))%N).
    { apply time_of_nat_le. apply word_modulus_size_bound. }
    time_unfold T_wrap. rewrite !Nat2N.inj_add, !Nat2N.inj_pow in *.
    time_cbn_all. nia.
  Qed.

  (** Signed interpretation adds only linear work to modular wrapping. *)
  Lemma word_signed_time_bound w z :
    (T_signed w z <= 128 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w z) as Hwrap.
    pose proof (word_half_time_bound w) as Hhalf.
    pose proof (word_modulus_time_bound w) as Hmodulus.
    pose proof (Z.T_ltb_le (wrap w z) (half w)) as Hcompare.
    pose proof (Z.T_sub_le (wrap w z) (modulus w)) as Hsubtract.
    assert (Hsize : (N.of_nat (Z.size_nat (wrap w z)) <=
      N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. apply word_wrap_size_bound. }
    assert (Hmodsize : (N.of_nat (Z.size_nat (modulus w)) <=
      N.of_nat (Pos.to_nat w + 1))%N).
    { apply time_of_nat_le. apply word_modulus_size_bound. }
    time_unfold T_signed. destruct (wrap w z <? half w)%Z;
      rewrite !Nat2N.inj_add, !Nat2N.inj_pow in *; time_cbn_all; nia.
  Qed.

  (** Bit lookup traverses at most the positive input's bits while decrementing its index. *)
  Lemma positive_testbit_time_bound p n :
    (Word.Pos.T_testbit p n <=
      N.of_nat ((Pos.size_nat p + 1) * (N.size_nat n + 2)))%N.
  Proof.
    revert n. induction p as [p IH|p IH|]; intros [|n];
      time_unfold Word.Pos.T_testbit; cbn [Pos.size_nat N.size_nat].
    all: try (specialize (IH (Pos.pred_N n)); pose proof (Pos.T_pred_N_le n) as Hpred;
      assert (Hsize : (N.of_nat (N.size_nat (Pos.pred_N n)) <=
        N.of_nat (Pos.size_nat n))%N) by
        (apply time_of_nat_le; apply N.size_nat_pred_N)).
    all: rewrite ?Nat2N.inj_mul, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Nonnegative integer bit lookup is quadratic in input and index bit lengths. *)
  Lemma integer_testbit_time_bound a n : (0 <= a)%Z -> (0 <= n)%Z ->
    (Word.Z.T_testbit a n <=
      4 * N.of_nat ((Z.size_nat a + 1) * (Z.size_nat n + 1)))%N.
  Proof.
    intros Ha Hn. destruct a as [|a|a], n as [|n|n]; try lia;
      time_unfold Word.Z.T_testbit; cbn [Z.size_nat]; time_simpl; time_cbn; try lia.
    pose proof (positive_testbit_time_bound a (Npos n)) as Hbit.
    cbn [N.size_nat] in Hbit.
    rewrite ?Nat2N.inj_mul, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Reading the sign bit charges wrapping and a width-bounded bit lookup. *)
  Lemma word_msb_time_bound w z :
    (T_msb w z <= 128 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w z) as Hwrap.
    pose proof (Z.T_sub_le (Zpos w) 1) as Hsubtract.
    pose proof (integer_testbit_time_bound (wrap w z) (Zpos w - 1)
      (proj1 (wrap_is_word w z)) ltac:(lia)) as Hbit.
    assert (Hsize : (N.of_nat (Z.size_nat (wrap w z)) <=
      N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. apply word_wrap_size_bound. }
    assert (Hwidth : (N.of_nat (Pos.size_nat w) <= N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. apply positive_size_value. }
    assert (Hindex : (N.of_nat (Z.size_nat (Zpos w - 1)) <=
      N.of_nat (Pos.to_nat w))%N).
    { apply time_of_nat_le. eapply Nat.le_trans.
      - apply (Z.size_nat_mono (Zpos w - 1) (Zpos w)). lia.
      - apply positive_size_value. }
    time_unfold T_msb. change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in Hsubtract.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_pow in *.
    time_cbn_all. nia.
  Qed.

  (** The binary size representation agrees with the natural bit count. *)
  Lemma positive_size_correct p : Pos.to_nat (Pos.size p) = Pos.size_nat p.
  Proof.
    induction p as [p IH|p IH|]; cbn [Pos.size Pos.size_nat];
      rewrite ?Pos2Nat.inj_succ, ?IH; reflexivity.
  Qed.

  (** Constructing the binary bit count costs at most a quadratic bit budget. *)
  Lemma positive_size_time_bound p :
    (Fun.Pos.T_size p <= N.of_nat ((Pos.size_nat p + 1) ^ 2))%N.
  Proof.
    induction p as [p IH|p IH|]; time_unfold Fun.Pos.T_size; cbn [Pos.size_nat].
    all: try (pose proof (Pos.T_succ_le (Pos.size p)) as Hsucc;
      pose proof (positive_size_value (Pos.size p)) as Hsize;
      rewrite positive_size_correct in Hsize;
      apply time_of_nat_le in Hsize).
    all: rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** A binary logarithm cannot increase magnitude bit length. *)
  Lemma integer_log2_size z : (Z.size_nat (Z.log2 z) <= Z.size_nat z)%nat.
  Proof.
    destruct z as [|[p|p|]|p]; cbn [Z.log2 Z.size_nat Pos.size_nat]; try lia.
    all: pose proof (positive_size_value (Pos.size p)) as Hsize;
      rewrite positive_size_correct in Hsize; lia.
  Qed.

  (** Integer logarithms construct a binary bit count. *)
  Lemma integer_log2_time_bound z :
    (Fun.Z.T_log2 z <= 2 * N.of_nat ((Z.size_nat z + 1) ^ 2))%N.
  Proof.
    destruct z as [|[p|p|]|p]; time_unfold Fun.Z.T_log2;
      cbn [Z.size_nat Pos.size_nat].
    all: try pose proof (positive_size_time_bound p) as Hsize.
    all: rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** A positive integer has no more set bits than its numeric value. *)
  Lemma positive_popcount_bound p : (0 <= popcount_pos p <= Zpos p)%Z.
  Proof.
    induction p as [p IH|p IH|].
    - change (0 <= 1 + popcount_pos p <= 2 * Zpos p + 1)%Z. lia.
    - change (0 <= popcount_pos p <= 2 * Zpos p)%Z. lia.
    - cbn. lia.
  Qed.

  (** Population counts fit within the input's magnitude bit length. *)
  Lemma positive_popcount_size p : (Z.size_nat (popcount_pos p) <= Pos.size_nat p)%nat.
  Proof.
    apply (Z.size_nat_mono (popcount_pos p) (Zpos p)). apply positive_popcount_bound.
  Qed.

  (** Counting set bits traverses the input and increments a bounded counter. *)
  Lemma positive_popcount_time_bound p :
    (T_popcount_pos p <= 8 * N.of_nat ((Pos.size_nat p + 1) ^ 2))%N.
  Proof.
    induction p as [p IH|p IH|]; time_unfold T_popcount_pos; cbn [Pos.size_nat].
    all: try (pose proof (Z.T_add_le 1 (popcount_pos p)) as Hadd;
      pose proof (time_of_nat_le _ _ (positive_popcount_size p)) as Hsize).
    all: rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Integer population count adds a constant dispatch cost. *)
  Lemma integer_popcount_time_bound z :
    (T_popcount z <= 16 * N.of_nat ((Z.size_nat z + 1) ^ 2))%N.
  Proof.
    destruct z as [|p|p]; time_unfold T_popcount; cbn [Z.size_nat].
    all: try pose proof (positive_popcount_time_bound p) as Hcount.
    all: rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Conjunction with a normalized word cannot introduce higher bits. *)
  Lemma integer_land_size_bound w x y : is_word w x ->
    (Z.size_nat (Z.land x y) <= Pos.to_nat w)%nat.
  Proof.
    intros Hx. apply word_size_bound, word_of_bits. intros i Hi.
    rewrite Z.land_spec, (word_bits_high w x i Hx Hi). reflexivity.
  Qed.

  (** Leading-zero count charges wrapping and two bounded integer subtractions. *)
  Lemma word_clz_time_bound w x :
    (T_wclz w x <= 256 * N.of_nat ((Pos.to_nat w + Z.size_nat x + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w x) as Hwrap.
    pose proof (Z.T_eqb_le (wrap w x) 0) as Heq.
    pose proof (Z.T_sub_le (Zpos w) 1) as Hsubwidth.
    pose proof (integer_log2_time_bound (wrap w x)) as Hlog.
    pose proof (Z.T_sub_le (Zpos w - 1) (Z.log2 (wrap w x))) as Hsub.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsize.
    pose proof (time_of_nat_le _ _ (positive_size_value w)) as Hwidth.
    pose proof (time_of_nat_le _ _ (integer_log2_size (wrap w x))) as Hlogsize.
    pose proof (time_of_nat_le _ _
      (Z.size_nat_mono (Zpos w - 1) (Zpos w) ltac:(lia))) as Hsubsize.
    time_unfold T_wclz. destruct (wrap w x =? 0)%Z;
      change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in *;
      rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Trailing-zero count forms the low bit and computes its logarithm. *)
  Lemma word_ctz_time_bound w x :
    (T_wctz w x <= 256 * N.of_nat ((Pos.to_nat w + Z.size_nat x + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w x) as Hwrap.
    pose proof (Z.T_eqb_le (wrap w x) 0) as Heq.
    pose proof (Z.T_opp_le (wrap w x)) as Hopp.
    pose proof (Z.T_land_le (wrap w x) (- wrap w x)) as Hland.
    pose proof (integer_log2_time_bound (Z.land (wrap w x) (- wrap w x))) as Hlog.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsize.
    pose proof (time_of_nat_le _ _
      (integer_land_size_bound w (wrap w x) (- wrap w x) (wrap_is_word w x))) as Hlandsize.
    rewrite integer_opp_size in Hland.
    time_unfold T_wctz. destruct (wrap w x =? 0)%Z;
      rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Word population count charges wrapping and traversal of at most the declared width. *)
  Lemma word_popcount_time_bound w x :
    (T_wpopcnt w x <= 128 * N.of_nat ((Pos.to_nat w + Z.size_nat x + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w x) as Hwrap.
    pose proof (integer_popcount_time_bound (wrap w x)) as Hcount.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsize.
    time_unfold T_wpopcnt.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Magnitude bit length gives a strict symmetric power-of-two bound. *)
  Lemma integer_magnitude_bound z :
    (- (2 ^ Z.of_nat (Z.size_nat z)) < z < 2 ^ Z.of_nat (Z.size_nat z))%Z.
  Proof.
    destruct z as [|p|p]; [cbn; lia| |]; cbn [Z.size_nat];
      pose proof (Pos.size_nat_upper p) as Hupper;
      apply Nat2Z.inj_lt in Hupper;
      rewrite positive_nat_Z, Nat2Z.inj_pow in Hupper; lia.
  Qed.

  (** Addition increases the combined magnitude budget by at most one bit. *)
  Lemma integer_add_size x y :
    (Z.size_nat (x + y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
  Proof.
    apply integer_abs_size_bound.
    pose proof (integer_magnitude_bound x) as Hx.
    pose proof (integer_magnitude_bound y) as Hy.
    assert (Hxp : (0 < 2 ^ Z.of_nat (Z.size_nat x))%Z) by
      (apply Z.pow_pos_nonneg; lia).
    assert (Hyp : (0 < 2 ^ Z.of_nat (Z.size_nat y))%Z) by
      (apply Z.pow_pos_nonneg; lia).
    rewrite !Nat2Z.inj_add. change (Z.of_nat 1%nat) with 1%Z.
    rewrite !Z.pow_add_r by lia. rewrite Z.pow_1_r. nia.
  Qed.

  (** Subtraction uses the same combined magnitude budget as addition. *)
  Lemma integer_sub_size x y :
    (Z.size_nat (x - y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
  Proof.
    pose proof (integer_add_size x (- y)) as Hsize.
    rewrite integer_opp_size in Hsize. exact Hsize.
  Qed.

  (** A product fits within the sum of its factors' magnitude bit lengths. *)
  Lemma integer_mul_size x y :
    (Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y)%nat.
  Proof.
    destruct x, y; cbn [Z.mul Z.size_nat]; try lia; apply Pos.size_nat_mul.
  Qed.

  (** Complement charges wrapping and two width-bounded subtractions. *)
  Lemma word_not_time_bound w x :
    (T_wnot w x <= 128 * N.of_nat ((Pos.to_nat w + Z.size_nat x + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w x) as Hwrap.
    pose proof (word_modulus_time_bound w) as Hmodulus.
    pose proof (Z.T_sub_le (modulus w) 1) as Hones.
    pose proof (Z.T_sub_le (modulus w - 1) (wrap w x)) as Hsub.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsize.
    pose proof (time_of_nat_le _ _ (word_modulus_size_bound w)) as Hmodsize.
    pose proof (time_of_nat_le _ _
      (Z.size_nat_mono (modulus w - 1) (modulus w)
        ltac:(pose proof (modulus_pos w); lia))) as Honessize.
    time_unfold T_wnot.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Modular negation preserves the raw magnitude budget before wrapping. *)
  Lemma word_neg_time_bound w x :
    (T_wneg w x <= 128 * N.of_nat ((Pos.to_nat w + Z.size_nat x + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w (- x)) as Hwrap.
    pose proof (Z.T_opp_le x) as Hopp. rewrite integer_opp_size in Hwrap.
    time_unfold T_wneg.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Every unary operator charges a quadratic width and raw-input budget. *)
  Lemma word_unary_time_bound tag w x :
    (T_eval_unary_tag tag w x <=
      512 * N.of_nat ((Pos.to_nat w + Z.size_nat x + 1) ^ 2))%N.
  Proof.
    pose proof (word_not_time_bound w x) as Hnot.
    pose proof (word_neg_time_bound w x) as Hneg.
    pose proof (word_clz_time_bound w x) as Hclz.
    pose proof (word_ctz_time_bound w x) as Hctz.
    pose proof (word_popcount_time_bound w x) as Hcount.
    destruct tag; time_unfold T_eval_unary_tag;
      rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Modular addition charges a combined operand bit budget. *)
  Lemma word_add_time_bound w x y :
    (T_wadd w x y <=
      512 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    pose proof (Z.T_add_le x y) as Hadd.
    pose proof (word_wrap_time_bound w (x + y)) as Hwrap.
    pose proof (time_of_nat_le _ _ (integer_add_size x y)) as Hsize.
    time_unfold T_wadd.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Modular subtraction charges a combined operand bit budget. *)
  Lemma word_sub_time_bound w x y :
    (T_wsub w x y <=
      512 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    pose proof (Z.T_sub_le x y) as Hsub.
    pose proof (word_wrap_time_bound w (x - y)) as Hwrap.
    pose proof (time_of_nat_le _ _ (integer_sub_size x y)) as Hsize.
    time_unfold T_wsub.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Modular multiplication charges the product computation and its bounded result size. *)
  Lemma word_mul_time_bound w x y :
    (T_wmul w x y <=
      128 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    pose proof (Z.T_mul_le x y) as Hmul.
    pose proof (word_wrap_time_bound w (x * y)) as Hwrap.
    pose proof (time_of_nat_le _ _ (integer_mul_size x y)) as Hsize.
    time_unfold T_wmul.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Bitwise conjunction normalizes both inputs before its linear bit traversal. *)
  Lemma word_and_time_bound w x y :
    (T_wand w x y <=
      256 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w x) as Hx.
    pose proof (word_wrap_time_bound w y) as Hy.
    pose proof (Z.T_land_le (wrap w x) (wrap w y)) as Hland.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsx.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w y)) as Hsy.
    time_unfold T_wand.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Bitwise disjunction normalizes both inputs before its linear bit traversal. *)
  Lemma word_or_time_bound w x y :
    (T_wor w x y <=
      256 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w x) as Hx.
    pose proof (word_wrap_time_bound w y) as Hy.
    pose proof (Z.T_lor_le (wrap w x) (wrap w y)) as Hlor.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsx.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w y)) as Hsy.
    time_unfold T_wor.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Exclusive disjunction normalizes both inputs before its linear bit traversal. *)
  Lemma word_xor_time_bound w x y :
    (T_wxor w x y <=
      256 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    pose proof (word_wrap_time_bound w x) as Hx.
    pose proof (word_wrap_time_bound w y) as Hy.
    pose proof (Z.T_lxor_le (wrap w x) (wrap w y)) as Hlxor.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsx.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w y)) as Hsy.
    time_unfold T_wxor.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Division of normalized words uses a quadratic width budget. *)
  Lemma integer_div_word_time_bound w a b : is_word w a -> is_word w b ->
    (Z.T_div a b <= 64 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Ha Hb. pose proof (Z.T_div_le a b) as Hdiv.
    pose proof (time_of_nat_le _ _ (word_size_bound w a Ha)) as Hsa.
    pose proof (time_of_nat_le _ _ (word_size_bound w b Hb)) as Hsb.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Remainder of normalized words uses the same quadratic width budget. *)
  Lemma integer_mod_word_time_bound w a b : is_word w a -> is_word w b ->
    (Z.T_modulo a b <= 64 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Ha Hb. pose proof (Z.T_modulo_le a b) as Hmod.
    pose proof (time_of_nat_le _ _ (word_size_bound w a Ha)) as Hsa.
    pose proof (time_of_nat_le _ _ (word_size_bound w b Hb)) as Hsb.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Increasing a natural work budget preserves a quadratic clock bound. *)
  Lemma time_square_weaken t c a b :
    (t <= c * N.of_nat (a ^ 2))%N -> (a <= b)%nat ->
    (t <= c * N.of_nat (b ^ 2))%N.
  Proof.
    intros Htime Hsize. eapply N.le_trans; [exact Htime|].
    apply N.mul_le_mono_l, time_of_nat_le, Nat.pow_le_mono_l. exact Hsize.
  Qed.

  (** Scaling the input budget squares the corresponding coefficient. *)
  Lemma time_square_scale t c a b k :
    (t <= c * N.of_nat (a ^ 2))%N -> (a <= k * b)%nat ->
    (t <= (c * N.of_nat (k ^ 2)) * N.of_nat (b ^ 2))%N.
  Proof.
    intros Htime Hsize. eapply N.le_trans with (m := (c * N.of_nat ((k * b) ^ 2))%N).
    - eapply time_square_weaken; eassumption.
    - rewrite Nat.pow_mul_l, Nat2N.inj_mul, N.mul_assoc. reflexivity.
  Qed.

  (** A positive squared work budget also pays any smaller linear charge. *)
  Lemma time_square_floor a b : (a <= b)%nat -> (1 <= b)%nat ->
    (N.of_nat a <= N.of_nat (b ^ 2))%N.
  Proof.
    intros Hsmall Hpositive. apply time_of_nat_le. cbn [Nat.pow]. nia.
  Qed.

  (** Unsigned division normalizes both operands and handles zero divisors directly. *)
  Lemma word_udiv_time_bound w x y :
    (T_wudiv w x y <=
      512 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    set (budget := N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2)).
    assert (Hx : (T_wrap w x <= 64 * budget)%N).
    { unfold budget. eapply time_square_weaken; [apply word_wrap_time_bound|lia]. }
    assert (Hy : (T_wrap w y <= 64 * budget)%N).
    { unfold budget. eapply time_square_weaken; [apply word_wrap_time_bound|lia]. }
    pose proof (word_modulus_time_bound w) as Hmodulus.
    pose proof (Z.T_sub_le (modulus w) 1) as Hones.
    pose proof (Z.T_eqb_le (wrap w y) 0) as Heq.
    assert (Hdiv : (Z.T_div (wrap w x) (wrap w y) <= 64 * budget)%N).
    { unfold budget. eapply time_square_weaken;
        [apply integer_div_word_time_bound; apply wrap_is_word|lia]. }
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsx.
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w y)) as Hsy.
    pose proof (time_of_nat_le _ _ (word_modulus_size_bound w)) as Hmodsize.
    assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= budget)%N).
    { unfold budget. apply time_square_floor; lia. }
    clearbody budget.
    time_unfold T_wudiv. destruct (wrap w y =? 0)%Z;
      rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  Qed.

  (** Unsigned remainder normalizes both operands and handles zero divisors directly. *)
  Lemma word_urem_time_bound w x y :
    (T_wurem w x y <=
      512 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    set (budget := N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2)).
    assert (Hx : (T_wrap w x <= 64 * budget)%N).
    { unfold budget. eapply time_square_weaken; [apply word_wrap_time_bound|lia]. }
    assert (Hy : (T_wrap w y <= 64 * budget)%N).
    { unfold budget. eapply time_square_weaken; [apply word_wrap_time_bound|lia]. }
    pose proof (Z.T_eqb_le (wrap w y) 0) as Heq.
    assert (Hmod : (Z.T_modulo (wrap w x) (wrap w y) <= 64 * budget)%N).
    { unfold budget. eapply time_square_weaken;
        [apply integer_mod_word_time_bound; apply wrap_is_word|lia]. }
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w y)) as Hsy.
    assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= budget)%N).
    { unfold budget. apply time_square_floor; lia. }
    clearbody budget.
    time_unfold T_wurem. destruct (wrap w y =? 0)%Z;
      rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  Qed.

  (** Comparison dispatch charges normalized unsigned or signed views of both operands. *)
  Lemma word_comparison_time_bound tag w x y :
    (T_eval_comparison_tag tag w x y <=
      512 * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N.
  Proof.
    set (budget := N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2)).
    assert (Hx : (T_wrap w x <= 64 * budget)%N).
    { unfold budget. eapply time_square_weaken; [apply word_wrap_time_bound|lia]. }
    assert (Hy : (T_wrap w y <= 64 * budget)%N).
    { unfold budget. eapply time_square_weaken; [apply word_wrap_time_bound|lia]. }
    assert (Hsignedx : (T_signed w x <= 128 * budget)%N).
    { unfold budget. eapply time_square_weaken; [apply word_signed_time_bound|lia]. }
    assert (Hsignedy : (T_signed w y <= 128 * budget)%N).
    { unfold budget. eapply time_square_weaken; [apply word_signed_time_bound|lia]. }
    pose proof (time_of_nat_le _ _ (word_wrap_size_bound w x)) as Hsx.
    pose proof (time_of_nat_le _ _ (word_signed_size_bound w x)) as Hssx.
    pose proof (Z.T_eqb_le (wrap w x) (wrap w y)) as Heq.
    pose proof (Z.T_ltb_le (wrap w x) (wrap w y)) as Hult.
    pose proof (Z.T_leb_le (wrap w x) (wrap w y)) as Hule.
    pose proof (Z.T_ltb_le (signed w x) (signed w y)) as Hslt.
    pose proof (Z.T_leb_le (signed w x) (signed w y)) as Hsle.
    assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= budget)%N).
    { unfold budget. apply time_square_floor; lia. }
    clearbody budget.
    destruct tag; time_unfold T_eval_comparison_tag;
      try time_unfold T_wult; try time_unfold T_wule;
      try time_unfold T_wslt; try time_unfold T_wsle;
      time_simpl; rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  Qed.

  (** A normalized unary input reduces its raw budget to twice the width budget. *)
  Lemma word_unary_width_bound f c w x :
    (forall w x, (f w x <= c * N.of_nat ((Pos.to_nat w + Z.size_nat x + 1) ^ 2))%N) ->
    is_word w x -> (f w x <= (c * 4) * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Htime Hx. eapply (time_square_scale _ c _ _ 2); [apply Htime|].
    pose proof (word_size_bound w x Hx). lia.
  Qed.

  (** Two normalized inputs reduce their raw budget to three times the width budget. *)
  Lemma word_binary_width_bound f c w x y :
    (forall w x y, (f w x y <=
      c * N.of_nat ((Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1) ^ 2))%N) ->
    is_word w x -> is_word w y ->
    (f w x y <= (c * 9) * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Htime Hx Hy. eapply (time_square_scale _ c _ _ 3); [apply Htime|].
    pose proof (word_size_bound w x Hx). pose proof (word_size_bound w y Hy). lia.
  Qed.

  (** Signed division composes bounded sign reads, unsigned division and modular negation. *)
  Lemma word_sdiv_time_bound w x y : is_word w x -> is_word w y ->
    (T_wsdiv w x y <= 16384 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy. assert (Hnx : is_word w (wneg w x)) by apply wrap_is_word.
    assert (Hny : is_word w (wneg w y)) by apply wrap_is_word.
    pose proof (word_unary_width_bound _ _ w x word_msb_time_bound Hx) as Hmx.
    pose proof (word_unary_width_bound _ _ w y word_msb_time_bound Hy) as Hmy.
    pose proof (word_unary_width_bound _ _ w x word_neg_time_bound Hx) as Hnegx.
    pose proof (word_unary_width_bound _ _ w y word_neg_time_bound Hy) as Hnegy.
    pose proof (word_binary_width_bound _ _ w x y word_udiv_time_bound Hx Hy) as Hpp.
    pose proof (word_binary_width_bound _ _ w (wneg w x) y
      word_udiv_time_bound Hnx Hy) as Hnp.
    pose proof (word_binary_width_bound _ _ w x (wneg w y)
      word_udiv_time_bound Hx Hny) as Hpn.
    pose proof (word_binary_width_bound _ _ w (wneg w x) (wneg w y)
      word_udiv_time_bound Hnx Hny) as Hnn.
    pose proof (word_unary_width_bound _ _ w (wudiv w (wneg w x) y)
      word_neg_time_bound (wudiv_is_word w (wneg w x) y)) as Houtnp.
    pose proof (word_unary_width_bound _ _ w (wudiv w x (wneg w y))
      word_neg_time_bound (wudiv_is_word w x (wneg w y))) as Houtpn.
    pose proof (time_square_floor 1 (Pos.to_nat w + 1) ltac:(lia) ltac:(lia)) as Hpositive.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
    time_unfold T_wsdiv. destruct (msb w x), (msb w y); time_cbn_all; lia.
  Qed.

  (** Signed remainder composes the same bounded sign reads and normalized operations. *)
  Lemma word_srem_time_bound w x y : is_word w x -> is_word w y ->
    (T_wsrem w x y <= 16384 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy. assert (Hnx : is_word w (wneg w x)) by apply wrap_is_word.
    assert (Hny : is_word w (wneg w y)) by apply wrap_is_word.
    pose proof (word_unary_width_bound _ _ w x word_msb_time_bound Hx) as Hmx.
    pose proof (word_unary_width_bound _ _ w y word_msb_time_bound Hy) as Hmy.
    pose proof (word_unary_width_bound _ _ w x word_neg_time_bound Hx) as Hnegx.
    pose proof (word_unary_width_bound _ _ w y word_neg_time_bound Hy) as Hnegy.
    pose proof (word_binary_width_bound _ _ w x y word_urem_time_bound Hx Hy) as Hpp.
    pose proof (word_binary_width_bound _ _ w (wneg w x) y
      word_urem_time_bound Hnx Hy) as Hnp.
    pose proof (word_binary_width_bound _ _ w x (wneg w y)
      word_urem_time_bound Hx Hny) as Hpn.
    pose proof (word_binary_width_bound _ _ w (wneg w x) (wneg w y)
      word_urem_time_bound Hnx Hny) as Hnn.
    pose proof (word_unary_width_bound _ _ w (wurem w (wneg w x) y)
      word_neg_time_bound (wurem_is_word w (wneg w x) y)) as Houtnp.
    pose proof (word_unary_width_bound _ _ w (wurem w (wneg w x) (wneg w y))
      word_neg_time_bound (wurem_is_word w (wneg w x) (wneg w y))) as Houtnn.
    pose proof (time_square_floor 1 (Pos.to_nat w + 1) ltac:(lia) ltac:(lia)) as Hpositive.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
    time_unfold T_wsrem. destruct (msb w x), (msb w y); time_cbn_all; lia.
  Qed.

  (** Signed modulus adjusts a normalized unsigned remainder by bounded word arithmetic. *)
  Lemma word_smod_time_bound w x y : is_word w x -> is_word w y ->
    (T_wsmod w x y <= 32768 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy. time_unfold T_wsmod.
    set (ax := if msb w x then wneg w x else wrap w x).
    set (ay := if msb w y then wneg w y else wrap w y).
    set (u := wurem w ax ay).
    assert (Hax : is_word w ax) by (unfold ax; destruct (msb w x); apply wrap_is_word).
    assert (Hay : is_word w ay) by (unfold ay; destruct (msb w y); apply wrap_is_word).
    assert (Hu : is_word w u) by apply wurem_is_word.
    pose proof (word_unary_width_bound _ _ w x word_msb_time_bound Hx) as Hmx.
    pose proof (word_unary_width_bound _ _ w y word_msb_time_bound Hy) as Hmy.
    pose proof (word_unary_width_bound _ _ w x word_neg_time_bound Hx) as Hnegx.
    pose proof (word_unary_width_bound _ _ w y word_neg_time_bound Hy) as Hnegy.
    pose proof (word_unary_width_bound _ _ w x word_wrap_time_bound Hx) as Hwrapx.
    pose proof (word_unary_width_bound _ _ w y word_wrap_time_bound Hy) as Hwrapy.
    pose proof (word_binary_width_bound _ _ w ax ay word_urem_time_bound Hax Hay) as Hurem.
    pose proof (word_unary_width_bound _ _ w u word_neg_time_bound Hu) as Hnegu.
    pose proof (word_binary_width_bound _ _ w (wneg w u) y
      word_add_time_bound (wrap_is_word w (- u)) Hy) as Haddneg.
    pose proof (word_binary_width_bound _ _ w u y word_add_time_bound Hu Hy) as Hadd.
    pose proof (Z.T_eqb_le u 0) as Heq.
    pose proof (time_of_nat_le _ _ (word_size_bound w u Hu)) as Hsize.
    pose proof (time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      ltac:(lia) ltac:(lia)) as Hlinear.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
    clearbody budget ax ay u. destruct (u =? 0)%Z, (msb w x), (msb w y);
      rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  Qed.

  (** Division by a positive integer never increases magnitude bit length. *)
  Lemma integer_positive_div_size a d : (0 < d)%Z ->
    (Z.size_nat (a / d) <= Z.size_nat a)%nat.
  Proof.
    intros Hd. apply integer_abs_size_bound.
    pose proof (integer_magnitude_bound a) as Ha.
    destruct (Z_le_dec 0 a) as [Hnonnegative|Hnegative].
    - assert (Hlo : (0 <= a / d)%Z) by (apply Z.div_pos; lia).
      assert (Hhi : (a / d <= a)%Z) by (apply Z.div_le_upper_bound; nia).
      lia.
    - assert (Hlo : (a <= a / d)%Z) by (apply Z.div_le_lower_bound; nia).
      assert (Hhi : (a / d <= 0)%Z) by (apply Z.div_le_upper_bound; nia).
      lia.
  Qed.

  (** A power used by a bounded shift needs at most one extra width bit. *)
  Lemma word_power_size_bound w k : (0 <= k <= Zpos w)%Z ->
    (Z.size_nat (2 ^ k) <= Pos.to_nat w + 1)%nat.
  Proof.
    intros Hk. apply integer_size_bound. split.
    - apply Z.pow_nonneg; lia.
    - rewrite Nat2Z.inj_add, positive_nat_Z. apply Z.pow_lt_mono_r; lia.
  Qed.

  (** Constructing a bounded shift power takes linear time in the width. *)
  Lemma word_power_time_bound w k : (0 <= k <= Zpos w)%Z ->
    (Word.Z.T_pow 2 k <= 8 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    intros Hk. pose proof (word_pow_two_time_bound k ltac:(lia)) as Hpow.
    assert (Hknat : (Z.to_nat k <= Pos.to_nat w)%nat).
    { change (Z.to_nat k <= Z.to_nat (Zpos w))%nat. apply Z2Nat.inj_le; lia. }
    apply time_of_nat_le in Hknat. rewrite Nat2N.inj_add. time_cbn_all. lia.
  Qed.

  (** Multiplying two normalized words fits a quadratic width budget. *)
  Lemma integer_mul_word_time_bound w x y : is_word w x -> is_word w y ->
    (Z.T_mul x y <= 8 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy. pose proof (Z.T_mul_le x y) as Htime.
    pose proof (time_of_nat_le _ _ (word_size_bound w x Hx)).
    pose proof (time_of_nat_le _ _ (word_size_bound w y Hy)).
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *. nia.
  Qed.

  (** Left shift tests the amount before constructing a width-bounded power. *)
  Lemma word_shl_time_bound w x y : is_word w x -> is_word w y ->
    (T_wshl w x y <= 2048 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy.
    pose proof (word_unary_width_bound _ _ w x word_wrap_time_bound Hx) as Hwrapx.
    pose proof (word_unary_width_bound _ _ w y word_wrap_time_bound Hy) as Hwrapy.
    pose proof (Z.T_leb_le (Zpos w) (wrap w y)) as Hcompare.
    pose proof (time_of_nat_le _ _ (positive_size_value w)) as Hwidthsize.
    pose proof (time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      ltac:(lia) ltac:(lia)) as Hlinear.
    time_unfold T_wshl. destruct (Zpos w <=? wrap w y)%Z eqn:Hlarge.
    - set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
      rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
    - apply Z.leb_gt in Hlarge. pose proof (proj1 (wrap_is_word w y)) as Hyzero.
      assert (Hpower : is_word w (2 ^ wrap w y)) by (apply pow2_word; lia).
      pose proof (word_power_time_bound w (wrap w y) ltac:(unfold is_word in *; lia))
        as Hpowtime.
      pose proof (integer_mul_word_time_bound w (wrap w x) (2 ^ wrap w y)
        (wrap_is_word w x) Hpower) as Hmultime.
      assert (Houter : (T_wrap w (wrap w x * 2 ^ wrap w y) <=
        (64 * 9) * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
      { eapply (time_square_scale _ 64 _ _ 3); [apply word_wrap_time_bound|].
        pose proof (integer_mul_size (wrap w x) (2 ^ wrap w y)).
        pose proof (word_wrap_size_bound w x). pose proof (word_size_bound w _ Hpower). lia. }
      set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
      rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.

  (** Division depends quadratically on the two magnitude bounds. *)
  Lemma integer_div_size_time_bound n x y :
    (Z.size_nat x <= n)%nat -> (Z.size_nat y <= n)%nat ->
    (Z.T_div x y <= 64 * N.of_nat ((n + 1) ^ 2))%N.
  Proof.
    intros Hx Hy. apply time_of_nat_le in Hx. apply time_of_nat_le in Hy.
    pose proof (Z.T_div_le x y) as Hdiv.
    rewrite ?Nat2N.inj_pow, ?Nat2N.inj_add in *. nia.
  Qed.

  (** Logical right shift divides only by a power fitting the operand width. *)
  Lemma word_lshr_time_bound w x y : is_word w x -> is_word w y ->
    (T_wlshr w x y <= 2048 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy.
    pose proof (word_unary_width_bound _ _ w x word_wrap_time_bound Hx) as Hwrapx.
    pose proof (word_unary_width_bound _ _ w y word_wrap_time_bound Hy) as Hwrapy.
    pose proof (Z.T_leb_le (Zpos w) (wrap w y)) as Hcompare.
    pose proof (time_of_nat_le _ _ (positive_size_value w)) as Hwidthsize.
    pose proof (time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      ltac:(lia) ltac:(lia)) as Hlinear.
    time_unfold T_wlshr. destruct (Zpos w <=? wrap w y)%Z eqn:Hlarge.
    - set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
      rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
    - apply Z.leb_gt in Hlarge. pose proof (proj1 (wrap_is_word w y)) as Hyzero.
      assert (Hpower : is_word w (2 ^ wrap w y)) by (apply pow2_word; lia).
      pose proof (word_power_time_bound w (wrap w y) ltac:(lia)) as Hpowtime.
      pose proof (integer_div_word_time_bound w (wrap w x) (2 ^ wrap w y)
        (wrap_is_word w x) Hpower) as Hdivtime.
      set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
      rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.

  (** Arithmetic right shift charges its sign branch or a bounded signed quotient. *)
  Lemma word_ashr_time_bound w x y : is_word w x -> is_word w y ->
    (T_washr w x y <= 2048 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy.
    pose proof (word_unary_width_bound _ _ w x word_msb_time_bound Hx) as Hmsb.
    pose proof (word_unary_width_bound _ _ w x word_signed_time_bound Hx) as Hsigned.
    pose proof (word_unary_width_bound _ _ w y word_wrap_time_bound Hy) as Hwrapy.
    pose proof (word_modulus_time_bound w) as Hmodulus.
    pose proof (Z.T_sub_le (modulus w) 1) as Hsub.
    pose proof (time_of_nat_le _ _ (word_modulus_size_bound w)) as Hmodulussize.
    pose proof (Z.T_leb_le (Zpos w) (wrap w y)) as Hcompare.
    pose proof (time_of_nat_le _ _ (positive_size_value w)) as Hwidthsize.
    pose proof (time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      ltac:(lia) ltac:(lia)) as Hlinear.
    time_unfold T_washr. destruct (Zpos w <=? wrap w y)%Z eqn:Hlarge.
    - set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
      destruct (msb w x); rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
    - apply Z.leb_gt in Hlarge. pose proof (proj1 (wrap_is_word w y)) as Hyzero.
      assert (Hpower : is_word w (2 ^ wrap w y)) by (apply pow2_word; lia).
      assert (Hpositive : (0 < 2 ^ wrap w y)%Z) by (apply Z.pow_pos_nonneg; lia).
      pose proof (word_power_time_bound w (wrap w y) ltac:(lia)) as Hpowtime.
      pose proof (integer_div_size_time_bound (Pos.to_nat w)
        (signed w x) (2 ^ wrap w y) (word_signed_size_bound w x)
        (word_size_bound w _ Hpower)) as Hdivtime.
      assert (Houter : (T_wrap w (signed w x / 2 ^ wrap w y) <=
        (64 * 4) * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
      { eapply (time_square_scale _ 64 _ _ 2); [apply word_wrap_time_bound|].
        pose proof (integer_positive_div_size (signed w x) _ Hpositive).
        pose proof (word_signed_size_bound w x). lia. }
      set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
      rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.

  (** Left rotation combines two bounded powers and one final normalization. *)
  Lemma word_rotl_time_bound w x y : is_word w x -> is_word w y ->
    (T_wrotl w x y <= 4096 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy. time_unfold T_wrotl. set (k := (wrap w y mod Zpos w)%Z).
    assert (Hk : (0 <= k < Zpos w)%Z) by (unfold k; apply Z.mod_pos_bound; lia).
    assert (Hkw : is_word w k) by (apply small_amount_word; exact Hk).
    assert (Hpower : is_word w (2 ^ k)) by (apply pow2_word; exact Hk).
    assert (Hcomplement : (0 < 2 ^ (Zpos w - k))%Z) by (apply Z.pow_pos_nonneg; lia).
    pose proof (word_unary_width_bound _ _ w x word_wrap_time_bound Hx) as Hwrapx.
    pose proof (word_unary_width_bound _ _ w y word_wrap_time_bound Hy) as Hwrapy.
    pose proof (integer_mod_word_time_bound w (wrap w y) (Zpos w)
      (wrap_is_word w y) (count_is_word w (Zpos w) ltac:(lia))) as Hmodtime.
    pose proof (word_power_time_bound w k ltac:(lia)) as Hpowlo.
    pose proof (word_power_time_bound w (Zpos w - k) ltac:(lia)) as Hpowhi.
    pose proof (integer_mul_word_time_bound w (wrap w x) (2 ^ k)
      (wrap_is_word w x) Hpower) as Hmultime.
    assert (Hdivtime : (Z.T_div (wrap w x) (2 ^ (Zpos w - k)) <=
      (64 * 4) * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
    { eapply (time_square_scale _ 64 _ _ 2).
      - apply (integer_div_size_time_bound (Pos.to_nat w + 1)).
        + pose proof (word_wrap_size_bound w x). lia.
        + apply word_power_size_bound. lia.
      - lia. }
    assert (Hmulsize : (Z.size_nat (wrap w x * 2 ^ k) <= 2 * Pos.to_nat w)%nat).
    { pose proof (integer_mul_size (wrap w x) (2 ^ k)).
      pose proof (word_wrap_size_bound w x). pose proof (word_size_bound w _ Hpower). lia. }
    assert (Hdivsize : (Z.size_nat (wrap w x / 2 ^ (Zpos w - k)) <= Pos.to_nat w)%nat).
    { pose proof (integer_positive_div_size (wrap w x) _ Hcomplement).
      pose proof (word_wrap_size_bound w x). lia. }
    assert (Houter : (T_wrap w (wrap w x * 2 ^ k + wrap w x / 2 ^ (Zpos w - k)) <=
      (64 * 16) * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N).
    { eapply (time_square_scale _ 64 _ _ 4); [apply word_wrap_time_bound|].
      pose proof (integer_add_size (wrap w x * 2 ^ k) (wrap w x / 2 ^ (Zpos w - k))).
      lia. }
    pose proof (Z.T_add_le (wrap w x * 2 ^ k) (wrap w x / 2 ^ (Zpos w - k))) as Hadd.
    pose proof (Z.T_sub_le (Zpos w) k) as Hsub.
    pose proof (time_of_nat_le _ _ (word_size_bound w _ Hkw)) as Hksize.
    pose proof (time_of_nat_le _ _ (positive_size_value w)) as Hwidthsize.
    apply time_of_nat_le in Hmulsize. apply time_of_nat_le in Hdivsize.
    pose proof (time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      ltac:(lia) ltac:(lia)) as Hlinear.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget k.
    rewrite ?Nat2N.inj_mul, ?Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.

  (** Right rotation calls the bounded left rotation at a normalized complementary amount. *)
  Lemma word_rotr_time_bound w x y : is_word w x -> is_word w y ->
    (T_wrotr w x y <= 8192 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy. time_unfold T_wrotr. set (k := (wrap w y mod Zpos w)%Z).
    assert (Hk : (0 <= k < Zpos w)%Z) by (unfold k; apply Z.mod_pos_bound; lia).
    pose proof (word_rotl_time_bound w x (Zpos w - k) Hx
      (count_is_word w (Zpos w - k) ltac:(lia))) as Hrotl.
    pose proof (word_unary_width_bound _ _ w y word_wrap_time_bound Hy) as Hwrapy.
    pose proof (integer_mod_word_time_bound w (wrap w y) (Zpos w)
      (wrap_is_word w y) (count_is_word w (Zpos w) ltac:(lia))) as Hmodtime.
    pose proof (Z.T_sub_le (Zpos w) k) as Hsub.
    pose proof (time_of_nat_le _ _ (word_size_bound w k (small_amount_word w k Hk)))
      as Hksize.
    pose proof (time_of_nat_le _ _ (positive_size_value w)) as Hwidthsize.
    pose proof (time_square_floor (Pos.to_nat w + 1) (Pos.to_nat w + 1)
      ltac:(lia) ltac:(lia)) as Hlinear.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget k.
    rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.

  (** Binary dispatch chooses one of the uniformly bounded normalized operations. *)
  Lemma word_binary_time_bound tag w x y : is_word w x -> is_word w y ->
    (T_eval_binary_tag tag w x y <= 65536 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intros Hx Hy.
    pose proof (word_binary_width_bound _ _ w x y word_add_time_bound Hx Hy) as Hadd.
    pose proof (word_binary_width_bound _ _ w x y word_sub_time_bound Hx Hy) as Hsub.
    pose proof (word_binary_width_bound _ _ w x y word_mul_time_bound Hx Hy) as Hmul.
    pose proof (word_binary_width_bound _ _ w x y word_udiv_time_bound Hx Hy) as Hudiv.
    pose proof (word_binary_width_bound _ _ w x y word_urem_time_bound Hx Hy) as Hurem.
    pose proof (word_sdiv_time_bound w x y Hx Hy) as Hsdiv.
    pose proof (word_srem_time_bound w x y Hx Hy) as Hsrem.
    pose proof (word_smod_time_bound w x y Hx Hy) as Hsmod.
    pose proof (word_binary_width_bound _ _ w x y word_and_time_bound Hx Hy) as Hand.
    pose proof (word_binary_width_bound _ _ w x y word_or_time_bound Hx Hy) as Hor.
    pose proof (word_binary_width_bound _ _ w x y word_xor_time_bound Hx Hy) as Hxor.
    pose proof (word_shl_time_bound w x y Hx Hy) as Hshl.
    pose proof (word_lshr_time_bound w x y Hx Hy) as Hlshr.
    pose proof (word_ashr_time_bound w x y Hx Hy) as Hashr.
    pose proof (word_rotl_time_bound w x y Hx Hy) as Hrotl.
    pose proof (word_rotr_time_bound w x y Hx Hy) as Hrotr.
    pose proof (time_square_floor 1 (Pos.to_nat w + 1) ltac:(lia) ltac:(lia)) as Hpositive.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *. clearbody budget.
    destruct tag; time_unfold T_eval_binary_tag; time_cbn_all; lia.
  Qed.

End WordTime.


Inductive bop : Type :=
  | BConst (w : width) (z : Z)
  | BOp (o : Op.op).

Inductive bguard : Type :=
  | BTruth (b : bool).

(** Operator work charges its own widths and literal before operand widths. *)
Definition op_bits (o : bop) : nat :=
  match o with
  | BConst w z => Pos.to_nat w + Z.size_nat z
  | BOp o => Op.op_widths o
  end.

(** Word evaluation charges metadata, operand widths and raw integer sizes quadratically. *)
Definition work (o : bop) (vs : list word) : nat :=
  ((op_bits o + fold_right Nat.add 0
    (map (fun v => Pos.to_nat (fst v) + Z.size_nat (snd v)) vs) + 1) ^ 2)%nat.

Module Nat.
  TimeFun Nat.pow.
End Nat.

TimeFun op_bits.
TimeFun work.

Module BitsLangCode <: LANG_OPS.
  Definition op := bop.
  Definition guard := bguard.
  Definition val := word.
  Definition eval (o : op) (vs : list val) : option val :=
    match o, vs with
    | BConst w z, [] => Some (w, wrap w z)
    | BOp o, _ => eval_op o vs
    | _, _ => None
    end.
  Definition literal (o : op) : option Z :=
    match o with
    | BConst _ z => Some z
    | BOp _ => None
    end.
End BitsLangCode.

Module BitsLang <: LANG.
  Include BitsLangCode.
  Definition holds (g : guard) (vs : list val) : Prop :=
    match g, vs with
    | BTruth b, (w, z) :: nil => w = 1%positive /\ z = (if b then 1 else 0)%Z
    | _, _ => False
    end.
End BitsLang.

Module WordLanguageCode <: WORD_LANGUAGE_OPS.
  Definition op := Op.op.
  Definition wrap := Word.wrap.
  Definition signed := Word.signed.
  Definition eval_op := Op.eval_op.
  Definition result_width := Op.result_width.
End WordLanguageCode.

Module WordLanguage <: WORD_LANGUAGE.
  Include WordLanguageCode.
  Definition is_word := Word.is_word.
  Lemma wrap_is_word : forall w z, is_word w (wrap w z).
  Proof. exact Word.wrap_is_word. Qed.
  Lemma eval_op_is_word : forall o cs w z, eval_op o cs = Some (w, z) ->
    is_word w z /\ result_width o (map fst cs) = Some w.
  Proof.
    intros o cs w z Hresult. split.
    - exact (Op.eval_op_is_word o cs (w, z) Hresult).
    - exact (Op.eval_op_width o cs (w, z) Hresult).
  Qed.
End WordLanguage.

Module BitsLangT <: LANG_T.
  Include BitsLang.
  Definition work := work.
  TimeFun eval.
  TimeFun literal.
  Definition c_lang : N := 1%N. (* STUB *)
  Lemma T_eval_le : forall o vs,
    (T_eval o vs <= c_lang * N.of_nat (work o vs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_literal_le : forall o, (T_literal o <= c_lang)%N.
  Proof.
    intros o. unfold c_lang. time_step.
  Qed.
End BitsLangT.

Module WordLanguageT <: WORD_LANGUAGE_T.
  Include WordLanguage.
  TimeFun wrap.
  TimeFun signed.
  TimeFun eval_op.
  TimeFun result_width.
  Definition c_word : N := 1%N. (* STUB *)
  Lemma T_eval_op_le : forall o cs,
    (T_eval_op o cs <=
      c_word * N.of_nat (((Op.op_widths o +
        fold_right Nat.add 0
          (map (fun c => Pos.to_nat (fst c) + Z.size_nat (snd c)) cs) + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
End WordLanguageT.
