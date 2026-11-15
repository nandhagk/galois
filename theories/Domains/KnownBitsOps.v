(** * Known-bit word operations

    These operations connect known-bit masks to word transfers.
    For example, evaluating a zero-preserving operator keeps known zero bits.
    Builds on: KnownBits and the bit-vector operations. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word Op Fun Arith.
From Galois.Domains Require Import ValueSig WordSig KnownBitsSig KnownBits BitsLang Tagged.
Import List.ListNotations.
Local Open Scope Z_scope.

Module KnownBitsOpsCode (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG)
    (K : KNOWN_BITS_OPS L C).
  Definition tnum_forward_raw (o : op) (wps : list (width * tnum)) (rw : width) : tnum :=
    match o, wps with
    | bvnot, [(_, a)] => K.tnum_not rw a
    | bvneg, [(_, a)] => K.tnum_neg rw a
    | (bvclz | bvctz | bvpopcnt), [_] => tnum_count rw
    | bvadd, [(_, a); (_, b)] => K.tnum_add rw a b
    | bvsub, [(_, a); (_, b)] => K.tnum_sub rw a b
    | bvmul, [(w, a); (v, b)] =>
      if Pos.eqb w rw && Pos.eqb v rw then K.tnum_mul rw a b
      else tnum_mul rw a b
    | bvudiv, [(_, a); (_, b)] => tnum_udiv rw a b
    | bvurem, [(_, a); _] => tnum_urem rw a
    | bvsrem, [(_, a); _] => tnum_srem rw a
    | bvand, [(_, a); (_, b)] => K.tnum_and rw a b
    | bvor, [(_, a); (_, b)] => K.tnum_or rw a b
    | bvxor, [(_, a); (_, b)] => K.tnum_xor rw a b
    | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(_, a); (_, b)] =>
      K.tnum_variable o rw a b
    | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] =>
      tnum_compare o w a b
    | bvite, [(_, c); (_, a); (_, b)] => tnum_ite rw c a b
    | (bvzext _ | bvtrunc _), [(w, a)] => tnum_map w rw (tnum_wrap rw) a
    | bvsext _, [(w, a)] => tnum_map w rw (fun x => tnum_wrap rw (signed w x)) a
    | bvextract _ lo, [(w, a)] => tnum_map w rw (fun x => tnum_wrap rw (x / 2 ^ Z.of_nat lo)) a
    | bvconcat, [(w, a); (v, b)] => tnum_concat w v a b
    | _, _ => tnum_top
    end.
End KnownBitsOpsCode.

Module KnownBitsOpsClock (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG) (K : KNOWN_BITS_T L C).
  Include KnownBitsOpsCode L C K.
  TimeFun tnum_forward_raw.
End KnownBitsOpsClock.

Definition tnum_payload_sound (wp : width * tnum) (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ tnum_gamma (fst wp) (snd wp) (snd y).

(** Pointwise agreement suffices because a mask map reads only its two endpoints. *)
Lemma tnum_map_ext : forall sw rw f g a,
  (forall x, f x = g x) -> tnum_map sw rw f a = tnum_map sw rw g a.
Proof.
  intros sw rw f g a Hagree. unfold tnum_map. now rewrite !Hagree.
Qed.

(** A nonnegative endpoint needs at most its stored bit count as an upper-mask length. *)
Lemma table_bitlen_size : forall h, 0 <= h ->
  0 <= tnum_bitlen h /\ (Z.to_nat (tnum_bitlen h) <= Z.size_nat h)%nat.
Proof.
  intros h Hh. unfold tnum_bitlen.
  destruct (h =? 0) eqn:Hzero; [split; [lia|cbn; lia]|].
  apply Z.eqb_neq in Hzero.
  pose proof (Z.log2_nonneg h) as Hlog.
  pose proof (tnum_abs_bits_bound h) as Hbits.
  rewrite Z.abs_eq in Hbits by exact Hh.
  apply Z.log2_lt_pow2 in Hbits; [|lia].
  split; [lia|]. apply Nat2Z.inj_le.
  rewrite Z2Nat.id by lia. lia.
Qed.

(** Constructing an all-ones mask preserves its requested bit-length bound. *)
Local Lemma table_ones_bits : forall n, 0 <= n ->
  (Z.size_nat (Z.ones n) <= Z.to_nat n)%nat.
Proof.
  intros n Hn. apply tnum_bits_of_abs_bound.
  rewrite Z.ones_equiv, Z2Nat.id by exact Hn.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn).
  rewrite Z.abs_eq; lia.
Qed.

(** Determining the upper-mask length scans only the endpoint's stored bits. *)
Lemma table_bitlen_time : forall h,
  (T_tnum_bitlen h <= 32 * N.of_nat (Z.size_nat h + 1))%N.
Proof.
  intro h. pose proof (WordTime.integer_log2_size h) as Hsize.
  time_unfold T_tnum_bitlen. time_cbn. time_pose.
  destruct (h =? 0); rewrite ?Nat2N.inj_add in *; nia.
Qed.
TimeBound table_bitlen_time.

(** An upper-mask transfer is linear in width and endpoint storage. *)
Lemma table_upper_time : forall w h, 0 <= h ->
  (T_tnum_upper w h <= 2048 * N.of_nat (Pos.to_nat w + Z.size_nat h + 1))%N.
Proof.
  intros w h Hh. destruct (table_bitlen_size h Hh) as [Hnonnegative Hlength].
  pose proof (table_ones_bits _ Hnonnegative) as Hbits.
  pose proof (tnum_ones_time _ Hnonnegative) as Hones.
  time_unfold T_tnum_upper. time_cbn. time_pose.
  rewrite ?Nat2N.inj_add in *. nia.
Qed.

(** The coarse unsigned quotient only inspects the divisor and dividend masks. *)
Lemma table_udiv_time : forall w a b,
  (T_tnum_udiv w a b <= 8192 *
    N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b.
  pose proof (table_upper_time w (tnum_max w a) (proj1 (tnum_max_word w a))).
  pose proof (tnum_max_bits w a). pose proof (tnum_wrap_bits w (ones b)).
  time_unfold T_tnum_udiv. time_cbn. time_pose.
  destruct (tnum_wrap w (ones b) =? 0); unfold tnum_bits in *;
    rewrite ?Nat2N.inj_add in *; nia.
Qed.
TimeBound table_udiv_time.

(** The coarse unsigned remainder reads the dividend's maximum endpoint. *)
Lemma table_urem_time : forall w a,
  (T_tnum_urem w a <= 8192 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a.
  pose proof (table_upper_time w (tnum_max w a) (proj1 (tnum_max_word w a))).
  pose proof (tnum_max_bits w a).
  time_unfold T_tnum_urem. time_cbn. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound table_urem_time.

(** Count transfers construct an upper bound from the width itself. *)
Lemma table_count_time : forall w,
  (T_tnum_count w <= 8192 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (table_upper_time w (Zpos w) ltac:(lia)) as Hupper.
  pose proof (tnum_positive_bits w).
  time_unfold T_tnum_count. time_cbn.
  change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in Hupper.
  rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound table_count_time.

(** The signed remainder approximation reads the sign mask linearly. *)
Lemma table_srem_time : forall w a,
  (T_tnum_srem w a <= 1024 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a. pose proof (WordTime.word_half_time_bound w).
  pose proof (WordTime.word_half_size_bound w).
  time_unfold T_tnum_srem. time_cbn. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound table_srem_time.

(** A recognized constant is a normalized endpoint. *)
Lemma table_constant_bits : forall w a k, tnum_constant w a = Some k ->
  (Z.size_nat k <= Pos.to_nat w)%nat.
Proof.
  intros w a k Hconstant. unfold tnum_constant in Hconstant.
  destruct (tnum_wrap w (zeros a) =? tnum_wnot w (ones a)); [|discriminate].
  injection Hconstant as <-. apply tnum_min_bits.
Qed.

(** An order comparison reads four bounded endpoints and returns a one-bit mask. *)
Lemma table_order_time : forall strict w a b,
  (T_tnum_order strict w a b <= 8192 *
    N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros strict w a b.
  pose proof (tnum_min_bits w a). pose proof (tnum_max_bits w a).
  pose proof (tnum_min_bits w b). pose proof (tnum_max_bits w b).
  destruct strict; time_unfold T_tnum_order; cbn beta iota zeta;
    repeat match goal with
    | |- context [if ?test then _ else _] => destruct test
    end; time_pose; unfold tnum_bits in *;
    cbn [Z.size_nat Pos.size_nat Pos.to_nat] in *;
    rewrite ?Nat2N.inj_add in *; lia.
Qed.
TimeBound table_order_time.

(** Equality comparison inspects the masks and at most two normalized constants. *)
Lemma table_equal_time : forall w a b,
  (T_tnum_equal w a b <= 8192 *
    N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b. pose proof (tnum_meet_bits w a b) as Hmeet.
  time_unfold T_tnum_equal. cbn beta iota zeta.
  destruct (tnum_empty w (tnum_meet w a b)); [|].
  - time_pose. unfold tnum_bits in *. cbn [Z.size_nat Pos.size_nat Pos.to_nat] in *.
    rewrite ?Nat2N.inj_add in *. lia.
  - destruct (tnum_constant w a) as [x|] eqn:Ha;
      destruct (tnum_constant w b) as [y|] eqn:Hb; cbn beta iota zeta;
      try pose proof (table_constant_bits w a x Ha) as Hx;
      try pose proof (table_constant_bits w b y Hb) as Hy;
      time_pose;
      repeat match goal with
      | |- context [if ?test then _ else _] => destruct test
      end; unfold tnum_bits in *; cbn [Z.size_nat Pos.size_nat Pos.to_nat] in *;
      rewrite ?Nat2N.inj_add in *; lia.
Qed.
TimeBound table_equal_time.

(** Flipping the sign bit adds only linear mask work. *)
Lemma table_bias_time : forall w a,
  (T_tnum_bias w a <= 16384 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a. pose proof (WordTime.word_half_time_bound w).
  pose proof (WordTime.word_half_size_bound w).
  pose proof (tnum_const_bits w (half w)).
  time_unfold T_tnum_bias. cbn beta iota zeta. time_pose.
  rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound table_bias_time.

(** Every comparison uses a bounded number of linear mask transfers. *)
Lemma table_compare_time : forall o w a b,
  (T_tnum_compare o w a b <= 131072 *
    N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros o w a b.
  pose proof (tnum_equal_bits w a b).
  pose proof (tnum_xor_bits w a (tnum_const w (half w))) as Ha.
  pose proof (tnum_xor_bits w b (tnum_const w (half w))) as Hb.
  change (tnum_bits (tnum_bias w a) <= 2 * Pos.to_nat w)%nat in Ha.
  change (tnum_bits (tnum_bias w b) <= 2 * Pos.to_nat w)%nat in Hb.
  destruct o; time_unfold T_tnum_compare; cbn beta iota zeta; time_pose;
    cbn [Pos.to_nat] in *; rewrite ?Nat2N.inj_add in *; lia.
Qed.
TimeBound table_compare_time.

(** Conditional selection inspects a one-bit condition and normalizes its result. *)
Lemma table_ite_time : forall w c a b,
  (T_tnum_ite w c a b <= 8192 *
    N.of_nat (Pos.to_nat w + tnum_bits c + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w c a b. time_unfold T_tnum_ite. cbn beta iota zeta.
  destruct (tnum_constant 1%positive c) as [k|] eqn:Hconstant;
    cbn beta iota zeta.
  - pose proof (table_constant_bits 1%positive c k Hconstant) as Hk.
    destruct (k =? 1); time_pose; cbn [Pos.to_nat] in *;
      rewrite ?Nat2N.inj_add in *; lia.
  - time_pose. cbn [Pos.to_nat] in *. rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound table_ite_time.

(** A shared magnitude bound gives a quadratic multiplication clock. *)
Lemma table_product_time_budget : forall x y n,
  (Z.size_nat x <= n)%nat -> (Z.size_nat y <= n)%nat ->
  (Std.Z.T_mul x y <= 8 * N.of_nat ((n + 1) ^ 2))%N.
Proof.
  intros x y n Hx Hy. apply time_of_nat_le in Hx, Hy.
  pose proof (Std.Z.T_mul_le x y).
  cbn [Nat.pow]. rewrite ?Nat2N.inj_mul, ?Nat2N.inj_add. nia.
Qed.

(** Concatenation normalizes raw masks before its two width-bounded products. *)
Lemma table_concat_time : forall w v a b,
  (T_tnum_concat w v a b <= 8192 * N.of_nat
    ((Pos.to_nat w + Pos.to_nat v + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
Proof.
  intros w v a b.
  pose proof (Pos2Nat.is_pos w) as Hw. pose proof (Pos2Nat.is_pos v) as Hv.
  pose proof (tnum_positive_bits w). pose proof (tnum_positive_bits v).
  pose proof (tnum_wrap_bits w (zeros a)) as Haz.
  pose proof (tnum_wrap_bits w (ones a)) as Hao.
  pose proof (tnum_wrap_bits v (zeros b)) as Hbz.
  pose proof (tnum_wrap_bits v (ones b)) as Hbo.
  pose proof (tnum_modulus_bits v) as Hmod.
  pose proof (WordTime.integer_mul_size (tnum_wrap w (zeros a)) (modulus v)) as Hpzero.
  pose proof (WordTime.integer_mul_size (tnum_wrap w (ones a)) (modulus v)) as Hpone.
  pose proof (tnum_sum_bits (tnum_wrap w (zeros a) * modulus v)
    (tnum_wrap v (zeros b))) as Hszero.
  pose proof (tnum_sum_bits (tnum_wrap w (ones a) * modulus v)
    (tnum_wrap v (ones b))) as Hsone.
  pose proof (table_product_time_budget (tnum_wrap w (zeros a)) (modulus v)
    (Pos.to_nat w + Pos.to_nat v) ltac:(lia) ltac:(lia)) as HTzero.
  pose proof (table_product_time_budget (tnum_wrap w (ones a)) (modulus v)
    (Pos.to_nat w + Pos.to_nat v) ltac:(lia) ltac:(lia)) as HTone.
  time_unfold T_tnum_concat. cbn beta iota zeta. time_pose.
  rewrite ?Pos2Nat.inj_add in *.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *.
  set (square := N.of_nat ((Pos.to_nat w + Pos.to_nat v + 1) ^ 2)) in *.
  assert (Hlinear : (N.of_nat (Pos.to_nat w + Pos.to_nat v + 1) <= square)%N).
  { unfold square. clear - w v. apply time_of_nat_le. cbn [Nat.pow]. nia. }
  clearbody square. rewrite ?Nat2N.inj_add in Hlinear. lia.
Qed.
TimeBound table_concat_time.

(** Two bounded endpoint callbacks lift to the shared quadratic table budget. *)
Lemma table_map_time_budget : forall sw rw f Tf a k,
  (forall x, is_word sw x -> is_word rw (f x)) ->
  (forall x, is_word sw x ->
    (Tf x <= k * N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2))%N) ->
  (T_tnum_map sw rw f Tf a <= (2 * k + 1024) * N.of_nat
    ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2 + tnum_bits a))%N.
Proof.
  intros sw rw f Tf a k Hword Hcallback.
  pose proof (tnum_map_time sw rw f Tf a Hword) as Hmap.
  pose proof (Hcallback _ (tnum_max_word sw a)) as Hmax.
  pose proof (Hcallback _ (tnum_min_word sw a)) as Hmin.
  rewrite ?Nat2N.inj_add in *.
  set (square := N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2)) in *.
  assert (Hlinear : (N.of_nat (Pos.to_nat sw + Pos.to_nat rw + 1) <= square)%N).
  { unfold square. clear - sw rw. apply time_of_nat_le. cbn [Nat.pow]. nia. }
  clearbody square. rewrite ?Nat2N.inj_add in Hlinear. nia.
Qed.

(** A normalized endpoint makes the wrapping callback fit the width budget. *)
Lemma table_wrap_callback_time : forall sw rw x, is_word sw x ->
  (16 + T_tnum_wrap rw x <=
    2048 * N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2))%N.
Proof.
  intros sw rw x Hword. pose proof (tnum_word_bits sw x Hword) as Hbits.
  pose proof (tnum_wrap_time rw x) as Hwrap.
  pose proof (WordTime.time_square_floor (Pos.to_nat rw + Z.size_nat x + 1)
    (Pos.to_nat sw + Pos.to_nat rw + 1)
    ltac:(clear - Hbits; lia) ltac:(clear; lia)) as Hlinear.
  pose proof (WordTime.time_square_floor 1
    (Pos.to_nat sw + Pos.to_nat rw + 1)
    ltac:(clear; lia) ltac:(clear; lia)) as Hpositive.
  clear Hword Hbits.
  set (square := N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2)) in *.
  clearbody square. lia.
Qed.

(** Sign extension reads a normalized source word before the destination mask. *)
Lemma table_signed_callback_time : forall sw rw x, is_word sw x ->
  (16 + T_signed sw x + T_tnum_wrap rw (signed sw x) <=
    2048 * N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2))%N.
Proof.
  intros sw rw x Hword. pose proof (tnum_word_bits sw x Hword) as Hbits.
  pose proof (WordTime.word_signed_size_bound sw x) as Hsignedbits.
  assert (Hsigned : (T_signed sw x <=
    512 * N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2))%N).
  { eapply (WordTime.time_square_scale _ 128 _ _ 2);
      [apply WordTime.word_signed_time_bound|clear - Hbits; lia]. }
  pose proof (tnum_wrap_time rw (signed sw x)) as Hwrap.
  pose proof (WordTime.time_square_floor (Pos.to_nat rw + Z.size_nat (signed sw x) + 1)
    (Pos.to_nat sw + Pos.to_nat rw + 1)
    ltac:(clear - Hsignedbits; lia) ltac:(clear; lia)) as Hlinear.
  pose proof (WordTime.time_square_floor 1
    (Pos.to_nat sw + Pos.to_nat rw + 1)
    ltac:(clear; lia) ltac:(clear; lia)) as Hpositive.
  clear Hword Hbits Hsignedbits.
  set (square := N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2)) in *.
  clearbody square. lia.
Qed.

(** A checked extraction offset bounds conversion, power construction and division. *)
Lemma table_extract_callback_time : forall sw rw lo x,
  (lo < Pos.to_nat sw)%nat -> is_word sw x ->
  (16 + Op.Z.T_of_nat lo + Word.Z.T_pow 2 (Z.of_nat lo) +
    Std.Z.T_div x (2 ^ Z.of_nat lo) + T_tnum_wrap rw (x / 2 ^ Z.of_nat lo) <=
    2048 * N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2))%N.
Proof.
  intros sw rw lo x Hlo Hword.
  pose proof (tnum_word_bits sw x Hword) as Hbits.
  pose proof (tnum_pow2_bits (Z.of_nat lo) ltac:(clear; lia)) as Hpowerbits.
  rewrite Nat2Z.id in Hpowerbits.
  pose proof (WordTime.integer_div_size_time_bound (Pos.to_nat sw) x
    (2 ^ Z.of_nat lo) Hbits ltac:(clear - Hlo Hpowerbits; lia)) as Hdivision.
  pose proof (WordTime.integer_positive_div_size x (2 ^ Z.of_nat lo)
    ltac:(clear; apply Z.pow_pos_nonneg; lia)) as Hquotientbits.
  pose proof (tnum_wrap_time rw (x / 2 ^ Z.of_nat lo)) as Hwrap.
  pose proof (tnum_pow2_time (Z.of_nat lo) ltac:(clear; lia)) as Hpower.
  rewrite Nat2Z.id in Hpower.
  pose proof (WordTime.natural_to_integer_time_bound lo) as Hconvert.
  pose proof (WordTime.time_square_weaken _ 64 (Pos.to_nat sw + 1)
    (Pos.to_nat sw + Pos.to_nat rw + 1) Hdivision ltac:(clear; lia)) as Hdivisionwide.
  pose proof (WordTime.time_square_weaken _ 8 (lo + 1)
    (Pos.to_nat sw + Pos.to_nat rw + 1) Hconvert
    ltac:(clear - Hlo; lia)) as Hconvertwide.
  pose proof (WordTime.time_square_floor (lo + 1)
    (Pos.to_nat sw + Pos.to_nat rw + 1)
    ltac:(clear - Hlo; lia) ltac:(clear; lia)) as Hpowerlinear.
  pose proof (WordTime.time_square_floor (Pos.to_nat rw + Z.size_nat (x / 2 ^ Z.of_nat lo) + 1)
    (Pos.to_nat sw + Pos.to_nat rw + 1)
    ltac:(clear - Hquotientbits Hbits; lia) ltac:(clear; lia)) as Hwraplinear.
  pose proof (WordTime.time_square_floor 1
    (Pos.to_nat sw + Pos.to_nat rw + 1)
    ltac:(clear; lia) ltac:(clear; lia)) as Hpositive.
  clear Hlo Hword Hbits Hpowerbits Hquotientbits Hdivision Hconvert.
  set (square := N.of_nat ((Pos.to_nat sw + Pos.to_nat rw + 1) ^ 2)) in *.
  clearbody square. lia.
Qed.

Module ForwardClaims (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG).
  Module P := KnownBitsCode L C.
  Module F := KnownBitsOpsCode L C P.
Lemma tnum_forward_mul_same : forall w a b,
  F.tnum_forward_raw bvmul [(w, a); (w, b)] w =
    tnum_mul_with (C.multiplier) w a b.
Proof.
  intros w a b. unfold F.tnum_forward_raw. now rewrite !Pos.eqb_refl.
Qed.
Lemma tnum_forward_one_sound : forall o w a x rw z,
  is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, a)] rw) z.
Proof.
  intros o w a x rw z Hx Ha Heval. destruct o; try apply tnum_top_sound.
  - rewrite (eval_op_fun1 bvnot w x UNot eq_refl) in Heval.
    injection Heval as <- <-. now apply tnum_not_sound.
  - rewrite (eval_op_fun1 bvneg w x UNeg eq_refl) in Heval.
    injection Heval as <- <-. now apply tnum_neg_sound.
  - rewrite (eval_op_fun1 bvclz w x UClz eq_refl) in Heval.
    injection Heval as <- <-. exact (tnum_count_sound bvclz w UClz x ltac:(tauto) eq_refl).
  - rewrite (eval_op_fun1 bvctz w x UCtz eq_refl) in Heval.
    injection Heval as <- <-. exact (tnum_count_sound bvctz w UCtz x ltac:(tauto) eq_refl).
  - rewrite (eval_op_fun1 bvpopcnt w x UPopcnt eq_refl) in Heval.
    injection Heval as <- <-.
    exact (tnum_count_sound bvpopcnt w UPopcnt x ltac:(tauto) eq_refl).
  - rewrite eval_op_zext in Heval. injection Heval as <- <-.
    rewrite (wrap_id w x Hx).
    change (tnum_gamma (w + extra)%positive
      (tnum_map w (w + extra)%positive (tnum_wrap (w + extra)%positive) a)
      (wrap (w + extra)%positive x)).
    rewrite (tnum_map_ext _ _ _ (wrap (w + extra)%positive) a) by
      apply tnum_wrap_agrees.
    apply tnum_map_sound; try assumption. apply tnum_zext_copy, width_add_le.
  - rewrite eval_op_sext in Heval. injection Heval as <- <-.
    change (tnum_gamma (w + extra)%positive
      (tnum_map w (w + extra)%positive
        (fun v => tnum_wrap (w + extra)%positive (signed w v)) a)
      (wrap (w + extra)%positive (signed w x))).
    rewrite (tnum_map_ext _ _ _
      (fun v => wrap (w + extra)%positive (signed w v)) a) by
      (intro v; apply tnum_wrap_agrees).
    apply (tnum_map_sound w (w + extra)%positive
      (fun v => wrap (w + extra)%positive (signed w v)) a x); try assumption.
    apply tnum_sext_copy.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w) eqn:Hle;
      [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx).
    change (tnum_gamma target (tnum_map w target (tnum_wrap target) a) (wrap target x)).
    rewrite (tnum_map_ext _ _ _ (wrap target) a) by apply tnum_wrap_agrees.
    apply tnum_map_sound; try assumption. apply tnum_trunc_copy. now apply Pos.leb_le.
  - rewrite eval_op_extract in Heval.
    destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)) eqn:Hshape;
      [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx).
    apply andb_true_iff in Hshape as [Hlo Hhi].
    apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
    change (tnum_gamma (Pos.of_nat (S (hi - lo)))
      (tnum_map w (Pos.of_nat (S (hi - lo)))
        (fun v => tnum_wrap (Pos.of_nat (S (hi - lo))) (v / 2 ^ Z.of_nat lo)) a)
      (wrap (Pos.of_nat (S (hi - lo))) (x / 2 ^ Z.of_nat lo))).
    rewrite (tnum_map_ext _ _ _
      (fun v => wrap (Pos.of_nat (S (hi - lo))) (v / 2 ^ Z.of_nat lo)) a) by
      (intro v; apply tnum_wrap_agrees).
    apply (tnum_map_sound w (Pos.of_nat (S (hi - lo)))
      (fun v => wrap (Pos.of_nat (S (hi - lo))) (v / 2 ^ Z.of_nat lo)) a x);
      try assumption. apply tnum_extract_copy; [lia|].
    rewrite <- positive_nat_Z, Nat2Pos.id by lia.
    rewrite <- (positive_nat_Z w). lia.
Qed.

Lemma tnum_binary_transfer_sound : forall o w f a b x y,
  word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (F.tnum_forward_raw o [(w, a); (w, b)] w) (eval_binary_tag f w x y).
Proof.
  intros o w f a b x y Hf Hx Hy Ha Hb.
  destruct o; try discriminate Hf; injection Hf as <-;
    first [now apply tnum_add_sound|now apply tnum_sub_sound|
      rewrite tnum_forward_mul_same; now apply tnum_mul_with_sound|
      now apply tnum_udiv_sound|now apply tnum_urem_sound|apply tnum_top_sound|
      now apply tnum_srem_sound|now apply tnum_and_sound|now apply tnum_or_sound|
      now apply tnum_xor_sound|
      eapply tnum_variable_sound; try eassumption; try reflexivity;
        unfold tnum_shift_op; tauto].
Qed.
Lemma tnum_forward_fun2_sound : forall o w v f a b x y rw z,
  word_fun2 o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
  pose proof (eval_op_fun2_width o f w v x y (rw, z) Hf Heval) as ->.
  rewrite (eval_op_fun2 o v x y f Hf) in Heval.
  injection Heval as <- <-. now apply (tnum_binary_transfer_sound o v f).
Qed.
Lemma tnum_forward_cmp_sound : forall o w v f a b x y rw z,
  word_cmp o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
  pose proof (eval_op_cmp_width o f w v x y (rw, z) Hf Heval) as ->.
  rewrite (eval_op_cmp o v x y f Hf) in Heval. injection Heval as <- <-.
  pose proof (tnum_compare_sound o v f a b x y Hf Hx Hy Ha Hb) as Hsound.
  destruct o; try discriminate Hf; exact Hsound.
Qed.
Lemma tnum_forward_two_sound : forall o w v a b x y rw z,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v a b x y rw z Hx Hy Ha Hb Heval.
  destruct o; try apply tnum_top_sound;
    try (eapply tnum_forward_fun2_sound; try eassumption; reflexivity);
    try (eapply tnum_forward_cmp_sound; try eassumption; reflexivity).
  rewrite eval_op_concat in Heval. injection Heval as <- <-.
  rewrite (wrap_id w x Hx), (wrap_id v y Hy).
  apply tnum_gamma_wrap. now apply tnum_concat_sound.
Qed.
Lemma tnum_forward_three_sound : forall o w v u c a b k x y rw z,
  is_word w k -> is_word v x -> is_word u y ->
  tnum_gamma w c k -> tnum_gamma v a x -> tnum_gamma u b y ->
  eval_op o [(w, k); (v, x); (u, y)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, c); (v, a); (u, b)] rw) z.
Proof.
  intros o w v u c a b k x y rw z Hk Hx Hy Hc Ha Hb Heval.
  destruct o; try apply tnum_top_sound.
  destruct (eval_op_ite_width w v u k x y (rw, z) Heval) as [Hw Hvu]. subst w u.
  rewrite eval_op_ite in Heval. injection Heval as <- <-.
  rewrite (wrap_id 1%positive k Hk), (wrap_id v x Hx), (wrap_id v y Hy).
  now apply tnum_ite_sound.
Qed.
Theorem known_bits_nullary : forall o rw, F.tnum_forward_raw o [] rw = tnum_top.
Proof. destruct o; reflexivity. Qed.
End ForwardClaims.

Module KnownBitsForwardProof (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG).
  Module P := KnownBitsCode L C.
  Module F := KnownBitsOpsCode L C P.
  Module Claims := ForwardClaims L C.

  (** Every supplied forward entry preserves successful concrete evaluation. *)
  Theorem tnum_forward_raw_sound : forall o wps ys rw z,
    Forall2 tnum_payload_sound wps ys -> eval_op o ys = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o wps rw) z.
  Proof.
    intros o wps ys rw z Hgamma Heval.
    destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
    - destruct o; apply tnum_top_sound.
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
      destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
      exact (Claims.tnum_forward_one_sound o w a x rw z Hx Ha Heval).
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
      inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
      destruct y as [wy x], y' as [vy y].
      destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
      cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
      exact (Claims.tnum_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval).
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
      inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
      inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
      inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
      destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
      cbn in Hwx, Hvy, Hut, Hx, Hy, Ht, Ha, Hb, Hc. subst wy vy uy.
      exact (Claims.tnum_forward_three_sound o w v u a b c x y t rw z
        Hx Hy Ht Ha Hb Hc Heval).
    - destruct o; apply tnum_top_sound.
  Qed.
End KnownBitsForwardProof.
Theorem known_bits_eval_primitive_bound : forall o (xs : list word),
  Nat.eqb (length xs) (arity o) = true -> (length xs <= 3)%nat.
Proof.
  intros o xs Hlength. apply Nat.eqb_eq in Hlength. rewrite Hlength.
  destruct o; repeat constructor.
Qed.

(* The landed shape, table and word-law bundles used removed closure-bearing records.
   WORD_TABLE now states the corresponding operation-level contracts, which the supplied
   payload proof below derives from the arithmetic and gamma laws of KNOWN_BITS.
Lemma known_bits_shape_laws :
  transfer_sem known_bits_shape (payload_sound tnum_gamma) (word_output tnum_gamma)
    word_context.
Theorem known_bits_table_laws : forall opts,
  table_laws (known_bits_table opts) known_bits_shape (payload_sound tnum_gamma)
    (word_output tnum_gamma) word_context.
Lemma known_bits_table_refines : forall opts,
  table_refines (known_bits_table opts) known_bits_shape
    (fun wp q => leb (tnum_lattice (fst wp)) q (snd wp) = true).
Theorem known_bits_word_builder_laws : forall opts,
  word_laws (known_bits_word_builder opts) tnum_gamma.
Theorem known_bits_word_laws : forall opts,
  word_laws (known_bits_word_domain opts) tnum_gamma.

   These source statements refer to removed charged wrappers. The corresponding
   uncharged evaluation is eval_op and the configured forward body is F.tnum_forward_raw.
Theorem known_bits_eval_equation : forall o xs,
  Cost.value (known_bits_eval_c o xs) = eval_op o xs.
Theorem known_bits_nonempty_delegation : forall opts o x xs rw,
  pforward_c (known_bits_word_domain opts) o (x :: xs) rw =
    pforward_c (known_bits_word_builder opts) o (x :: xs) rw.
Theorem known_bits_nonmultiplication_agrees : forall opts opts' o, o <> bvmul ->
  pforward_c (known_bits_word_domain opts) o =
    pforward_c (known_bits_word_domain opts') o.
*)

(** Supplied payload operations are used only through their public soundness laws. *)
Module KnownBitsSuppliedForwardProof (L : WORD_LANGUAGE) (C : TNUM_CONFIG)
    (K : KNOWN_BITS L C).
  Module F := KnownBitsOpsCode L C K.
  Module Base := ForwardClaims L C.

  Lemma tnum_forward_one_sound : forall o w a x rw z,
    is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o [(w, a)] rw) z.
  Proof.
    intros o w a x rw z Hx Ha Heval.
    pose proof (Base.tnum_forward_one_sound o w a x rw z Hx Ha Heval) as Hbase.
    pose proof (proj2 (K.gamma_tnum w a x) Ha) as Hpayload.
    destruct o; try exact Hbase.
    - pose proof (eval_op_fun1 bvnot w x UNot eq_refl) as Hop.
      rewrite Hop in Heval. injection Heval as <- <-.
      apply (proj1 (K.gamma_tnum _ _ _)).
      eapply K.tnum_not_sound; eassumption.
    - pose proof (eval_op_fun1 bvneg w x UNeg eq_refl) as Hop.
      rewrite Hop in Heval. injection Heval as <- <-.
      apply (proj1 (K.gamma_tnum _ _ _)).
      eapply K.tnum_neg_sound; eassumption.
  Qed.

  Lemma tnum_binary_transfer_sound : forall o w f a b x y,
    word_fun2 o = Some f -> is_word w x -> is_word w y ->
    tnum_gamma w a x -> tnum_gamma w b y ->
    tnum_gamma w (F.tnum_forward_raw o [(w, a); (w, b)] w)
      (eval_binary_tag f w x y).
  Proof.
    intros o w f a b x y Hf Hx Hy Ha Hb.
    pose proof (Base.tnum_binary_transfer_sound o w f a b x y Hf Hx Hy Ha Hb) as Hbase.
    pose proof (proj2 (K.gamma_tnum w a x) Ha) as Hleft.
    pose proof (proj2 (K.gamma_tnum w b y) Hb) as Hright.
    pose proof (eval_op_fun2 o w x y f Hf) as Heval.
    destruct o; try discriminate Hf; try exact Hbase.
    all: cbn [F.tnum_forward_raw]; try rewrite !Pos.eqb_refl;
      cbn [andb]; try rewrite K.multiplier_selected;
      apply (proj1 (K.gamma_tnum _ _ _)).
    all: first [eapply (K.tnum_add_sound w a b x y); eassumption
      | eapply (K.tnum_sub_sound w a b x y); eassumption
      | eapply (K.tnum_and_sound w a b x y); eassumption
      | eapply (K.tnum_or_sound w a b x y); eassumption
      | eapply (K.tnum_xor_sound w a b x y); eassumption
      | eapply (K.tnum_mul_with_sound C.multiplier w a b x y); eassumption
      | eapply (K.tnum_variable_sound _ w a b x y); [cbn; tauto|eassumption|eassumption|
          eassumption|eassumption|eassumption]].
  Qed.

  Lemma tnum_forward_fun2_sound : forall o w v f a b x y rw z,
    word_fun2 o = Some f -> is_word w x -> is_word v y ->
    tnum_gamma w a x -> tnum_gamma v b y ->
    eval_op o [(w, x); (v, y)] = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
  Proof.
    intros o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
    pose proof (eval_op_fun2_width o f w v x y (rw, z) Hf Heval) as ->.
    rewrite (eval_op_fun2 o v x y f Hf) in Heval.
    injection Heval as <- <-. now apply (tnum_binary_transfer_sound o v f).
  Qed.

  Lemma tnum_forward_two_sound : forall o w v a b x y rw z,
    is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
    eval_op o [(w, x); (v, y)] = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
  Proof.
    intros o w v a b x y rw z Hx Hy Ha Hb Heval.
    pose proof (Base.tnum_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval)
      as Hbase.
    destruct o; try exact Hbase;
      eapply tnum_forward_fun2_sound; try eassumption; reflexivity.
  Qed.

  Lemma tnum_forward_three_sound : forall o w v u c a b k x y rw z,
    is_word w k -> is_word v x -> is_word u y ->
    tnum_gamma w c k -> tnum_gamma v a x -> tnum_gamma u b y ->
    eval_op o [(w, k); (v, x); (u, y)] = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o [(w, c); (v, a); (u, b)] rw) z.
  Proof.
    intros o w v u c a b k x y rw z Hk Hx Hy Hc Ha Hb Heval.
    pose proof (Base.tnum_forward_three_sound o w v u c a b k x y rw z
      Hk Hx Hy Hc Ha Hb Heval) as Hbase.
    destruct o; exact Hbase.
  Qed.

  (** Successful evaluation is retained by any payload satisfying KNOWN_BITS. *)
  Theorem tnum_forward_raw_sound : forall o wps ys rw z,
    Forall2 tnum_payload_sound wps ys -> eval_op o ys = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o wps rw) z.
  Proof.
    intros o wps ys rw z Hgamma Heval.
    destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
    - destruct o; apply tnum_top_sound.
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
      destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
      exact (tnum_forward_one_sound o w a x rw z Hx Ha Heval).
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
      inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
      destruct y as [wy x], y' as [vy y].
      destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
      cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
      exact (tnum_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval).
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
      inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
      inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
      inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
      destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
      cbn in Hwx, Hvy, Hut, Hx, Hy, Ht, Ha, Hb, Hc. subst wy vy uy.
      exact (tnum_forward_three_sound o w v u a b c x y t rw z
        Hx Hy Ht Ha Hb Hc Heval).
    - destruct o; apply tnum_top_sound.
  Qed.
End KnownBitsSuppliedForwardProof.

(** The unsigned numeric view reads the normalized integer stored in a word. *)
Module KnownBitsNumU <: NUM_VIEW BitsLang.
  Definition num (c : BitsLang.val) : Z := snd c.
End KnownBitsNumU.

Module KnownBitsRangeCode (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG)
    (K : KNOWN_BITS_OPS L C).
  Definition range (a : tagged K.p) : bnd * bnd :=
    match a with
    | TBot => (PosInf, NegInf)
    | TVal w p =>
      if tnum_empty w p then (PosInf, NegInf)
      else (Fin (tnum_min w p), Fin (tnum_max w p))
    | TAny => (NegInf, PosInf)
    end.
End KnownBitsRangeCode.

(** A tagged known-bit payload exposes its least and greatest unsigned members. *)
Module KnownBitsRange (L : WORD_LANGUAGE) (C : TNUM_CONFIG) (K : KNOWN_BITS L C)
    (D : VALUE_DOMAIN BitsLang with Definition t := tagged K.p
      with Definition gamma := tagged_gamma L.is_word K.pgamma)
    <: RANGE_QUERY BitsLang KnownBitsNumU D.
  Include KnownBitsRangeCode L C K.

  (** Every represented integer lies between the queried endpoints. *)
  Lemma range_sound : forall a c,
    D.gamma a c -> in_bnd (fst (range a)) (snd (range a)) (KnownBitsNumU.num c).
  Proof.
    intros [|w a|] [v z] Hgamma.
    - contradiction.
    - destruct Hgamma as [Hwidth [Hword Hmask]].
      apply (proj1 (K.gamma_tnum w a z)) in Hmask.
      cbn [range KnownBitsNumU.num fst snd].
      rewrite (tnum_empty_sound w a z Hmask).
      exact (tnum_unsigned_bounds w a z Hword Hmask).
    - split; exact I.
  Qed.
End KnownBitsRange.
