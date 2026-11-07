(** * Known-bit comparisons and control

    Endpoint bounds decide comparisons and sign bias reuses the unsigned rules.
    For example, a known negative word is strictly less than a known nonnegative word.
    Builds on: DomainsTnumArith, DomainsTnumMul and the public Bits signed equations. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith BitsOp.
From Galois.Domains Require Import DomainsTnum DomainsTnumArith DomainsTnumMul.

Local Open Scope Z_scope.

Definition tnum_order (strict : bool) (w : width) (a b : tnum) : tnum :=
  if (if strict then tnum_max w a <? tnum_min w b
      else tnum_max w a <=? tnum_min w b) then tnum_const 1%positive 1
  else if (if strict then tnum_max w b <=? tnum_min w a
           else tnum_max w b <? tnum_min w a) then tnum_const 1%positive 0
  else tnum_top.

(** Separated unsigned endpoint bounds decide strict and non-strict comparisons. *)
Theorem tnum_order_sound : forall strict w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_order strict w a b)
    (if (if strict then x <? y else x <=? y) then 1 else 0).
Proof.
  intros strict w a b x y Hx Hy Ha Hb.
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hax.
  pose proof (tnum_unsigned_bounds w b y Hy Hb) as Hby.
  unfold tnum_order. destruct strict.
  - destruct (tnum_max w a <? tnum_min w b) eqn:Htrue.
    + apply Z.ltb_lt in Htrue. rewrite (proj2 (Z.ltb_lt x y)) by lia.
      exact (tnum_const_sound 1%positive 1).
    + destruct (tnum_max w b <=? tnum_min w a) eqn:Hfalse; [|apply tnum_top_sound].
      apply Z.leb_le in Hfalse. rewrite (proj2 (Z.ltb_ge x y)) by lia.
      exact (tnum_const_sound 1%positive 0).
  - destruct (tnum_max w a <=? tnum_min w b) eqn:Htrue.
    + apply Z.leb_le in Htrue. rewrite (proj2 (Z.leb_le x y)) by lia.
      exact (tnum_const_sound 1%positive 1).
    + destruct (tnum_max w b <? tnum_min w a) eqn:Hfalse; [|apply tnum_top_sound].
      apply Z.ltb_lt in Hfalse. rewrite (proj2 (Z.leb_gt x y)) by lia.
      exact (tnum_const_sound 1%positive 0).
Qed.

Definition tnum_equal (w : width) (a b : tnum) : tnum :=
  if tnum_empty w (tnum_meet w a b) then tnum_const 1%positive 0 else
  match tnum_constant w a, tnum_constant w b with
  | Some x, Some y => tnum_const 1%positive (if x =? y then 1 else 0)
  | _, _ => tnum_top
  end.

(** Incompatible masks prove disequality and two constant masks decide equality. *)
Theorem tnum_equal_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_equal w a b) (if x =? y then 1 else 0).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_equal.
  destruct (tnum_empty w (tnum_meet w a b)) eqn:Hempty.
  - destruct (x =? y) eqn:Hxy.
    + apply Z.eqb_eq in Hxy. subst y.
      pose proof (tnum_empty_sound w _ x (tnum_meet_sound w a b x Ha Hb)). congruence.
    + exact (tnum_const_sound 1%positive 0).
  - destruct (tnum_constant w a) as [ca|] eqn:Hca,
      (tnum_constant w b) as [cb|] eqn:Hcb; try apply tnum_top_sound.
    rewrite (tnum_constant_value w a x ca Hx Ha Hca),
      (tnum_constant_value w b y cb Hy Hb Hcb).
    destruct (ca =? cb); apply tnum_const_sound.
Qed.

Definition tnum_bias (w : width) (a : tnum) : tnum :=
  tnum_xor w a (tnum_const w (half w)).

Lemma tnum_bias_sound : forall w a x,
  tnum_gamma w a x -> tnum_gamma w (tnum_bias w a) (wxor w x (half w)).
Proof.
  intros w a x Ha. unfold tnum_bias. apply tnum_xor_sound; [exact Ha|].
  rewrite <- (wrap_id w (half w)) at 2 by
    (unfold is_word; pose proof (half_pos w); pose proof (modulus_half w); lia).
  apply tnum_const_sound.
Qed.

Definition tnum_compare (o : op) (w : width) (a b : tnum) : tnum :=
  match o with
  | bveq => tnum_equal w a b
  | bvne => tnum_not 1%positive (tnum_equal w a b)
  | bvult => tnum_order true w a b
  | bvule => tnum_order false w a b
  | bvslt => tnum_order true w (tnum_bias w a) (tnum_bias w b)
  | bvsle => tnum_order false w (tnum_bias w a) (tnum_bias w b)
  | _ => tnum_top
  end.

(** Every comparison entry describes its concrete one-bit result. *)
Theorem tnum_compare_sound : forall o w f a b x y,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_compare o w a b) (if f w x y then 1 else 0).
Proof.
  intros o w f a b x y Hf Hx Hy Ha Hb. destruct o;
    try discriminate Hf; injection Hf as <-; cbn [tnum_compare].
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy). now apply tnum_equal_sound.
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy).
    pose proof (tnum_not_sound 1%positive (tnum_equal w a b)
      (if x =? y then 1 else 0) (tnum_equal_sound w a b x y Hx Hy Ha Hb)) as Hnot.
    destruct (x =? y); exact Hnot.
  - rewrite wult_value, (wrap_id w x Hx), (wrap_id w y Hy).
    exact (tnum_order_sound true w a b x y Hx Hy Ha Hb).
  - rewrite wule_value, (wrap_id w x Hx), (wrap_id w y Hy).
    exact (tnum_order_sound false w a b x y Hx Hy Ha Hb).
  - rewrite wslt_bias, wult_value. rewrite !wrap_id by apply wxor_is_word.
    apply (tnum_order_sound true w); try apply wxor_is_word; now apply tnum_bias_sound.
  - assert (Hbias : wsle w x y = (wxor w x (half w) <=? wxor w y (half w))).
    { rewrite wsle_value, !wxor_half_value.
      destruct (signed w x <=? signed w y) eqn:Hxy;
        destruct (signed w x + half w <=? signed w y + half w) eqn:Hbias;
        try reflexivity; apply Z.leb_le in Hxy || apply Z.leb_gt in Hxy;
        apply Z.leb_le in Hbias || apply Z.leb_gt in Hbias; lia. }
    rewrite Hbias. apply (tnum_order_sound false w);
      try apply wxor_is_word; now apply tnum_bias_sound.
Qed.

Definition tnum_count (w : width) : tnum := tnum_upper w (Zpos w).

(** The legacy count rule retains the shared upper bound of the three count primitives. *)
Theorem tnum_count_sound : forall o w f x,
  (o = bvclz \/ o = bvctz \/ o = bvpopcnt) -> word_fun1 o = Some f ->
  tnum_gamma w (tnum_count w) (f w x).
Proof.
  intros o w f x [Ho|[Ho|Ho]] Hf; subst o; injection Hf as <-;
    apply tnum_upper_sound; first [apply wclz_range|apply tnum_ctz_range|apply wpopcnt_range].
Qed.

Lemma tnum_half_value : forall w, half w = 2 ^ (Zpos w - 1).
Proof.
  intro w. pose proof (modulus_half w) as Hhalf. rewrite modulus_value in Hhalf.
  assert (Hpow : 2 ^ Zpos w = 2 * 2 ^ (Zpos w - 1)).
  { replace (Zpos w) with ((Zpos w - 1) + 1) at 1 by lia.
    rewrite Z.pow_add_r, Z.pow_1_r by lia. ring. }
  rewrite Hpow in Hhalf. lia.
Qed.

Lemma tnum_urem_bound : forall w x y,
  is_word w x -> is_word w y -> 0 <= wurem w x y <= x.
Proof.
  intros w x y Hx Hy. destruct (Z.eq_dec y 0) as [->|Hnz].
  - rewrite wurem_zero, (wrap_id w x Hx). unfold is_word in Hx. lia.
  - rewrite wurem_spec by assumption. split.
    + apply Z.mod_pos_bound. unfold is_word in Hy. lia.
    + apply Z.mod_le; unfold is_word in *; lia.
Qed.

Definition tnum_srem (w : width) (a : tnum) : tnum :=
  Tnum (wand w (zeros a) (half w)) 0.

(** A known nonnegative dividend keeps the result sign clear under signed remainder. *)
Theorem tnum_srem_sound : forall w a x y,
  is_word w x -> is_word w y -> tnum_gamma w a x ->
  tnum_gamma w (tnum_srem w a) (wsrem w x y).
Proof.
  intros w a x y Hx Hy Ha. apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
  apply tnum_gamma_bits. split; intros i Hi Hbit; cbn [tnum_srem zeros ones] in Hbit.
  - rewrite tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Hclear Hsign].
    rewrite tnum_half_value, Z.pow2_bits_eqb in Hsign by lia.
    apply Z.eqb_eq in Hsign. subst i.
    assert (Hmsb : msb w x = false) by (rewrite msb_testbit; now apply Hz).
    assert (Hhalf : x < half w).
    { rewrite msb_half, (wrap_id w x Hx) in Hmsb.
      apply negb_false_iff, Z.ltb_lt in Hmsb. exact Hmsb. }
    rewrite wsrem_value, Hmsb. destruct (msb w y).
    + pose proof (tnum_urem_bound w x (wneg w y) Hx
        (word_fun1_is_word bvneg wneg w y eq_refl)) as Hbound.
      rewrite <- (Z.mod_small (wurem w x (wneg w y)) (half w) ltac:(lia)).
      rewrite tnum_half_value. apply Z.mod_pow2_bits_high. lia.
    + pose proof (tnum_urem_bound w x y Hx Hy) as Hbound.
      rewrite <- (Z.mod_small (wurem w x y) (half w) ltac:(lia)).
      rewrite tnum_half_value. apply Z.mod_pow2_bits_high. lia.
  - rewrite Z.bits_0 in Hbit. discriminate.
Qed.

Definition tnum_ite (w : width) (c a b : tnum) : tnum :=
  match tnum_constant 1%positive c with
  | Some k => tnum_normalise w (if k =? 1 then a else b)
  | None => tnum_join w a b
  end.

(** Conditional selection keeps a known branch and otherwise joins both branch facts. *)
Theorem tnum_ite_sound : forall w c a b k x y,
  is_word 1%positive k -> tnum_gamma 1%positive c k ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_ite w c a b) (if k =? 1 then x else y).
Proof.
  intros w c a b k x y Hk Hc Ha Hb. unfold tnum_ite.
  destruct (tnum_constant 1%positive c) as [v|] eqn:Hconstant.
  - rewrite (tnum_constant_value 1%positive c k v Hk Hc Hconstant).
    apply tnum_normalise_sound. destruct (v =? 1); assumption.
  - apply tnum_join_sound. destruct (k =? 1); auto.
Qed.
