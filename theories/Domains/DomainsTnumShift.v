(** * Constant known-bit shifts

    Bit-copy maps transfer facts through shifts and changes of word width.
    For example, shifting a known low one left by two makes bit two a known one.
    Builds on: DomainsTnum and the public Bits shift and signed-bit laws. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsTnum.

Local Open Scope Z_scope.

(** Each output bit is either a fixed zero or a copy of one valid source bit. *)
Definition tnum_bit_copy (sw rw : width) (f : Z -> Z) : Prop :=
  forall i, 0 <= i < Zpos rw ->
    (forall x, is_word sw x -> Z.testbit (f x) i = false) \/
    exists j, 0 <= j < Zpos sw /\
      forall x, is_word sw x -> Z.testbit (f x) i = Z.testbit x j.

Definition tnum_map (sw rw : width) (f : Z -> Z) (a : tnum) : tnum :=
  Tnum (wnot rw (f (tnum_max sw a))) (wrap rw (f (tnum_min sw a))).

(** Applying a bit-copy map to the endpoints retains every concrete mapped value. *)
Theorem tnum_map_sound : forall sw rw f a x,
  tnum_bit_copy sw rw f -> is_word sw x -> tnum_gamma sw a x ->
  tnum_gamma rw (tnum_map sw rw f a) (f x).
Proof.
  intros sw rw f a x Hcopy Hx Ha. apply tnum_gamma_bits in Ha.
  destruct Ha as [Hz Ho]. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_map zeros ones] in Hbit.
  - rewrite tnum_not_bit in Hbit by exact Hi. apply negb_true_iff in Hbit.
    destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]]; [now apply Hclear|].
    rewrite Hsource in Hbit by apply wnot_is_word.
    rewrite Hsource by exact Hx. unfold tnum_max in Hbit.
    rewrite tnum_not_bit in Hbit by exact Hj. apply negb_false_iff in Hbit.
    now apply Hz.
  - rewrite tnum_wrap_bit in Hbit by exact Hi.
    destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]].
    + rewrite Hclear in Hbit by apply wrap_is_word. discriminate.
    + rewrite Hsource in Hbit by apply wrap_is_word. rewrite Hsource by exact Hx.
      unfold tnum_min in Hbit. rewrite tnum_wrap_bit in Hbit by exact Hj. now apply Ho.
Qed.

(** A concrete left shift copies the source suffix and supplies low zero bits. *)
Theorem tnum_shl_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => wshl w x k).
Proof.
  intros w k Hk i Hi. destruct (k <=? i) eqn:Hsmall.
  - apply Z.leb_le in Hsmall. right. exists (i - k). split; [unfold is_word in Hk; lia|].
    intros x Hx. rewrite testbit_wshl by (try assumption; lia).
    rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)),
      (proj2 (Z.leb_le k i) Hsmall). reflexivity.
  - left. intros x Hx. rewrite testbit_wshl by (try assumption; lia).
    rewrite Hsmall, andb_false_r. reflexivity.
Qed.

(** A logical right shift copies the source prefix and supplies high zero bits. *)
Theorem tnum_lshr_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => wlshr w x k).
Proof.
  intros w k Hk i Hi. destruct (Z_lt_ge_dec (i + k) (Zpos w)) as [Hsmall|Hbig].
  - right. exists (i + k). split; [unfold is_word in Hk; lia|].
    intros x Hx. rewrite testbit_wlshr by (try assumption; lia).
    now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
  - left. intros x Hx. rewrite testbit_wlshr by (try assumption; lia).
    rewrite (word_bits_high w x (i + k) Hx ltac:(lia)). apply andb_false_r.
Qed.

(** An arithmetic right shift copies source bits and repeats the sign bit. *)
Theorem tnum_ashr_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => washr w x k).
Proof.
  intros w k Hk i Hi. right. exists (Z.min (i + k) (Zpos w - 1)).
  split; [unfold is_word in Hk; lia|]. intros x Hx.
  rewrite testbit_washr by (try assumption; lia).
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

Definition tnum_shift (o : op) (w : width) (a : tnum) (k : Z) : tnum :=
  match word_fun2 o with
  | Some f => tnum_map w w (fun x => f w x k) a
  | None => tnum_top
  end.

(** Each supported constant shift contains the corresponding concrete result. *)
Theorem tnum_shift_sound : forall o w a x k f,
  (o = bvshl \/ o = bvlshr \/ o = bvashr) ->
  word_fun2 o = Some f -> is_word w x -> is_word w k -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shift o w a k) (f w x k).
Proof.
  intros o w a x k f Ho Hf Hx Hk Ha. unfold tnum_shift. rewrite Hf.
  apply (tnum_map_sound w w (fun z => f w z k) a x); try assumption.
  destruct Ho as [Ho|[Ho|Ho]]; subst o; injection Hf as <-.
  - now apply tnum_shl_copy.
  - now apply tnum_lshr_copy.
  - now apply tnum_ashr_copy.
Qed.

(** Zero extension copies low bits and supplies zero in the additional positions. *)
Theorem tnum_zext_copy : forall sw rw, (sw <= rw)%positive ->
  tnum_bit_copy sw rw (fun x => wrap rw x).
Proof.
  intros sw rw Hwidth i Hi. destruct (Z_lt_ge_dec i (Zpos sw)) as [Hlow|Hhigh].
  - right. exists i. split; [lia|]. intros x Hx. now rewrite tnum_wrap_bit by exact Hi.
  - left. intros x Hx. rewrite tnum_wrap_bit by exact Hi.
    apply (word_bits_high sw x i Hx). lia.
Qed.

(** Truncation copies precisely the low result-width bits. *)
Theorem tnum_trunc_copy : forall sw rw, (rw <= sw)%positive ->
  tnum_bit_copy sw rw (fun x => wrap rw x).
Proof.
  intros sw rw Hwidth i Hi. right. exists i. split.
  - apply Pos2Z.pos_le_pos in Hwidth. lia.
  - intros x Hx. now rewrite tnum_wrap_bit by exact Hi.
Qed.

(** Extraction copies its contiguous source slice. *)
Theorem tnum_extract_copy : forall sw rw lo,
  0 <= lo -> Zpos rw + lo <= Zpos sw ->
  tnum_bit_copy sw rw (fun x => wrap rw (x / 2 ^ lo)).
Proof.
  intros sw rw lo Hlo Hwidth i Hi. right. exists (i + lo). split; [lia|].
  intros x Hx. rewrite tnum_wrap_bit by exact Hi. now rewrite Z.div_pow2_bits by lia.
Qed.

(** A scalar left-shift amount saturates at the width before constructing a power. *)
Definition tnum_shl_scalar_value (w : width) (k x : Z) : Z :=
  wshl w x (Z.min k (Zpos w)).

Definition tnum_shl_scalar (w : width) (k : Z) (a : tnum) : tnum :=
  tnum_map w w (tnum_shl_scalar_value w k) a.

(** Saturating a nonnegative left-shift amount retains the concrete scalar result. *)
Theorem tnum_shl_scalar_sound : forall w k a x,
  0 <= k -> is_word w x -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shl_scalar w k a) (tnum_shl_scalar_value w k x).
Proof.
  intros w k a x Hk Hx Ha. apply tnum_map_sound; try assumption.
  apply tnum_shl_copy. apply count_is_word. lia.
Qed.

(** Scalar amounts saturate for shifts and reduce modulo the width for rotations. *)
Definition tnum_scalar_value (o : op) (w : width) (k x : Z) : Z :=
  match o with
  | bvshl => wshl w x (Z.min k (Zpos w))
  | bvlshr => wlshr w x (Z.min k (Zpos w))
  | bvashr => washr w x (Z.min k (Zpos w))
  | bvrotl => wrotl w x (k mod Zpos w)
  | bvrotr => wrotl w x ((-k) mod Zpos w)
  | _ => wrap w x
  end.

Definition tnum_source (o : op) (w : width) (k i : Z) : option Z :=
  match o with
  | bvshl => if k <=? i then Some (i - k) else None
  | bvlshr => if i + k <? Zpos w then Some (i + k) else None
  | bvashr => Some (Z.min (i + k) (Zpos w - 1))
  | bvrotl => Some ((i - k) mod Zpos w)
  | bvrotr => Some ((i + k) mod Zpos w)
  | _ => Some i
  end.

(** Scalar transfer supports the complete shift and rotation family. *)
Definition tnum_shift_op (o : op) : Prop :=
  o = bvshl \/ o = bvlshr \/ o = bvashr \/ o = bvrotl \/ o = bvrotr.

Definition tnum_scalar (o : op) (w : width) (k : Z) (a : tnum) : tnum :=
  tnum_map w w (tnum_scalar_value o w k) a.

Lemma tnum_scalar_word : forall o w k x,
  is_word w (tnum_scalar_value o w k x).
Proof.
  intros o w k x. destruct o; cbn [tnum_scalar_value];
    first [apply wrap_is_word|apply wshl_is_word|apply wlshr_is_word|
      apply washr_is_word|exact (word_fun2_is_word bvrotl wrotl w _ _ eq_refl)].
Qed.

(** Every scalar output bit has the source selected by the guarded index function. *)
Theorem tnum_scalar_bits : forall o w k x i,
  0 <= k -> is_word w x -> 0 <= i < Zpos w ->
  Z.testbit (tnum_scalar_value o w k x) i =
    match tnum_source o w k i with
    | Some j => Z.testbit x j
    | None => false
    end.
Proof.
  intros o w k x i Hk Hx Hi.
  assert (Hsat : is_word w (Z.min k (Zpos w))) by (apply count_is_word; lia).
  assert (Hres : forall n, is_word w (n mod Zpos w)).
  { intro n. apply small_amount_word. apply Z.mod_pos_bound. lia. }
  assert (Hlow : (i <? Zpos w) = true) by (apply Z.ltb_lt; lia).
  destruct o; cbn [tnum_scalar_value tnum_source];
    try (rewrite (wrap_id w x Hx); reflexivity).
  - rewrite testbit_wshl, Hlow by (try assumption; lia). cbn [andb].
    destruct (k <=? i) eqn:Hki.
    + apply Z.leb_le in Hki. rewrite Z.min_l by lia.
      now rewrite (proj2 (Z.leb_le k i) Hki).
    + apply Z.leb_gt in Hki. rewrite (proj2 (Z.leb_gt (Z.min k (Zpos w)) i)) by lia.
      reflexivity.
  - rewrite testbit_wlshr, Hlow by (try assumption; lia). cbn [andb].
    destruct (i + k <? Zpos w) eqn:Hsmall.
    + apply Z.ltb_lt in Hsmall. now rewrite Z.min_l by lia.
    + apply Z.ltb_ge in Hsmall. apply (word_bits_high w x); [exact Hx|lia].
  - rewrite testbit_washr, Hlow by (try assumption; lia). cbn [andb]. f_equal. lia.
  - rewrite testbit_wrotl by exact Hi.
    rewrite (wrap_id w _ (Hres k)), (wrap_id w x Hx).
    rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia. reflexivity.
  - rewrite testbit_wrotl by exact Hi.
    rewrite (wrap_id w _ (Hres (-k))), (wrap_id w x Hx).
    rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
    replace (i - - k) with (i + k) by ring. reflexivity.
Qed.

Lemma tnum_source_range : forall o w k i j,
  0 <= k -> 0 <= i < Zpos w -> tnum_source o w k i = Some j ->
  0 <= j < Zpos w.
Proof.
  intros o w k i j Hk Hi Hsource.
  destruct o; cbn [tnum_source] in Hsource; try (inversion Hsource; lia).
  - destruct (k <=? i) eqn:Hki; [apply Z.leb_le in Hki|discriminate].
    inversion Hsource. lia.
  - destruct (i + k <? Zpos w) eqn:Hki; [apply Z.ltb_lt in Hki|discriminate].
    inversion Hsource. lia.
  - change (Some (Z.min (i + k) (Zpos w - 1)) = Some j) in Hsource.
    injection Hsource as <-.
    change (0 <= Z.min (i + k) (Zpos w - 1) < Zpos w). lia.
  - inversion Hsource. apply Z.mod_pos_bound. lia.
  - inversion Hsource. apply Z.mod_pos_bound. lia.
Qed.

Lemma tnum_scalar_copy : forall o w k, 0 <= k ->
  tnum_bit_copy w w (tnum_scalar_value o w k).
Proof.
  intros o w k Hk i Hi. destruct (tnum_source o w k i) as [j|] eqn:Hsource.
  - right. exists j. split; [eapply tnum_source_range; eassumption|].
    intros x Hx. now rewrite tnum_scalar_bits, Hsource by assumption.
  - left. intros x Hx. now rewrite tnum_scalar_bits, Hsource by assumption.
Qed.

(** Every nonnegative scalar shift or rotation contains the concrete mapped word. *)
Theorem tnum_scalar_sound : forall o w k a x,
  0 <= k -> is_word w x -> tnum_gamma w a x ->
  tnum_gamma w (tnum_scalar o w k a) (tnum_scalar_value o w k x).
Proof.
  intros o w k a x Hk Hx Ha. apply tnum_map_sound; try assumption.
  now apply tnum_scalar_copy.
Qed.

(** Right rotation reads cyclic source indices after normalization of the count. *)
Theorem tnum_rotr_bits : forall w x k i,
  is_word w x -> is_word w k -> 0 <= i < Zpos w ->
  Z.testbit (wrotr w x k) i = Z.testbit x ((i + k) mod Zpos w).
Proof.
  intros w x k i Hx Hk Hi. rewrite wrotr_value, (wrap_id w k Hk).
  rewrite testbit_wrotl by exact Hi.
  assert (Hamount : is_word w (Zpos w - k mod Zpos w)).
  { pose proof (Z.mod_pos_bound k (Zpos w) ltac:(lia)). apply count_is_word. lia. }
  rewrite (wrap_id w _ Hamount), (wrap_id w x Hx). f_equal.
  replace (i - (Zpos w - k mod Zpos w)) with (i + k mod Zpos w + (-1) * Zpos w)
    by ring.
  rewrite Z.mod_add, Zplus_mod, Z.mod_mod, <- Zplus_mod by lia. reflexivity.
Qed.

(** Saturated scalar transfer agrees with the public word operation on word counts. *)
Theorem tnum_scalar_agrees : forall o w f k x,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w k -> is_word w x ->
  tnum_scalar_value o w k x = f w x k.
Proof.
  intros o w f k x Ho Hf Hk Hx. assert (Hk0 : 0 <= k) by exact (proj1 Hk).
  apply (word_ext w); [apply tnum_scalar_word|now apply (word_fun2_is_word o f)|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite tnum_scalar_bits by (try assumption; lia).
    destruct Ho as [Ho|[Ho|[Ho|[Ho|Ho]]]]; subst o; injection Hf as <-;
      cbn [tnum_source].
    + rewrite testbit_wshl by (try assumption; lia).
      rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia. destruct (k <=? i); reflexivity.
    + rewrite testbit_wlshr by (try assumption; lia).
      rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia. cbn [andb].
      destruct (i + k <? Zpos w) eqn:Hsmall; [reflexivity|].
      symmetry. apply (word_bits_high w x); [exact Hx|now apply Z.ltb_ge in Hsmall].
    + rewrite testbit_washr by (try assumption; lia).
      rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia. reflexivity.
    + rewrite testbit_wrotl, (wrap_id w k Hk), (wrap_id w x Hx) by lia. reflexivity.
    + rewrite tnum_rotr_bits by (try assumption; lia). reflexivity.
  - rewrite (word_bits_high w _ i (tnum_scalar_word o w k x) ltac:(lia)).
    rewrite (word_bits_high w _ i (word_fun2_is_word o f w x k Hf) ltac:(lia)). reflexivity.
Qed.

(** Sign extension copies low bits and repeats the original sign bit above the source width. *)
Theorem tnum_sext_copy : forall sw rw,
  tnum_bit_copy sw rw (fun x => wrap rw (signed sw x)).
Proof.
  intros sw rw i Hi. right. exists (Z.min i (Zpos sw - 1)). split; [lia|].
  intros x Hx. rewrite tnum_wrap_bit by exact Hi. rewrite signed_bits by (try exact Hx; lia).
  destruct (i <? Zpos sw) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. rewrite Z.min_l by lia. reflexivity.
  - apply Z.ltb_ge in Hlow. rewrite Z.min_r by lia. apply msb_testbit.
Qed.

Definition tnum_concat (w v : width) (a b : tnum) : tnum :=
  Tnum (wrap (w + v)%positive (wrap w (zeros a) * modulus v + wrap v (zeros b)))
    (wrap (w + v)%positive (wrap w (ones a) * modulus v + wrap v (ones b))).

(** Concatenation places each operand's known bits in the corresponding result slice. *)
Theorem tnum_concat_sound : forall w v a b x y,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  tnum_gamma (w + v)%positive (tnum_concat w v a b) (x * modulus v + y).
Proof.
  intros w v a b x y Hx Hy Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_concat zeros ones] in Hbit;
    rewrite tnum_wrap_bit in Hbit by exact Hi;
    rewrite !modulus_value in Hbit |- *;
    rewrite split_sum_bits in Hbit by
      (try (rewrite <- modulus_value; apply wrap_is_word); lia);
    rewrite split_sum_bits by (try (rewrite <- modulus_value; exact Hy); lia);
    destruct (i <? Zpos v) eqn:Hpart.
  - apply Z.ltb_lt in Hpart. rewrite tnum_wrap_bit in Hbit by lia. now apply Hbz.
  - apply Z.ltb_ge in Hpart. rewrite tnum_wrap_bit in Hbit by
      (rewrite Pos2Z.inj_add in Hi; lia). apply Haz; [rewrite Pos2Z.inj_add in Hi; lia|exact Hbit].
  - apply Z.ltb_lt in Hpart. rewrite tnum_wrap_bit in Hbit by lia. now apply Hbo.
  - apply Z.ltb_ge in Hpart. rewrite tnum_wrap_bit in Hbit by
      (rewrite Pos2Z.inj_add in Hi; lia). apply Hao; [rewrite Pos2Z.inj_add in Hi; lia|exact Hbit].
Qed.
