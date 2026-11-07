(** * Sign sets for words

    Three flags describe the possible signed classes of a word.
    For example, intersecting nonnegative and nonpositive sets leaves only zero.
    Builds on: LatticeCore, DomainsTransfer and Bits arithmetic. *)

From Stdlib Require Import Bool ZArith Lia List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsNumeric DomainsTransfer DomainsTagged.
Import List.ListNotations Cost.Notations.
Local Open Scope Z_scope.

(** Each flag permits one signed class. *)
Record sign : Type := Sign {
  neg : bool;
  zero : bool;
  pos : bool
}.

Definition sign_le (a b : sign) : bool :=
  (negb (neg a) || neg b) && (negb (zero a) || zero b) &&
    (negb (pos a) || pos b).

Definition sign_join (a b : sign) : sign :=
  Sign (neg a || neg b) (zero a || zero b) (pos a || pos b).

Definition sign_lattice : lattice sign :=
  simple sign_le (Sign false false false) sign_join.

(** The three flags form a lattice under inclusion and union. *)
Theorem sign_lattice_laws : lattice_laws sign_lattice.
Proof.
  apply simple_laws.
  - intros [a b c]. destruct a, b, c; reflexivity.
  - intros [a b c] [d e f] [g h i]. destruct a, b, c, d, e, f, g, h, i;
      cbn; intros; try discriminate; reflexivity.
  - intros [a b c]. reflexivity.
  - intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  - intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
Qed.

(** The number of permitted classes is a height bounded by three. *)
Theorem sign_height_on : height_on sign_lattice (fun _ => True).
Proof.
  refine {| rank := fun s => ((if neg s then 1 else 0) +
                                (if zero s then 1 else 0) +
                                (if pos s then 1 else 0))%nat;
            bound := 3%nat |}.
  - intros [a b c] _. destruct a, b, c; cbn; lia.
  - intros [a b c] [d e f] _ _. destruct a, b, c, d, e, f;
      cbn; intro Hle; try discriminate; lia.
  - intros [a b c] [d e f] _ _. destruct a, b, c, d, e, f;
      cbn; intro Hstrict; try discriminate; lia.
Defined.

(** A sign set permits each class inhabited by its signed word. *)
Definition sign_gamma (w : width) (s : sign) (z : Z) : Prop :=
  ((signed w z < 0)%Z -> neg s = true) /\
  ((signed w z = 0)%Z -> zero s = true) /\
  ((0 < signed w z)%Z -> pos s = true).

Definition sign_meet (a b : sign) : sign :=
  Sign (neg a && neg b) (zero a && zero b) (pos a && pos b).

(** Intersection retains any word admitted by both sign sets. *)
Theorem sign_meet_sound : forall w a b z,
  sign_gamma w a z -> sign_gamma w b z -> sign_gamma w (sign_meet a b) z.
Proof.
  intros w a b z [Hneg [Hzero Hpos]] [Hneg' [Hzero' Hpos']].
  split; [|split]; cbn [sign_meet neg zero pos]; intro Hsign;
    apply andb_true_iff; auto.
Qed.

Definition sign_top := Sign true true true.

Definition sign_const w z := Sign (signed w z <? 0) (signed w z =? 0) (0 <? signed w z).

Definition sign_nonneg s := zero s || pos s.

Definition sign_bits n nn := Sign n nn nn.

Definition sign_not a := sign_bits (sign_nonneg a) (neg a).

Definition sign_neg a := Sign (neg a || pos a) (zero a) (neg a).

Definition sign_and a b := sign_bits (neg a && neg b) (sign_nonneg a || sign_nonneg b).

Definition sign_or a b := sign_bits (neg a || neg b) (sign_nonneg a && sign_nonneg b).

Definition sign_xor a b :=
  sign_bits ((neg a && sign_nonneg b) || (sign_nonneg a && neg b))
    ((neg a && neg b) || (sign_nonneg a && sign_nonneg b)).

(** Bounds describe every signed or unsigned value admitted by a flag set. *)
Definition sign_lo w a := if neg a then - half w else if zero a then 0 else 1.

Definition sign_hi w a := if pos a then half w - 1 else if zero a then 0 else -1.

Definition sign_ulo w a := if zero a then 0 else if pos a then 1 else half w.

Definition sign_uhi w a := if neg a then modulus w - 1 else if pos a then half w - 1 else 0.

Local Lemma sign_bounds w a z : sign_gamma w a z ->
  sign_lo w a <= signed w z <= sign_hi w a.
Proof.
  destruct a as [n q p]. intros [Hn [Hq Hp]].
  pose proof (signed_range w z). pose proof (half_pos w).
  destruct n, q, p; unfold sign_lo, sign_hi; cbn in *; lia.
Qed.

Local Lemma sign_unsigned_bounds w a z : sign_gamma w a z ->
  sign_ulo w a <= wrap w z <= sign_uhi w a.
Proof.
  destruct a as [n q p]. intros Hgamma.
  pose proof (sign_bounds w (Sign n q p) z Hgamma) as Hbounds.
  destruct Hgamma as [Hn [Hq Hp]]. pose proof (wrap_is_word w z) as [Hlo Hhi].
  pose proof (half_pos w). pose proof (modulus_half w).
  rewrite signed_value in Hn, Hq, Hp, Hbounds.
  destruct (wrap w z <? half w) eqn:Hhalf;
    [apply Z.ltb_lt in Hhalf|apply Z.ltb_ge in Hhalf];
    destruct n, q, p; unfold sign_ulo, sign_uhi; cbn in *; lia.
Qed.

Definition sign_boolean (b : bool) :=
  if b then Sign true false false else Sign false true false.

Definition sign_bool_top := Sign true true false.

Definition sign_bool_not s := Sign (zero s) (neg s) false.

Definition sign_cmp_lt lo hi lo' hi' :=
  if hi <? lo' then sign_boolean true else
  if hi' <=? lo then sign_boolean false else sign_bool_top.

Definition sign_cmp_le lo hi lo' hi' :=
  if hi <=? lo' then sign_boolean true else
  if hi' <? lo then sign_boolean false else sign_bool_top.

Definition sign_cmp_eq lo hi lo' hi' :=
  if (hi <? lo') || (hi' <? lo) then sign_boolean false else
  if (lo =? hi) && (lo' =? hi') && (lo =? lo') then sign_boolean true else sign_bool_top.

(** Comparisons share bounds and encode their result as a signed one-bit boolean. *)
Definition sign_cmp o w a b :=
  match o with
  | bveq => sign_cmp_eq (sign_lo w a) (sign_hi w a) (sign_lo w b) (sign_hi w b)
  | bvne => sign_bool_not
    (sign_cmp_eq (sign_lo w a) (sign_hi w a) (sign_lo w b) (sign_hi w b))
  | bvult => sign_cmp_lt (sign_ulo w a) (sign_uhi w a) (sign_ulo w b) (sign_uhi w b)
  | bvule => sign_cmp_le (sign_ulo w a) (sign_uhi w a) (sign_ulo w b) (sign_uhi w b)
  | bvslt => sign_cmp_lt (sign_lo w a) (sign_hi w a) (sign_lo w b) (sign_hi w b)
  | bvsle => sign_cmp_le (sign_lo w a) (sign_hi w a) (sign_lo w b) (sign_hi w b)
  | _ => sign_bool_top
  end.

Local Lemma sign_gamma_boolean s (b : bool) :
  sign_gamma 1%positive s (if b then 1 else 0) <->
  (if b then neg s = true else zero s = true).
Proof.
  destruct b; unfold sign_gamma; cbn; split; intros H; try solve [intuition lia].
  exact (proj1 H ltac:(lia)).
Qed.

Local Lemma sign_boolean_sound b :
  sign_gamma 1%positive (sign_boolean b) (if b then 1 else 0).
Proof.
  apply sign_gamma_boolean. destruct b; reflexivity.
Qed.

Local Lemma sign_bool_top_sound (b : bool) :
  sign_gamma 1%positive sign_bool_top (if b then 1 else 0).
Proof.
  apply sign_gamma_boolean. destruct b; reflexivity.
Qed.

Local Lemma sign_bool_not_sound s (b : bool) :
  sign_gamma 1%positive s (if b then 1 else 0) ->
  sign_gamma 1%positive (sign_bool_not s) (if negb b then 1 else 0).
Proof.
  rewrite !sign_gamma_boolean. destruct b; exact (fun H => H).
Qed.

Local Lemma sign_cmp_lt_sound lo hi lo' hi' x y :
  lo <= x <= hi -> lo' <= y <= hi' ->
  sign_gamma 1%positive (sign_cmp_lt lo hi lo' hi') (if x <? y then 1 else 0).
Proof.
  intros Hx Hy. unfold sign_cmp_lt.
  destruct (hi <? lo') eqn:Htrue.
  - apply Z.ltb_lt in Htrue.
    rewrite (proj2 (Z.ltb_lt x y) ltac:(lia)). apply (sign_boolean_sound true).
  - destruct (hi' <=? lo) eqn:Hfalse; [|apply sign_bool_top_sound].
    apply Z.leb_le in Hfalse.
    rewrite (proj2 (Z.ltb_ge x y) ltac:(lia)). apply (sign_boolean_sound false).
Qed.

Local Lemma sign_cmp_le_sound lo hi lo' hi' x y :
  lo <= x <= hi -> lo' <= y <= hi' ->
  sign_gamma 1%positive (sign_cmp_le lo hi lo' hi') (if x <=? y then 1 else 0).
Proof.
  intros Hx Hy. unfold sign_cmp_le.
  destruct (hi <=? lo') eqn:Htrue.
  - apply Z.leb_le in Htrue.
    rewrite (proj2 (Z.leb_le x y) ltac:(lia)). apply (sign_boolean_sound true).
  - destruct (hi' <? lo) eqn:Hfalse; [|apply sign_bool_top_sound].
    apply Z.ltb_lt in Hfalse.
    rewrite (proj2 (Z.leb_gt x y) ltac:(lia)). apply (sign_boolean_sound false).
Qed.

Local Lemma sign_cmp_eq_sound lo hi lo' hi' x y :
  lo <= x <= hi -> lo' <= y <= hi' ->
  sign_gamma 1%positive (sign_cmp_eq lo hi lo' hi') (if x =? y then 1 else 0).
Proof.
  intros Hx Hy. unfold sign_cmp_eq.
  destruct ((hi <? lo') || (hi' <? lo)) eqn:Hfalse.
  - apply orb_true_iff in Hfalse as [Hfalse|Hfalse]; apply Z.ltb_lt in Hfalse;
      rewrite (proj2 (Z.eqb_neq x y) ltac:(lia)); apply (sign_boolean_sound false).
  - destruct ((lo =? hi) && (lo' =? hi') && (lo =? lo')) eqn:Htrue;
      [|apply sign_bool_top_sound].
    apply andb_true_iff in Htrue as [Hbounds Heq].
    apply andb_true_iff in Hbounds as [Hlo Hlo'].
    apply Z.eqb_eq in Hlo, Hlo', Heq.
    rewrite (proj2 (Z.eqb_eq x y) ltac:(lia)). apply (sign_boolean_sound true).
Qed.

Local Lemma sign_signed_eq w x y :
  (wrap w x =? wrap w y) = (signed w x =? signed w y).
Proof.
  apply Bool.eq_true_iff_eq. rewrite !Z.eqb_eq. split.
  - intro H. rewrite <- (signed_wrap w x), <- (signed_wrap w y). now rewrite H.
  - apply signed_inj.
Qed.

(** Every comparison decision retains the exact evaluator's boolean result. *)
Theorem sign_cmp_sound o w a b x y rw z :
  (o = bveq \/ o = bvne \/ o = bvult \/ o = bvule \/ o = bvslt \/ o = bvsle) ->
  sign_gamma w a x -> sign_gamma w b y ->
  eval_op o [(w, x); (w, y)] = Some (rw, z) -> sign_gamma rw (sign_cmp o w a b) z.
Proof.
  intros Ho Ha Hb Heval.
  pose proof (sign_bounds w a x Ha) as Hx. pose proof (sign_bounds w b y Hb) as Hy.
  pose proof (sign_unsigned_bounds w a x Ha) as Hux.
  pose proof (sign_unsigned_bounds w b y Hb) as Huy.
  destruct Ho as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  - pose proof (eq_trans (eq_sym (eval_op_cmp bveq w x y _ eq_refl)) Heval) as Hr.
    cbn beta in Hr. inversion Hr; subst rw z. unfold sign_cmp.
    rewrite sign_signed_eq. now apply sign_cmp_eq_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvne w x y _ eq_refl)) Heval) as Hr.
    cbn beta in Hr. inversion Hr; subst rw z. unfold sign_cmp.
    apply sign_bool_not_sound. rewrite sign_signed_eq. now apply sign_cmp_eq_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvult w x y _ eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. unfold sign_cmp. rewrite wult_value. now apply sign_cmp_lt_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvule w x y _ eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. unfold sign_cmp. rewrite wule_value. now apply sign_cmp_le_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvslt w x y _ eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. unfold sign_cmp. rewrite wslt_value. now apply sign_cmp_lt_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvsle w x y _ eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. unfold sign_cmp. rewrite wsle_value. now apply sign_cmp_le_sound.
Qed.

Local Lemma sign_msb_bit w x :
  msb w x = Z.testbit (wrap w x) (Zpos w - 1).
Proof.
  pose proof (Z.testbit_spec' (wrap w x) (Zpos w - 1) ltac:(lia)) as Hbit.
  fold (half w) in Hbit. rewrite msb_half.
  pose proof (wrap_is_word w x) as [Hlo Hhi].
  pose proof (half_pos w). pose proof (modulus_half w).
  destruct (wrap w x <? half w) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. rewrite Z.div_small in Hbit by lia.
    destruct (Z.testbit (wrap w x) (Zpos w - 1)); cbn in *; congruence.
  - apply Z.ltb_ge in Hlt.
    assert (Hdiv : wrap w x / half w = 1).
    { symmetry. apply Z.div_unique with (r := wrap w x - half w); [left; lia|ring]. }
    rewrite Hdiv in Hbit.
    destruct (Z.testbit (wrap w x) (Zpos w - 1)); cbn in *; congruence.
Qed.

Local Lemma sign_class w a x : sign_gamma w a x ->
  (if msb w x then neg a else sign_nonneg a) = true.
Proof.
  intros [Hn [Hz Hp]]. destruct (msb w x) eqn:Hmsb.
  - apply Hn. now apply signed_neg_iff_msb.
  - pose proof (signed_nonnegative w x Hmsb) as Hsigned.
    pose proof (wrap_is_word w x) as [Hlo Hhi].
    destruct (Z.eq_dec (signed w x) 0) as [Heq|Hneq].
    + unfold sign_nonneg. rewrite (Hz Heq). reflexivity.
    + unfold sign_nonneg. rewrite (Hp ltac:(lia)). apply orb_true_r.
Qed.

Local Lemma sign_from_msb w a x :
  (msb w x = true -> neg a = true) ->
  (msb w x = false -> zero a = true /\ pos a = true) -> sign_gamma w a x.
Proof.
  intros Hn Hnn. split; [|split]; intro Hsign.
  - apply Hn. now apply signed_neg_iff_msb.
  - assert (Hclear : msb w x = false).
    { destruct (msb w x) eqn:Hmsb; [|reflexivity].
      apply signed_neg_iff_msb in Hmsb. lia. }
    exact (proj1 (Hnn Hclear)).
  - assert (Hclear : msb w x = false).
    { destruct (msb w x) eqn:Hmsb; [|reflexivity].
      apply signed_neg_iff_msb in Hmsb. lia. }
    exact (proj2 (Hnn Hclear)).
Qed.

Local Lemma sign_bitwise_msb w x y :
  is_word w x -> is_word w y ->
  msb w (wand w x y) = (msb w x && msb w y) /\
  msb w (wor w x y) = (msb w x || msb w y) /\
  msb w (wxor w x y) = xorb (msb w x) (msb w y).
Proof.
  intros Hx Hy. rewrite !sign_msb_bit.
  rewrite !wrap_id by auto using wand_is_word, wor_is_word, wxor_is_word.
  rewrite testbit_wand, testbit_wor, testbit_wxor by (try assumption; lia).
  auto.
Qed.

(** Conjunction retains every possible sign bit of its concrete result. *)
Theorem sign_and_sound w a b x y :
  is_word w x -> is_word w y -> sign_gamma w a x -> sign_gamma w b y ->
  sign_gamma w (sign_and a b) (wand w x y).
Proof.
  intros Hx Hy Ha Hb.
  pose proof (sign_class w a x Ha) as Hfa. pose proof (sign_class w b y Hb) as Hfb.
  apply sign_from_msb; cbn [sign_and sign_bits neg zero pos];
    rewrite (proj1 (sign_bitwise_msb w x y Hx Hy));
    destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
    intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r; cbn; auto.
Qed.

(** Disjunction retains every possible sign bit of its concrete result. *)
Theorem sign_or_sound w a b x y :
  is_word w x -> is_word w y -> sign_gamma w a x -> sign_gamma w b y ->
  sign_gamma w (sign_or a b) (wor w x y).
Proof.
  intros Hx Hy Ha Hb.
  pose proof (sign_class w a x Ha) as Hfa. pose proof (sign_class w b y Hb) as Hfb.
  apply sign_from_msb; cbn [sign_or sign_bits neg zero pos];
    rewrite (proj1 (proj2 (sign_bitwise_msb w x y Hx Hy)));
    destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
    intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r; cbn; auto.
Qed.

(** Exclusive disjunction retains every possible sign bit of its concrete result. *)
Theorem sign_xor_sound w a b x y :
  is_word w x -> is_word w y -> sign_gamma w a x -> sign_gamma w b y ->
  sign_gamma w (sign_xor a b) (wxor w x y).
Proof.
  intros Hx Hy Ha Hb.
  pose proof (sign_class w a x Ha) as Hfa. pose proof (sign_class w b y Hb) as Hfb.
  apply sign_from_msb; cbn [sign_xor sign_bits neg zero pos];
    rewrite (proj2 (proj2 (sign_bitwise_msb w x y Hx Hy)));
    destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
    intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r; cbn; auto.
Qed.

(** Complement swaps the sign bit and permits both nonnegative classes. *)
Theorem sign_not_sound w a x : is_word w x -> sign_gamma w a x ->
  sign_gamma w (sign_not a) (wnot w x).
Proof.
  intros Hx Ha. pose proof (sign_class w a x Ha) as Hfa.
  assert (Hnot : msb w (wnot w x) = negb (msb w x)).
  { rewrite !sign_msb_bit, !wrap_id by auto using wnot_is_word.
    rewrite testbit_wnot by (try assumption; lia).
    rewrite (proj2 (Z.ltb_lt (Zpos w - 1) (Zpos w)) ltac:(lia)). reflexivity. }
  apply sign_from_msb; cbn [sign_not sign_bits neg zero pos]; rewrite Hnot;
    destruct (msb w x); cbn in Hfa |- *; intro Hresult; try discriminate; auto.
Qed.

(** Modular negation keeps the minimum signed word negative. *)
Theorem sign_neg_sound w a x : is_word w x -> sign_gamma w a x ->
  sign_gamma w (sign_neg a) (wneg w x).
Proof.
  intros Hx [Hn [Hz Hp]]. pose proof (half_pos w). pose proof (modulus_half w).
  assert (Hwrap : wrap w (- x) = if x =? 0 then 0 else modulus w - x).
  { destruct (x =? 0) eqn:Hxzero.
    - apply Z.eqb_eq in Hxzero. subst x. apply wrap_0.
    - apply Z.eqb_neq in Hxzero.
      replace (- x) with ((modulus w - x) + (-1) * modulus w) by ring.
      rewrite wrap_add_modulus. apply wrap_id. split; destruct Hx; lia. }
  unfold sign_gamma, sign_neg. cbn [neg zero pos].
  rewrite wneg_value, signed_value, wrap_wrap, Hwrap.
  rewrite signed_value, (wrap_id w x Hx) in Hn, Hz, Hp.
  destruct (x =? 0) eqn:Hxzero.
  - apply Z.eqb_eq in Hxzero. subst x.
    rewrite (proj2 (Z.ltb_lt 0 (half w)) ltac:(lia)) in *.
    split; [lia|]. split; [intros _; now apply Hz|lia].
  - apply Z.eqb_neq in Hxzero.
    destruct (x <? half w) eqn:Hxhalf, (modulus w - x <? half w) eqn:Hnhalf;
      try apply Z.ltb_lt in Hxhalf; try apply Z.ltb_ge in Hxhalf;
      try apply Z.ltb_lt in Hnhalf; try apply Z.ltb_ge in Hnhalf;
      destruct Hx; (split; [|split]); intro Hsign; try lia.
    + rewrite (Hp ltac:(lia)). apply orb_true_r.
    + rewrite (Hn ltac:(lia)). reflexivity.
    + rewrite (Hn ltac:(lia)). reflexivity.
Qed.

(** Unary entry adapters retain the callback's cost and invocation overhead. *)
Definition sign_unary (f : sign -> Cost.t sign) (_ : width) (xs : list (width * sign)) :=
  match xs with
  | [(_, a)] => Cost.step ;; f a
  | _ => Cost.ret sign_top
  end.

(** Binary entry adapters retain widths and the callback's cost. *)
Definition sign_binary (f : width -> sign -> sign -> Cost.t sign)
    (_ : width) (xs : list (width * sign)) :=
  match xs with
  | [(w, a); (_, b)] => Cost.step ;; f w a b
  | _ => Cost.ret sign_top
  end.

(** Selection joins its branch flags independently of the condition's signed class. *)
Definition sign_select (_ : width) (xs : list (width * sign)) :=
  Cost.step ;; Cost.ret
    (match xs with [_; (_, a); (_, b)] => sign_join a b | _ => sign_top end).

(** Sign entries model bitwise operations, negation, extensions, comparisons and selection. *)
Definition sign_table : Transfer.table (width * sign) sign op width :=
  {| Transfer.fwd := fun o n => Cost.ret
       (match o, n with
        | bvnot, 1%nat => Some (sign_unary (Cost.lift (fun _ => 1%N) sign_not))
        | bvneg, 1%nat => Some (sign_unary (Cost.lift (fun _ => 1%N) sign_neg))
        | bvzext _, 1%nat => Some (sign_unary (fun _ => Cost.ret (Sign false true true)))
        | bvsext _, 1%nat => Some (sign_unary Cost.ret)
        | bvand, 2%nat => Some (sign_binary
          (fun _ a b => Cost.step ;; Cost.ret (sign_and a b)))
        | bvor, 2%nat => Some (sign_binary
          (fun _ a b => Cost.step ;; Cost.ret (sign_or a b)))
        | bvxor, 2%nat => Some (sign_binary
          (fun _ a b => Cost.step ;; Cost.ret (sign_xor a b)))
        | (bveq | bvne | bvult | bvule | bvslt | bvsle), 2%nat =>
          Some (sign_binary (fun w a b => Cost.step ;; Cost.ret (sign_cmp o w a b)))
        | bvite, 3%nat => Some sign_select
        | _, _ => None
        end);
     Transfer.bwd := fun _ _ => Cost.ret None |}.

(** Bounded lookahead rejects long lists before invoking the scalar word evaluator. *)
Definition sign_eval_c o (xs : list word) :=
  match xs with
  | _ :: _ :: _ :: _ :: _ => Cost.ret None
  | _ => Cost.step ;; Cost.ret (eval_op o xs)
  end.

Local Lemma sign_eval_equation o xs : Cost.value (sign_eval_c o xs) = eval_op o xs.
Proof.
  destruct xs as [|a [|b [|c [|d rest]]]]; try reflexivity.
  destruct (eval_op o (a :: b :: c :: d :: rest)) as [r|] eqn:He; [|reflexivity].
  pose proof (eval_op_arity o _ r He) as Hlen.
  destruct o; cbn in Hlen; discriminate.
Qed.

(** Only the zero-only flag set is recognized as a point, preserving other legacy precision. *)
Definition sign_shape : Transfer.shape (width * sign) sign op width word :=
  {| Transfer.eval_c := sign_eval_c;
     Transfer.point_c := fun wp => Cost.step ;; Cost.ret
       (match snd wp with
        | Sign false true false => Some (fst wp, 0)
        | _ => None
        end);
     Transfer.is_empty_c := fun wp => Cost.step ;; Cost.ret
       (negb (neg (snd wp) || zero (snd wp) || pos (snd wp)));
     Transfer.inj_c := fun _ c => Cost.step ;; Cost.ret (sign_const (fst c) (snd c));
     Transfer.bot_out := fun _ => Sign false false false;
     Transfer.top_out := fun _ => sign_top;
     Transfer.keep_c := fun wp => Cost.ret (snd wp) |}.

(** The sign domain obtains empty, point and backward behavior from the harness. *)
Definition sign_word_domain : word_domain sign :=
  word_of_table sign_table sign_shape (fun _ => sign_lattice) (fun _ => sign_top)
    (fun w z => Cost.step ;; Cost.ret (sign_const w z))
    (fun _ a b => Cost.step ;; Cost.ret (sign_meet a b)).

Local Lemma sign_top_sound w z : sign_gamma w sign_top z.
Proof.
  split; [|split]; intro H; reflexivity.
Qed.

Local Lemma sign_const_sound w z : sign_gamma w (sign_const w z) z.
Proof.
  unfold sign_gamma, sign_const. cbn [neg zero pos].
  split; [|split]; intro Hsign; [now apply Z.ltb_lt|now apply Z.eqb_eq|now apply Z.ltb_lt].
Qed.

Local Lemma sign_bot_empty w z : ~ sign_gamma w (Sign false false false) z.
Proof.
  intros [Hn [Hz Hp]].
  destruct (Z.lt_trichotomy (signed w z) 0) as [Hneg|[Hzero|Hpos]].
  - discriminate (Hn Hneg).
  - discriminate (Hz Hzero).
  - discriminate (Hp Hpos).
Qed.

Local Lemma sign_mono w a b z :
  leb sign_lattice a b = true -> sign_gamma w a z -> sign_gamma w b z.
Proof.
  destruct a as [an az ap], b as [bn bz bp].
  destruct an, az, ap, bn, bz, bp; cbn; intros Hle Hg; try discriminate;
    unfold sign_gamma in *; cbn in *; intuition.
Qed.

Local Lemma sign_shape_laws :
  transfer_sem sign_shape (payload_sound sign_gamma) (word_output sign_gamma) word_context.
Proof.
  constructor.
  - intros [w [n q p]] [v x] [u y] Hpoint [Hwidth [Hword Hgamma]].
    destruct n, q, p; cbn in Hpoint; try discriminate.
    inversion Hpoint; subst v x. cbn in Hwidth. subst u.
    assert (Hsigned : signed w y = 0).
    { destruct Hgamma as [Hn [Hz Hp]]. cbn in Hn, Hp.
      destruct (Z.lt_trichotomy (signed w y) 0) as [Hneg|[Hzero|Hpos]];
        [discriminate (Hn Hneg)|exact Hzero|discriminate (Hp Hpos)]. }
    assert (Hz : wrap w y = wrap w 0).
    { apply signed_inj. now rewrite signed_zero. }
    rewrite wrap_0, wrap_id in Hz by exact Hword. subst y. reflexivity.
  - intros [w [n q p]] [v x] Hempty [_ [_ Hg]].
    destruct n, q, p; cbn in Hempty; try discriminate. exact (sign_bot_empty w x Hg).
  - intros r [w z] Hctx. apply sign_const_sound.
  - intros r [w z]. apply sign_bot_empty.
  - intros r [w z] Hctx. apply sign_top_sound.
  - intros r [w a] [v z] [Hw [_ Hg]]. cbn in Hw. subst v. exact Hg.
Qed.

Local Lemma sign_unary_sound o f rw xs cs c :
  (forall w a x target z, is_word w x -> sign_gamma w a x ->
    eval_op o [(w, x)] = Some (target, z) -> sign_gamma target (Cost.value (f a)) z) ->
  length xs = 1%nat -> Forall2 (payload_sound sign_gamma) xs cs ->
  eval_op o cs = Some c ->
  word_output sign_gamma rw (Cost.value (sign_unary f rw xs)) c.
Proof.
  intros Hf Hlen Hxs Heval.
  destruct xs as [|[w a] [|wp rest]]; cbn in Hlen; try discriminate.
  inversion Hxs as [|? [v x] ? ? Hhead Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hw [Hx Ha]]. cbn in Hw, Ha. subst v. destruct c as [target z].
  change (sign_gamma target (Cost.value (f a)) z). now apply (Hf w a x).
Qed.

Local Lemma sign_binary_sound o f rw xs cs c :
  (forall w v a b x y target z,
    is_word w x -> is_word v y -> sign_gamma w a x -> sign_gamma v b y ->
    eval_op o [(w, x); (v, y)] = Some (target, z) ->
    sign_gamma target (Cost.value (f w a b)) z) ->
  length xs = 2%nat -> Forall2 (payload_sound sign_gamma) xs cs ->
  eval_op o cs = Some c ->
  word_output sign_gamma rw (Cost.value (sign_binary f rw xs)) c.
Proof.
  intros Hf Hlen Hxs Heval.
  destruct xs as [|[w a] [|[v b] [|wp rest]]]; cbn in Hlen; try discriminate.
  inversion Hxs as [|? [wx x] ? ? Hhead Htail]; subst.
  inversion Htail as [|? [vy y] ? ? Hhead' Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
  cbn in Hwx, Hvy, Ha, Hb. subst wx vy. destruct c as [target z].
  change (sign_gamma target (Cost.value (f w a b)) z). now apply (Hf w v a b x y).
Qed.

Local Lemma sign_select_sound rw xs cs c :
  length xs = 3%nat -> Forall2 (payload_sound sign_gamma) xs cs ->
  eval_op bvite cs = Some c ->
  word_output sign_gamma rw (Cost.value (sign_select rw xs)) c.
Proof.
  intros Hlen Hxs Heval.
  destruct xs as [|[w a] [|[v b] [|[u d] [|wp rest]]]];
    cbn in Hlen; try discriminate.
  inversion Hxs as [|? [wx x] ? ? Hhead Htail]; subst.
  inversion Htail as [|? [vy y] ? ? Hhead' Htail']; subst.
  inversion Htail' as [|? [uz z] ? ? Hhead'' Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]],
    Hhead'' as [Huz [Hz Hd]].
  cbn in Hwx, Hvy, Huz, Ha, Hb, Hd. subst wx vy uz.
  destruct (eval_op_ite_width w v u x y z c Heval) as [Hw Hvu]. subst w u.
  rewrite eval_op_ite in Heval. destruct c as [target result].
  destruct (wrap 1%positive x =? 1); inversion Heval; subst target result.
  - rewrite (wrap_id v y Hy). apply (sign_mono v b (sign_join b d) y); [|exact Hb].
    exact (join_upper_l sign_lattice_laws b d).
  - rewrite (wrap_id v z Hz). apply (sign_mono v d (sign_join b d) z); [|exact Hd].
    exact (join_upper_r sign_lattice_laws b d).
Qed.

Local Lemma sign_zext_sound extra w a x target z :
  is_word w x -> sign_gamma w a x ->
  eval_op (bvzext extra) [(w, x)] = Some (target, z) ->
  sign_gamma target (Sign false true true) z.
Proof.
  intros Hx Ha Heval. rewrite eval_zext_value in Heval. inversion Heval; subst target z.
  unfold sign_gamma. rewrite (wrap_id w x Hx).
  assert (Hs : signed (w + extra)%positive x = x).
  { apply signed_id. pose proof (half_pos (w + extra)%positive).
    assert (Hm : modulus w <= half (w + extra)%positive).
    { change (2 ^ Zpos w <= 2 ^ (Zpos (w + extra) - 1)).
      rewrite Pos2Z.inj_add. apply Z.pow_le_mono_r; lia. }
    destruct Hx. lia. }
  rewrite Hs. cbn. destruct Hx.
  split; [lia|]. split; intros _; reflexivity.
Qed.

Local Lemma sign_sext_sound extra w a x target z :
  is_word w x -> sign_gamma w a x ->
  eval_op (bvsext extra) [(w, x)] = Some (target, z) -> sign_gamma target a z.
Proof.
  intros Hx Ha Heval. rewrite eval_sext_value in Heval. inversion Heval; subst target z.
  unfold sign_gamma in *. rewrite signed_wrap.
  assert (Hs : signed (w + extra)%positive (signed w x) = signed w x).
  { apply signed_id. pose proof (signed_range w x).
    assert (Hh : half w <= half (w + extra)%positive).
    { change (2 ^ (Zpos w - 1) <= 2 ^ (Zpos (w + extra) - 1)).
      rewrite Pos2Z.inj_add. apply Z.pow_le_mono_r; lia. }
    lia. }
  now rewrite Hs.
Qed.

(** Every sign table entry is sound and the absent backward entries retain operand counts. *)
Theorem sign_table_laws :
  table_laws sign_table sign_shape (payload_sound sign_gamma)
    (word_output sign_gamma) word_context.
Proof.
  constructor.
  - intros o n f rw xs cs c Hf Hlen Hxs Heval Hctx.
    change (Cost.value (sign_eval_c o cs) = Some c) in Heval.
    rewrite sign_eval_equation in Heval.
    destruct o; destruct n as [|[|[|[|n]]]]; cbn in Hf; try discriminate;
      injection Hf as <-.
    all: first
      [eapply sign_unary_sound; [|exact Hlen|exact Hxs|exact Heval]
      |eapply sign_binary_sound; [|exact Hlen|exact Hxs|exact Heval]
      |exact (sign_select_sound rw xs cs c Hlen Hxs Heval)].
    all: intros w; intros; autorewrite with galois_cost.
    all: first
      [eapply sign_zext_sound; eassumption
      |eapply sign_sext_sound; eassumption
      |match goal with
       | He : eval_op ?k [(?w, ?x)] = Some (?t, ?z) |- _ =>
         let Hr := fresh "Hr" in
         pose proof (eq_trans (eq_sym (eval_op_fun1 k w x _ eq_refl)) He) as Hr;
         inversion Hr; subst t z;
         first [now apply sign_not_sound|now apply sign_neg_sound]
       | He : eval_op ?k [(?w, ?x); (?v, ?y)] = Some (?t, ?z) |- _ =>
         assert (Hw : w = v) by
           (first [eapply (eval_op_fun2_width k _ w v x y (t, z)); eauto; reflexivity|
             eapply (eval_op_cmp_width k _ w v x y (t, z)); eauto; reflexivity]);
         subst v;
         first [eapply (sign_cmp_sound k); [tauto|eassumption|eassumption|exact He]|
           let Hr := fresh "Hr" in
           pose proof (eq_trans (eq_sym (eval_op_fun2 k w x y _ eq_refl)) He) as Hr;
           inversion Hr; subst t z;
           first [now apply sign_and_sound|now apply sign_or_sound|now apply sign_xor_sound]]
       end].
  - intros o n f rw q xs cs c Hf. discriminate Hf.
  - intros o n f rw q xs Hf. discriminate Hf.
Qed.

(** Sign backward transfer is the harness's reductive identity default. *)
Theorem sign_table_refines :
  table_refines sign_table sign_shape
    (fun wp q => leb sign_lattice q (snd wp) = true).
Proof.
  constructor.
  - intros [w a]. apply (leb_refl sign_lattice_laws).
  - intros o n f rw q xs Hf. discriminate Hf.
Qed.

(** Sign flags satisfy word evaluation, intersection and backward refinement laws. *)
Theorem sign_word_laws : word_laws sign_word_domain sign_gamma.
Proof.
  apply word_of_table_laws.
  - exact sign_eval_equation.
  - exact sign_shape_laws.
  - exact sign_table_laws.
  - intros. exact sign_lattice_laws.
  - exact sign_mono.
  - exact sign_bot_empty.
  - intros. apply sign_top_sound.
  - intros w z. unfold sign_gamma. rewrite signed_wrap.
    exact (sign_const_sound w z).
  - exact sign_table_refines.
  - intros. now apply sign_meet_sound.
  - intros w [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
Qed.

(** Width tagging supplies numeric soundness and refinement for sign flags. *)
Theorem sign_numeric_laws :
  numeric_laws (tagged_domain sign_word_domain) (tagged_gamma sign_gamma).
Proof.
  apply tagged_numeric_laws. exact sign_word_laws.
Qed.

#[export] Hint Resolve sign_and_sound sign_or_sound sign_xor_sound sign_not_sound
  sign_neg_sound sign_cmp_sound sign_meet_sound : galois_gamma.
