(** * Signed sign payload code

    Three Boolean flags represent signed word classes.
    For example, a zero-only payload represents the integer zero.
    Builds on: SignSig and the fixed-width word operations. *)

From Stdlib Require Import ZArith List Bool Lia Ring.
From Argent Require Import Time Std.
From Galois.Bits Require Import Word Fun Testbit Op Arith.
From Galois.Domains Require Import SignSig WordSig.
Import List.ListNotations.

Local Open Scope Z_scope.

Module SignCode (L : WORD_LANGUAGE_OPS) <: SIGN_OPS L.
  Definition p := sgn.
  Definition pleb (_ : positive) (a b : p) : bool :=
    (negb (neg a) || neg b) && (negb (zero a) || zero b) &&
      (negb (pos a) || pos b).
  Definition pjoin (_ : positive) (a b : p) : p :=
    Sgn (neg a || neg b) (zero a || zero b) (pos a || pos b).
  Definition pmeet (_ : positive) (a b : p) : p :=
    Sgn (neg a && neg b) (zero a && zero b) (pos a && pos b).
  Definition pbot (_ : positive) : p := Sgn false false false.
  Definition ptop (_ : positive) : p := Sgn true true true.
  Definition pis_bot (_ : positive) (a : p) : bool :=
    negb (neg a || zero a || pos a).
  Definition pconst (w : positive) (z : Z) : p :=
    Sgn (Word.signed w z <? 0) (Word.signed w z =? 0) (0 <? Word.signed w z).
  Definition ppoint (_ : positive) (a : p) : option Z :=
    match a with
    | Sgn false true false => Some 0
    | _ => None
    end.
  Definition pwparam := unit.
  Definition pwiden (_ : pwparam) w a b := pjoin w a b.
  Definition pnarrow w a b := pmeet w a b.
  Definition sign_nonneg (a : p) := zero a || pos a.
  Definition sign_bits n nn := Sgn n nn nn.
  Definition sign_not (a : p) := sign_bits (sign_nonneg a) (neg a).
  Definition sign_neg (a : p) := Sgn (neg a || pos a) (zero a) (neg a).
  Definition sign_and (a b : p) :=
    sign_bits (neg a && neg b) (sign_nonneg a || sign_nonneg b).
  Definition sign_or (a b : p) :=
    sign_bits (neg a || neg b) (sign_nonneg a && sign_nonneg b).
  Definition sign_xor (a b : p) :=
    sign_bits ((neg a && sign_nonneg b) || (sign_nonneg a && neg b))
      ((neg a && neg b) || (sign_nonneg a && sign_nonneg b)).
End SignCode.

Module SignTableCode (L : WORD_LANGUAGE_OPS) (S : SIGN_OPS L)
    <: WORD_TABLE_OPS L S.
  Definition sign_nonneg (a : sgn) := zero a || pos a.
  Definition sign_lo := sign_numeric_lo.
  Definition sign_hi := sign_numeric_hi.
  Definition sign_ulo := sign_numeric_ulo.
  Definition sign_uhi := sign_numeric_uhi.
  Definition sign_boolean := sign_numeric_boolean.
  Definition sign_bool_top := sign_numeric_bool_top.
  Definition sign_bool_not := sign_numeric_bool_not.
  Definition sign_cmp_lt := sign_numeric_cmp_lt.
  Definition sign_cmp_le := sign_numeric_cmp_le.
  Definition sign_cmp_eq := sign_numeric_cmp_eq.
  Definition sign_cmp := sign_numeric_cmp.
  Definition sign_half_class (w : positive) : Z :=
    match w with
    | xH => 1
    | xO xH => 2
    | _ => 4
    end.
  Definition sign_lo_sym w a :=
    if neg a then - sign_half_class w else if zero a then 0 else 1.
  Definition sign_hi_sym w a :=
    if pos a then sign_half_class w - 1 else if zero a then 0 else -1.
  Definition sign_ulo_sym w a :=
    if zero a then 0 else if pos a then 1 else sign_half_class w.
  Definition sign_uhi_sym w a :=
    if neg a then 2 * sign_half_class w - 1
    else if pos a then sign_half_class w - 1 else 0.
  Definition sign_cmp_sym o w a b :=
    match o with
    | bveq => sign_cmp_eq (sign_lo_sym w a) (sign_hi_sym w a)
        (sign_lo_sym w b) (sign_hi_sym w b)
    | bvne => sign_bool_not (sign_cmp_eq (sign_lo_sym w a) (sign_hi_sym w a)
        (sign_lo_sym w b) (sign_hi_sym w b))
    | bvult => sign_cmp_lt (sign_ulo_sym w a) (sign_uhi_sym w a)
        (sign_ulo_sym w b) (sign_uhi_sym w b)
    | bvule => sign_cmp_le (sign_ulo_sym w a) (sign_uhi_sym w a)
        (sign_ulo_sym w b) (sign_uhi_sym w b)
    | bvslt => sign_cmp_lt (sign_lo_sym w a) (sign_hi_sym w a)
        (sign_lo_sym w b) (sign_hi_sym w b)
    | bvsle => sign_cmp_le (sign_lo_sym w a) (sign_hi_sym w a)
        (sign_lo_sym w b) (sign_hi_sym w b)
    | _ => sign_bool_top
    end.
  Definition wfwd (o : L.op) (rw : positive) (xs : list (positive * S.p)) : option S.p :=
    match o, xs with
    | bvnot, [(_, a)] => Some (S.sign_not a)
    | bvneg, [(_, a)] => Some (S.sign_neg a)
    | bvzext _, [(_, _)] => Some (Sgn false true true)
    | bvsext _, [(_, a)] => Some a
    | bvand, [(_, a); (_, b)] => Some (S.sign_and a b)
    | bvor, [(_, a); (_, b)] => Some (S.sign_or a b)
    | bvxor, [(_, a); (_, b)] => Some (S.sign_xor a b)
    | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] =>
        Some (sign_cmp_sym o w a b)
    | bvite, [_; (_, a); (_, b)] => Some (S.pjoin rw a b)
    | _, _ => None
    end.
  Definition wbwd (_ : L.op) (_ : positive) (_ : S.p)
      (_ : list (positive * S.p)) : option (list S.p) := None.
End SignTableCode.

Module Sign (L : WORD_LANGUAGE) <: SIGN L.
  Include SignCode L.
  Include SIGN_SPEC L.
  Definition pgamma := sign_gamma.
  Definition pwrank (_ : pwparam) (_ : positive) (a : p) : nat := 3 - sign_level a.

  (** Each inhabited signed class requires its corresponding flag. *)
  Local Lemma pgamma_cases w a z : pgamma w a z <->
    (Word.signed w z < 0 -> neg a = true) /\
    (Word.signed w z = 0 -> zero a = true) /\
    (0 < Word.signed w z -> pos a = true).
  Proof.
    unfold pgamma, sign_gamma, L.signed.
    destruct (Word.signed w z <? 0) eqn:Hneg.
    - apply Z.ltb_lt in Hneg. split; intros H; intuition lia.
    - apply Z.ltb_ge in Hneg. destruct (Word.signed w z =? 0) eqn:Hzero.
      + apply Z.eqb_eq in Hzero. split; intros H; intuition lia.
      + apply Z.eqb_neq in Hzero. split.
        * intros H. intuition lia.
        * intros [_ [_ Hp]]. apply Hp. lia.
  Qed.

  (** Widening contains both payloads. *)
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof.
    intros q w. intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  Qed.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof.
    intros q w. intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  Qed.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof.
    intros q w [a b c] [d e f] Hle. destruct a, b, c, d, e, f;
      cbn in Hle |- *; try discriminate; reflexivity.
  Qed.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof.
    intros q w [a b c] [d e f] Hbot Hstrict. destruct a, b, c, d, e, f;
      cbn in Hstrict |- *; try discriminate; lia.
  Qed.
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof.
    intros q w [a b c] [d e f] Hbot. destruct a, b, c, d, e, f;
      cbn; lia.
  Qed.
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof.
    intros w [a b c] [d e f] Hle. destruct a, b, c, d, e, f;
      cbn in Hle |- *; try discriminate; split; reflexivity.
  Qed.
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof. intros w [a b c]. destruct a, b, c; reflexivity. Qed.
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof.
    intros w [a b c] [d e f] [g h i]. destruct a, b, c, d, e, f, g, h, i;
      cbn; intros; try discriminate; reflexivity.
  Qed.
  (** Bottom is below every payload. *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof. intros w [a b c]. reflexivity. Qed.
  (** Top is above every payload. *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof.
    intros w [a b c]. destruct a, b, c; reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof.
    intro w. reflexivity.
  Qed.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof.
    intros w [a b c] d Hbot. destruct a, b, c;
      cbn in Hbot |- *; try discriminate; reflexivity.
  Qed.
  (** Join contains the left payload. *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof. intros w [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity. Qed.
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof. intros w [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity. Qed.
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof.
    intros w [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  Qed.
  (** Meet refines the right payload. *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof.
    intros w [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  Qed.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof.
    intros w [an az ap] [bn bz bp] z Hle Hg.
    apply pgamma_cases in Hg. apply pgamma_cases.
    destruct an, az, ap, bn, bz, bp; cbn in Hle, Hg |- *;
      try discriminate; intuition.
  Qed.
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof.
    intros w z Hg. apply pgamma_cases in Hg as [Hn [Hz Hp]].
    destruct (Z.lt_trichotomy (Word.signed w z) 0) as [Hneg|[Hzero|Hpos]].
    - discriminate (Hn Hneg).
    - discriminate (Hz Hzero).
    - discriminate (Hp Hpos).
  Qed.
  (** Top contains every normalized integer at its width. *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof.
    intros w z _. unfold pgamma, sign_gamma, ptop.
    destruct (L.signed w z <? 0); [reflexivity|].
    destruct (L.signed w z =? 0); reflexivity.
  Qed.
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof.
    intros w a b z Ha Hb. apply pgamma_cases in Ha as [Hn [Hz Hp]].
    apply pgamma_cases in Hb as [Hn' [Hz' Hp']]. apply pgamma_cases.
    split; [|split]; cbn [pmeet neg zero pos]; intro Hsign;
      apply andb_true_iff; auto.
  Qed.
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof.
    intros w [n q p] x Hempty Hg. destruct n, q, p; cbn in Hempty; try discriminate. exact (pgamma_bot w x Hg).
  Qed.
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof.
    intros w [a b c] [d e f] Hle Hbot. destruct a, b, c, d, e, f;
      cbn in Hle, Hbot |- *; try discriminate; reflexivity.
  Qed.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof.
    intros w z. unfold pgamma, sign_gamma, pconst.
    rewrite signed_wrap.
    destruct (Word.signed w z <? 0) eqn:Hneg; cbn; [reflexivity|].
    destruct (Word.signed w z =? 0) eqn:Hzero; cbn; [reflexivity|].
    apply Z.ltb_lt. change (0 < Word.signed w z).
    apply Z.ltb_ge in Hneg. apply Z.eqb_neq in Hzero. lia.
  Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof.
    intros w [n q p] z v Hpoint Hword Hg.
    destruct n, q, p; cbn in Hpoint; try discriminate.
    injection Hpoint as <-. apply pgamma_cases in Hg as [Hn [Hz Hp]].
    assert (Hsigned : Word.signed w z = 0).
    { destruct (Z.lt_trichotomy (Word.signed w z) 0) as [Hneg|[Hzero|Hpos]];
        [discriminate (Hn Hneg)|exact Hzero|discriminate (Hp Hpos)]. }
    assert (Hwrap : wrap w z = wrap w 0).
    { apply signed_inj. now rewrite signed_zero. }
    now rewrite wrap_0, wrap_id in Hwrap by exact Hword.
  Qed.
  (** Payload concretization reads the sign flags. *)
  Lemma F1_gamma : forall w a z, pgamma w a z <-> sign_gamma w a z.
  Proof.
    intros w a z. reflexivity.
  Qed.

  (** The most significant bit selects the negative or nonnegative flags. *)
  Local Lemma sign_class w a x : pgamma w a x ->
    (if msb w x then neg a else sign_nonneg a) = true.
  Proof.
    intros Hg. apply pgamma_cases in Hg as [Hn [Hz Hp]].
    destruct (msb w x) eqn:Hmsb.
    - apply Hn. now apply signed_neg_iff_msb.
    - pose proof (signed_nonnegative w x Hmsb) as Hsigned.
      pose proof (wrap_is_word w x) as [Hlo Hhi].
      destruct (Z.eq_dec (Word.signed w x) 0) as [Heq|Hneq].
      + unfold sign_nonneg. rewrite (Hz Heq). reflexivity.
      + unfold sign_nonneg. rewrite (Hp ltac:(lia)). apply orb_true_r.
  Qed.

  (** A sign bit and two nonnegative flags suffice for concretization. *)
  Local Lemma sign_from_msb w a x :
    (msb w x = true -> neg a = true) ->
    (msb w x = false -> zero a = true /\ pos a = true) -> pgamma w a x.
  Proof.
    intros Hn Hnn. apply pgamma_cases. split; [|split]; intro Hsign.
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

  (** Integer bitwise operations preserve their Boolean sign-bit equations after wrapping. *)
  Local Lemma sign_bitwise_msb w x y :
    msb w (wrap w (Z.land x y)) = (msb w x && msb w y) /\
    msb w (wrap w (Z.lor x y)) = (msb w x || msb w y) /\
    msb w (wrap w (Z.lxor x y)) = xorb (msb w x) (msb w y).
  Proof.
    rewrite !msb_testbit, !testbit_wrap by lia.
    rewrite (proj2 (Z.ltb_lt (Zpos w - 1) (Zpos w)) ltac:(lia)).
    rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec. auto.
  Qed.

  (** Bitwise negation retains every normalized concrete result. *)
  Lemma F3_sign_not_sound : forall w a x, L.is_word w x -> pgamma w a x ->
    pgamma w (sign_not a) (L.wrap w (Z.lnot x)).
  Proof.
    intros w a x Hx Ha. pose proof (sign_class w a x Ha) as Hfa.
    assert (Hnot : msb w (L.wrap w (Z.lnot x)) = negb (msb w x)).
    { rewrite !msb_testbit, testbit_wrap, Z.lnot_spec by lia.
      rewrite (proj2 (Z.ltb_lt (Zpos w - 1) (Zpos w)) ltac:(lia)). reflexivity. }
    apply sign_from_msb; cbn [sign_not sign_bits neg zero pos]; rewrite Hnot;
      destruct (msb w x); cbn in Hfa |- *; intro Hresult; try discriminate; auto.
  Qed.
  (** Arithmetic negation retains every normalized concrete result. *)
  Lemma F4_sign_neg_sound : forall w a x, L.is_word w x -> pgamma w a x ->
    pgamma w (sign_neg a) (L.wrap w (- x)).
  Proof.
    intros w a x Hx Ha. apply pgamma_cases in Ha as [Hn [Hz Hp]].
    pose proof (half_pos w). pose proof (modulus_half w).
    assert (Hwrap : wrap w (- x) = if x =? 0 then 0 else modulus w - x).
    { destruct (x =? 0) eqn:Hxzero.
      - apply Z.eqb_eq in Hxzero. subst x. apply wrap_0.
      - apply Z.eqb_neq in Hxzero.
        replace (- x) with ((modulus w - x) + (-1) * modulus w) by ring.
        rewrite wrap_add_modulus. apply wrap_id. split; destruct Hx; lia. }
    apply pgamma_cases. cbn [sign_neg neg zero pos].
    rewrite signed_value, wrap_wrap, Hwrap.
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
  (** Bitwise conjunction retains every normalized concrete result. *)
  Lemma F5_sign_and_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_and a b) (L.wrap w (Z.land x y)).
  Proof.
    intros w a b x y Hx Hy Ha Hb.
    pose proof (sign_class w a x Ha) as Hfa. pose proof (sign_class w b y Hb) as Hfb.
    unfold L.wrap.
    apply sign_from_msb; cbn [sign_and sign_bits neg zero pos];
      rewrite (proj1 (sign_bitwise_msb w x y));
      destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
      intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r;
      cbn; auto.
  Qed.
  (** Bitwise disjunction retains every normalized concrete result. *)
  Lemma F6_sign_or_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_or a b) (L.wrap w (Z.lor x y)).
  Proof.
    intros w a b x y Hx Hy Ha Hb.
    pose proof (sign_class w a x Ha) as Hfa. pose proof (sign_class w b y Hb) as Hfb.
    unfold L.wrap.
    apply sign_from_msb; cbn [sign_or sign_bits neg zero pos];
      rewrite (proj1 (proj2 (sign_bitwise_msb w x y)));
      destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
      intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r;
      cbn; auto.
  Qed.
  (** Bitwise exclusive disjunction retains every normalized concrete result. *)
  Lemma F7_sign_xor_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_xor a b) (L.wrap w (Z.lxor x y)).
  Proof.
    intros w a b x y Hx Hy Ha Hb.
    pose proof (sign_class w a x Ha) as Hfa. pose proof (sign_class w b y Hb) as Hfb.
    unfold L.wrap.
    apply sign_from_msb; cbn [sign_xor sign_bits neg zero pos];
      rewrite (proj2 (proj2 (sign_bitwise_msb w x y)));
      destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
      intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r;
      cbn; auto.
  Qed.
End Sign.

Module SignT (L : WORD_LANGUAGE_T) <: SIGN_T L.
  Include Sign L.

  TimeFun pleb.
  TimeFun pjoin.
  TimeFun pmeet.
  TimeFun pbot.
  TimeFun ptop.
  TimeFun pis_bot.
  TimeFun pconst.
  TimeFun ppoint.
  TimeFun pwiden.
  TimeFun pnarrow.
  TimeFun sign_nonneg.
  TimeFun sign_bits.
  TimeFun sign_not.
  TimeFun sign_neg.
  TimeFun sign_and.
  TimeFun sign_or.
  TimeFun sign_xor.

  Definition psize (w : positive) (_ : p) : nat := Pos.to_nat w.
  Definition pwsize (_ : pwparam) : nat := 1.
  Definition c_payload : N := 1%N. (* STUB *)
  (** STUB: sign payload size and cost obligations. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pconst_le : forall w z, (T_pconst w z <=
    c_payload * N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)

  Definition c_sign : N := 1%N. (* STUB *)
  (** Flag inclusion takes constant time. *)
  Lemma T_pleb_const : forall w a b, (T_pleb w a b <= c_sign)%N.
  Proof. Admitted. (* STUB *)
  (** Flag join takes constant time. *)
  Lemma T_pjoin_const : forall w a b, (T_pjoin w a b <= c_sign)%N.
  Proof. Admitted. (* STUB *)
  (** Flag meet takes constant time. *)
  Lemma T_pmeet_const : forall w a b, (T_pmeet w a b <= c_sign)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sign_not_le : forall a, (T_sign_not a <= c_sign)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sign_neg_le : forall a, (T_sign_neg a <= c_sign)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sign_and_le : forall a b, (T_sign_and a b <= c_sign)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sign_or_le : forall a b, (T_sign_or a b <= c_sign)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sign_xor_le : forall a b, (T_sign_xor a b <= c_sign)%N.
  Proof. Admitted. (* STUB *)
  Lemma psize_width : forall w a, psize w a = Pos.to_nat w.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
End SignT.

Module SignAll (L : WORD_LANGUAGE_T) <: SIGN_ALL L.
  Include SignT L.
  Lemma F2_level : forall a, (sign_level a <= 3)%nat.
  Proof.
    intros [a b c]. destruct a, b, c; cbn; lia.
  Qed.
  Lemma F_pwrank : forall q w a, pwrank q w a = Nat.sub 3 (sign_level a).
  Proof.
    intros q w a. reflexivity.
  Qed.
End SignAll.

Module SignTable (L : WORD_LANGUAGE) (W : SIGN L) <: SIGN_TABLE L W.
  Include SignTableCode L W.
  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted. (* CONVERT: sign_table_laws: No product even after head-reduction. *)
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. intros o rw q wps ys cs z Hf. discriminate Hf. Qed.
End SignTable.

Module SignTableT (L : WORD_LANGUAGE_T) (S : SIGN_T L) <: SIGN_TABLE_ALL L S.
  Include SignTable L S.
  TimeFun sign_nonneg.
  TimeFun sign_lo.
  TimeFun sign_hi.
  TimeFun sign_ulo.
  TimeFun sign_uhi.
  TimeFun sign_boolean.
  TimeFun sign_bool_top.
  TimeFun sign_bool_not.
  TimeFun sign_cmp_lt.
  TimeFun sign_cmp_le.
  TimeFun sign_cmp_eq.
  TimeFun sign_cmp.
  TimeFun sign_half_class.
  TimeFun sign_lo_sym.
  TimeFun sign_hi_sym.
  TimeFun sign_ulo_sym.
  TimeFun sign_uhi_sym.
  TimeFun sign_cmp_sym.
  TimeFun wfwd.
  TimeFun wbwd.
  Definition c_sign_table : N := 1%N. (* STUB *)
  Definition c_word_table : N := 1%N. (* STUB *)
  (** The bounded flag comparison keeps every numeric comparator result. *)
  Lemma F_sign_cmp_sym : forall c w a b, sign_cmp_sym c w a b = sign_cmp c w a b.
  Proof. Admitted. (* STUB *)
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => S.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        S.psize rw q +
        fold_right Nat.add 0 (map (fun x => S.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sign_entry_le : forall o rw xs, (T_wfwd o rw xs <= c_sign_table)%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (S.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => S.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => S.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        S.psize rw q +
        fold_right Nat.add 0 (map (fun x => S.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
End SignTableT.
