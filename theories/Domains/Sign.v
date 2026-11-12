(** * Signed sign payload code

    Three Boolean flags represent signed word classes.
    For example, a zero-only payload represents the integer zero.
    Builds on: SignSig and the fixed-width word operations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time Std.
From Galois.Bits Require Import Word Op Arith.
From Galois.Domains Require Import SignSig WordSig.
Import List.ListNotations.

Local Open Scope Z_scope.

Module SignSig.
  TimeFun Galois.Domains.SignSig.neg.
  TimeFun Galois.Domains.SignSig.zero.
  TimeFun Galois.Domains.SignSig.pos.
End SignSig.

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
    Sgn (L.signed w z <? 0) (L.signed w z =? 0) (0 <? L.signed w z).
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
  Definition sign_lo w a := if neg a then - half w else if zero a then 0 else 1.
  Definition sign_hi w a := if pos a then half w - 1 else if zero a then 0 else -1.
  Definition sign_ulo w a := if zero a then 0 else if pos a then 1 else half w.
  Definition sign_uhi w a := if neg a then modulus w - 1 else if pos a then half w - 1 else 0.
  Definition sign_boolean (b : bool) := if b then Sgn true false false else Sgn false true false.
  Definition sign_bool_top := Sgn true true false.
  Definition sign_bool_not s := Sgn (zero s) (neg s) false.
  Definition sign_cmp_lt lo hi lo' hi' :=
    if hi <? lo' then sign_boolean true else
    if hi' <=? lo then sign_boolean false else sign_bool_top.
  Definition sign_cmp_le lo hi lo' hi' :=
    if hi <=? lo' then sign_boolean true else
    if hi' <? lo then sign_boolean false else sign_bool_top.
  Definition sign_cmp_eq lo hi lo' hi' :=
    if (hi <? lo') || (hi' <? lo) then sign_boolean false else
    if (lo =? hi) && (lo' =? hi') && (lo =? lo') then sign_boolean true else sign_bool_top.
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
        Some (sign_cmp o w a b)
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
  Proof. Admitted.
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
  Proof. Admitted.
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
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof. Admitted.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof. Admitted.
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
  Proof. Admitted.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof. Admitted. (* CONVERT: sign_mono: Attempt to save an incomplete proof. *)
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof. Admitted. (* CONVERT: sign_bot_empty: Not an inductive product. *)
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
  Proof. Admitted. (* CONVERT: sign_meet_sound: Not an inductive product. *)
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof.
    intros w [n q p] x Hempty Hg. destruct n, q, p; cbn in Hempty; try discriminate. exact (pgamma_bot w x Hg).
  Qed.
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof. Admitted.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof.
    intros w z. unfold pgamma, sign_gamma, pconst.
    rewrite signed_wrap.
    destruct (Word.signed w z <? 0) eqn:Hneg; cbn; [exact Hneg|].
    destruct (Word.signed w z =? 0) eqn:Hzero; cbn; [exact Hzero|].
    apply Z.ltb_lt. change (0 < Word.signed w z).
    apply Z.ltb_ge in Hneg. apply Z.eqb_neq in Hzero. lia.
  Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof. Admitted. (* CONVERT: sign_shape_laws: Not an inductive definition. *)
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

  Definition psize (_ : positive) (_ : p) : nat := 1.
  Definition pwsize (_ : pwparam) : nat := 1.
  Definition c_payload : N := 1%N.
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

  Definition c_sign : N := 1%N.
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
End SignT.

Module SignAll (L : WORD_LANGUAGE_T) <: SIGN_ALL L.
  Include SignT L.
  Definition k_sign : N := 1%N. (* STUB *)
  Lemma F1_gamma : forall w a z, pgamma w a z <-> sign_gamma w a z.
  Proof. Admitted. (* STUB *)
  Lemma F2_level : forall a, (sign_level a <= 3)%nat.
  Proof. Admitted. (* STUB *)
  Lemma F_pwrank : forall q w a, pwrank q w a = Nat.sub 3 (sign_level a).
  Proof. Admitted. (* STUB *)
  Lemma F3_sign_not_sound : forall w a x, L.is_word w x -> pgamma w a x ->
    pgamma w (sign_not a) (L.wrap w (Z.lnot x)).
  Proof. Admitted. (* STUB *)
  Lemma F4_sign_neg_sound : forall w a x, L.is_word w x -> pgamma w a x ->
    pgamma w (sign_neg a) (L.wrap w (- x)).
  Proof. Admitted. (* STUB *)
  Lemma F5_sign_and_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_and a b) (L.wrap w (Z.land x y)).
  Proof. Admitted. (* STUB *)
  Lemma F6_sign_or_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_or a b) (L.wrap w (Z.lor x y)).
  Proof. Admitted. (* STUB *)
  Lemma F7_sign_xor_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_xor a b) (L.wrap w (Z.lxor x y)).
  Proof. Admitted. (* STUB *)
  Lemma T1_pleb : forall w a b, (T_pleb w a b <= k_sign)%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_pjoin : forall w a b, (T_pjoin w a b <= k_sign)%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_pmeet : forall w a b, (T_pmeet w a b <= k_sign)%N.
  Proof. Admitted. (* STUB *)
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

Module SignTableT (L : WORD_LANGUAGE_T) (S : SIGN_T L) <: SIGN_TABLE_T L S.
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
  TimeFun wfwd.
  TimeFun wbwd.
  Definition c_sign_table : N := 1%N. (* STUB *)
  Definition c_word_table : N := 1%N. (* STUB *)
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
End SignTableT.
