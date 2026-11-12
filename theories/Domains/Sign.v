(** * Signed sign payload code

    Three Boolean flags represent signed word classes.
    For example, a zero-only payload represents the integer zero.
    Builds on: SignSig and the fixed-width word operations. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Op.
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
  Proof. Admitted.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof. Admitted.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted.
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted.
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted.
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof. Admitted.
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof. Admitted.
  (** Bottom is below every payload. *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof. Admitted.
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
  Proof. Admitted.
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof. Admitted.
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof. Admitted.
  (** Meet refines the right payload. *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof. Admitted.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof. Admitted.
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof. Admitted.
  (** Top contains every normalized integer at its width. *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof. Admitted.
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. Admitted.
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof. Admitted.
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof. Admitted.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof. Admitted.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> pgamma w a z -> z = v.
  Proof. Admitted.
End Sign.

Module SignTable (L : WORD_LANGUAGE) (W : SIGN L) <: SIGN_TABLE L W.
  Include SignTableCode L W.
  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted.
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. Admitted.
End SignTable.
