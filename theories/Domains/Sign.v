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
