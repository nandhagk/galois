(** * Word interval operations

    Endpoint arithmetic retains finite ranges when they fit the word width.
    For example, adding [1, 4] to [2, 5] yields [3, 9] at width eight.
    Builds on: Interval and the fixed-width word operations. *)

From Stdlib Require Import ZArith List Bool.
From Argent Require Import Time Std.
From Galois.Bits Require Import Word Fun Op.
From Galois.Domains Require Import Interval IntervalSig ThresholdsSig ValueSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Datatypes.
  TimeFun Corelib.Init.Datatypes.xorb.
End Datatypes.
Module Bool.
  TimeFun Bool.eqb.
End Bool.

Module IntervalOpsCode (T : THRESHOLDS_OPS) (Scalar : INTERVAL_SCALAR_OPS T).

  Definition interval_top (w : width) : itv := I (Fin 0) (Fin (modulus w - 1)).
  Definition interval_const (w : width) (z : Z) : itv :=
    I (Fin (wrap w z)) (Fin (wrap w z)).
  Definition interval_clip (w : width) (a : itv) := Scalar.interval_meet a (interval_top w).
Definition interval_checked (w : width) (lo hi : Z) : itv :=
  if (Z.leb 0 lo && Z.ltb hi (modulus w))%bool
  then I (Fin lo) (Fin hi) else interval_top w.

Definition interval_add (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) => interval_checked w (la + lb) (ha + hb)
  | _, _ => interval_top w
  end.

Definition interval_add_modular (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb (modulus w) (la + lb) && Z.ltb (ha + hb) (2 * modulus w))%bool
    then interval_checked w (la + lb - modulus w) (ha + hb - modulus w)
    else interval_add w a b
  | _, _ => interval_top w
  end.

Definition interval_sub (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) => interval_checked w (la - hb) (ha - lb)
  | _, _ => interval_top w
  end.

Definition interval_mul (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb)%bool
    then interval_checked w (la * lb) (ha * hb) else interval_top w
  | _, _ => interval_top w
  end.

Definition interval_neg (w : width) (a : itv) : itv :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.eqb hi 0 then I (Fin 0) (Fin 0)
    else if Z.ltb 0 lo then interval_checked w (modulus w - hi) (modulus w - lo)
    else interval_top w
  | None => interval_top w
  end.

Definition interval_concat (rw lower_width : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    interval_checked rw (la * modulus lower_width + lb) (ha * modulus lower_width + hb)
  | _, _ => interval_top rw
  end.

Definition interval_rewrap (rw : width) (a : itv) : itv :=
  match interval_finite_helper a with
  | Some (lo, hi) => interval_checked rw lo hi
  | None => interval_top rw
  end.

Definition interval_counts (w : width) : itv := I (Fin 0) (Fin (Zpos w)).

Definition interval_udiv (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.ltb 0 lb)%bool
    then interval_checked w (la / hb) (ha / lb)
    else if (Z.leb 0 la && Z.eqb lb 0 && Z.ltb 0 hb)%bool
         then interval_checked w (la / hb) (modulus w - 1)
         else if (Z.eqb lb 0 && Z.eqb hb 0)%bool
              then I (Fin (modulus w - 1)) (Fin (modulus w - 1))
              else interval_top w
  | _, _ => interval_top w
  end.

Definition interval_urem (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.ltb 0 lb && Z.eqb (la / hb) (ha / lb))%bool then
      let quotient := la / hb in
      interval_checked w (la - quotient * hb) (ha - quotient * lb)
    else interval_checked w 0 (if Z.ltb 0 lb then Z.min ha (hb - 1) else ha)
  | _, _ => interval_top w
  end.

Definition interval_not (w : width) (a : itv) : itv :=
  match interval_finite_helper a with
  | Some (lo, hi) => interval_checked w (modulus w - 1 - hi) (modulus w - 1 - lo)
  | None => interval_top w
  end.

Definition interval_and (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (_, ha), Some (_, hb) => interval_checked w 0 (Z.min ha hb)
  | _, _ => interval_top w
  end.

Definition interval_mask (hi : Z) : Z :=
  if Z.eqb hi 0 then 0 else Z.ones (Z.log2 hi + 1).

Definition interval_or_xor (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (_, ha), Some (_, hb) => interval_checked w 0 (interval_mask (Z.max ha hb))
  | _, _ => interval_top w
  end.

Definition interval_truth (decision : option bool) : itv :=
  match decision with
  | Some true => I (Fin 1) (Fin 1)
  | Some false => I (Fin 0) (Fin 0)
  | None => I (Fin 0) (Fin 1)
  end.

Definition interval_bool_not (a : itv) : itv :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.eqb lo 0 && Z.eqb hi 0 then interval_truth (Some true)
    else if Z.eqb lo 1 && Z.eqb hi 1 then interval_truth (Some false)
    else interval_truth None
  | None => interval_truth None
  end.

Definition interval_ult (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if Z.ltb ha lb then Some true
                    else if Z.leb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

Definition interval_ule (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if Z.leb ha lb then Some true
                    else if Z.ltb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

Definition interval_eq (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if (Z.ltb ha lb || Z.ltb hb la)%bool then Some false
      else if (Z.eqb la ha && Z.eqb lb hb && Z.eqb la lb)%bool then Some true else None)
  | _, _ => interval_truth None
  end.

Definition interval_shl (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (la * 2 ^ lb) (ha * 2 ^ hb) else interval_top w
  | _, _ => interval_top w
  end.

Definition interval_lshr (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (la / 2 ^ hb) (ha / 2 ^ lb) else interval_top w
  | _, _ => interval_top w
  end.

Definition interval_sign (w : width) (a : itv) : option bool :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.ltb hi (half w) then Some false
    else if Z.leb (half w) lo then Some true else None
  | None => None
  end.

Definition interval_signed (w : width) (a : itv) : option (Z * Z) :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.ltb hi (half w) then Some (lo, hi)
    else if Z.leb (half w) lo then Some (lo - modulus w, hi - modulus w)
    else None
  | None => None
  end.

Definition interval_sext (rw w : width) (a : itv) : itv :=
  match interval_signed w a with
  | Some (lo, hi) =>
    if Z.ltb hi 0 then interval_checked rw (modulus rw + lo) (modulus rw + hi)
    else if Z.leb 0 lo then interval_checked rw lo hi else interval_top rw
  | None => interval_top rw
  end.

Definition interval_signed_compare (w : width) (strict : bool) (a b : itv) : itv :=
  match interval_signed w a, interval_signed w b with
  | Some (la, ha), Some (lb, hb) =>
    if strict then
      interval_truth (if Z.ltb ha lb then Some true
                      else if Z.leb hb la then Some false else None)
    else
      interval_truth (if Z.leb ha lb then Some true
                      else if Z.ltb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

Definition interval_sdiv (w : width) (a b : itv) : itv :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let q := interval_udiv w aa bb in
    if xorb sa sb then interval_neg w q else q
  | _, _ => interval_top w
  end.

Definition interval_srem (w : width) (a b : itv) : itv :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let r := interval_urem w aa bb in
    if sa then interval_neg w r else r
  | _, _ => interval_top w
  end.

Definition interval_mod_choice (u candidate : itv) : itv :=
  match interval_finite_helper u with
  | Some (lo, hi) =>
    if Z.ltb 0 lo then candidate
    else if Z.eqb hi 0 then I (Fin 0) (Fin 0)
    else Scalar.interval_join (I (Fin 0) (Fin 0)) candidate
  | None => Scalar.interval_join (I (Fin 0) (Fin 0)) candidate
  end.

Definition interval_smod_base (w : width) (a b : itv) : itv :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let u := interval_urem w aa bb in
    let candidate :=
      match sa, sb with
      | false, false => u
      | true, false => interval_add_modular w (interval_neg w u) b
      | false, true => interval_add_modular w u b
      | true, true => interval_neg w u
      end in
    interval_mod_choice u candidate
  | _, _ => interval_top w
  end.

Definition interval_smod (w : width) (a b : itv) : itv :=
  match interval_sign w b, interval_finite_helper b with
  | Some false, Some (lo, hi) =>
    if Z.ltb 0 lo then
      Scalar.interval_meet (interval_smod_base w a b) (I (Fin 0) (Fin (hi - 1)))
    else interval_smod_base w a b
  | _, _ => interval_smod_base w a b
  end.

Definition interval_ashr_small (w : width) (a b : itv) : itv :=
  match interval_sign w a with
  | Some false => interval_lshr w a b
  | Some true => interval_not w (interval_lshr w (interval_not w a) b)
  | None => interval_top w
  end.

Definition interval_ashr (w : width) (a b : itv) : itv :=
  match interval_sign w a, interval_finite_helper b with
  | Some sign, Some (lo, hi) =>
    let saturated := if sign then modulus w - 1 else 0 in
    if Z.ltb hi (Zpos w) then interval_ashr_small w a b
    else if Z.leb (Zpos w) lo then I (Fin saturated) (Fin saturated)
    else Scalar.interval_join
      (interval_ashr_small w a (I (Fin lo) (Fin (Zpos w - 1))))
      (I (Fin saturated) (Fin saturated))
  | _, _ => interval_ashr_small w a b
  end.

Definition interval_swap (p : itv * itv) : itv * itv := (snd p, fst p).

Definition interval_assume_equal (a b : itv) : itv * itv :=
  (Scalar.interval_meet a b, Scalar.interval_meet b a).

Definition interval_assume_ult (a b : itv) : itv * itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, _), Some (_, hb) =>
    (Scalar.interval_meet a (I NegInf (Fin (hb - 1))),
     Scalar.interval_meet b (I (Fin (la + 1)) PosInf))
  | _, _ => (a, b)
  end.

Definition interval_assume_ule (a b : itv) : itv * itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, _), Some (_, hb) =>
    (Scalar.interval_meet a (I NegInf (Fin hb)), Scalar.interval_meet b (I (Fin la) PosInf))
  | _, _ => (a, b)
  end.

Definition interval_assume_add (w : width) (a b q : itv) : itv * itv :=
  match interval_finite_helper a, interval_finite_helper b, interval_finite_helper q with
  | Some (la, ha), Some (lb, hb), Some (lq, hq) =>
    if Z.ltb (ha + hb) (modulus w) then
      (Scalar.interval_meet a (I (Fin (lq - hb)) (Fin (hq - lb))),
       Scalar.interval_meet b (I (Fin (lq - ha)) (Fin (hq - la))))
    else (a, b)
  | _, _, _ => (a, b)
  end.

Definition interval_assume_sub (a b q : itv) : itv * itv :=
  match interval_finite_helper a, interval_finite_helper b, interval_finite_helper q with
  | Some (la, ha), Some (lb, hb), Some (lq, hq) =>
    if Z.leb hb la then
      (Scalar.interval_meet a (I (Fin (lq + lb)) (Fin (hq + hb))),
       Scalar.interval_meet b (I (Fin (la - hq)) (Fin (ha - lq))))
    else (a, b)
  | _, _, _ => (a, b)
  end.

Definition interval_assume_rewrap (rw : width) (a q : itv) : itv :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool then Scalar.interval_meet a q else a
  | None => a
  end.

Definition interval_exclude (a : itv) (c : Z) : itv :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.eqb lo c then Scalar.interval_meet a (I (Fin (c + 1)) PosInf)
    else if Z.eqb hi c then Scalar.interval_meet a (I NegInf (Fin (c - 1)))
    else a
  | None => a
  end.

Definition interval_assume_neq (a b : itv) : itv * itv :=
  (match Scalar.interval_singleton b with Some c => interval_exclude a c | None => a end,
   match Scalar.interval_singleton a with Some c => interval_exclude b c | None => b end).

Definition interval_assume_signed (w : width) (strict result : bool)
    (a b : itv) : itv * itv :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    if Bool.eqb sa sb then
      match strict, result with
      | true, true => interval_assume_ult a b
      | true, false => interval_swap (interval_assume_ule b a)
      | false, true => interval_assume_ule a b
      | false, false => interval_swap (interval_assume_ult b a)
      end
    else (a, b)
  | _, _ => (a, b)
  end.

End IntervalOpsCode.

Module IntervalOpsT (T : THRESHOLDS_T) (Scalar : INTERVAL_SCALAR_T T).
  Include IntervalOpsCode T Scalar.
  TimeFun interval_top.
  TimeFun interval_const.
  TimeFun interval_clip.
  TimeFun interval_checked.
  TimeFun interval_add.
  TimeFun interval_add_modular.
  TimeFun interval_sub.
  TimeFun interval_mul.
  TimeFun interval_neg.
  TimeFun interval_concat.
  TimeFun interval_rewrap.
  TimeFun interval_counts.
  TimeFun interval_udiv.
  TimeFun interval_urem.
  TimeFun interval_not.
  TimeFun interval_and.
  TimeFun interval_mask.
  TimeFun interval_or_xor.
  TimeFun interval_truth.
  TimeFun interval_bool_not.
  TimeFun interval_ult.
  TimeFun interval_ule.
  TimeFun interval_eq.
  TimeFun interval_shl.
  TimeFun interval_lshr.
  TimeFun interval_sign.
  TimeFun interval_signed.
  TimeFun interval_sext.
  TimeFun interval_signed_compare.
  TimeFun interval_sdiv.
  TimeFun interval_srem.
  TimeFun interval_mod_choice.
  TimeFun interval_smod_base.
  TimeFun interval_smod.
  TimeFun interval_ashr_small.
  TimeFun interval_ashr.
  TimeFun interval_swap.
  TimeFun interval_assume_equal.
  TimeFun interval_assume_ult.
  TimeFun interval_assume_ule.
  TimeFun interval_assume_add.
  TimeFun interval_assume_sub.
  TimeFun interval_assume_rewrap.
  TimeFun interval_exclude.
  TimeFun interval_assume_neq.
  TimeFun interval_assume_signed.
End IntervalOpsT.
