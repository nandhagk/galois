(** * Interval lattice operations

    Intervals use integer bounds and threshold widening.
    For example, meeting disjoint finite intervals returns bottom.
    Builds on: IntervalSig and ThresholdsSig. *)

From Stdlib Require Import ZArith Bool.
From Galois.Domains Require Import ValueSig IntervalSig ThresholdsSig.

Module IntervalBaseCode (T : THRESHOLDS_OPS).
  Definition bound_leb (a b : bnd) : bool :=
    match a, b with
    | NegInf, _ => true
    | _, PosInf => true
    | Fin x, Fin y => Z.leb x y
    | _, _ => false
    end.
  Definition bound_min a b := if bound_leb a b then a else b.
  Definition bound_max a b := if bound_leb a b then b else a.
  Definition widen_lower ts old next :=
    if bound_leb old next then old else
      match next with
      | NegInf => NegInf
      | Fin z => match T.below ts z with Some u => Fin u | None => NegInf end
      | PosInf => PosInf
      end.
  Definition widen_upper ts old next :=
    if bound_leb next old then old else
      match next with
      | NegInf => NegInf
      | Fin z => match T.above ts z with Some u => Fin u | None => PosInf end
      | PosInf => PosInf
      end.
  Definition narrow_bound old next :=
    match old with
    | Fin _ => old
    | _ => next
    end.
  Definition interval_leb (a b : itv) :=
    match a, b with
    | IBot, _ => true
    | I _ _, IBot => false
    | I l h, I l' h' => bound_leb l' l && bound_leb h h'
    end.
  Definition interval_join (a b : itv) :=
    match a, b with
    | IBot, _ => b
    | _, IBot => a
    | I l h, I l' h' => I (bound_min l l') (bound_max h h')
    end.
  Definition interval_widen ts (a b : itv) :=
    match a, b with
    | IBot, _ => b
    | _, IBot => a
    | I l h, I l' h' => I (widen_lower ts l l') (widen_upper ts h h')
    end.
  Definition interval_narrow (a b : itv) :=
    match a, b with
    | IBot, _ => IBot
    | _, IBot => a
    | I l h, I l' h' => I (narrow_bound l l') (narrow_bound h h')
    end.
  Definition bounds_nonempty lo hi :=
    match lo, hi with
    | PosInf, _ => false
    | _, NegInf => false
    | _, _ => bound_leb lo hi
    end.
  Definition interval_meet (a b : itv) :=
    match a, b with
    | I l h, I l' h' =>
      let lo := bound_max l l' in
      let hi := bound_min h h' in
      if bounds_nonempty lo hi then I lo hi else IBot
    | _, _ => IBot
    end.
  Definition interval_finite (a : itv) : option (Z * Z) :=
    match a with
    | I (Fin lo) (Fin hi) => Some (lo, hi)
    | _ => None
    end.
  Definition interval_singleton a :=
    match interval_finite a with
    | Some (lo, hi) => if Z.eqb lo hi then Some lo else None
    | None => None
    end.
End IntervalBaseCode.
