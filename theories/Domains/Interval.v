(** * Interval lattice operations

    Intervals use integer bounds and threshold widening.
    For example, meeting disjoint finite intervals returns bottom.
    Builds on: IntervalSig and ThresholdsSig. *)

From Stdlib Require Import ZArith Bool List.
From Argent Require Import Std.
From Galois.Domains Require Import ValueSig IntervalSig ThresholdsSig.
Import List.ListNotations.
Local Open Scope Z_scope.

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

Module IntervalCode (L : Z_LANGUAGE_OPS) (T : THRESHOLDS_OPS) <: INTERVAL_OPS L T.
  Include IntervalBaseCode T.
  Definition t := itv.
  Definition wparam := ttree.
  Definition bot := IBot.
  Definition top := I NegInf PosInf.
  Definition leb := interval_leb.
  Definition is_bot a := match a with IBot => true | _ => false end.
  Definition join := interval_join.
  Definition meet := interval_meet.
  Definition widen ts a b := if leb b a then a else interval_widen ts a b.
  Definition narrow := interval_narrow.
  Definition point := interval_singleton.
  Definition abst z := I (Fin z) (Fin z).

  Definition add a b :=
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I la ha, I lb hb =>
      I (match la, lb with Fin x, Fin y => Fin (x + y) | _, _ => NegInf end)
        (match ha, hb with Fin x, Fin y => Fin (x + y) | _, _ => PosInf end)
    end%Z.
  Definition sub a b :=
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I la ha, I lb hb =>
      I (match la, hb with Fin x, Fin y => Fin (x - y) | _, _ => NegInf end)
        (match ha, lb with Fin x, Fin y => Fin (x - y) | _, _ => PosInf end)
    end%Z.
  Definition mul a b :=
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I (Fin la) (Fin ha), I (Fin lb) (Fin hb) =>
      let x := (la * lb)%Z in let y := (la * hb)%Z in
      let z := (ha * lb)%Z in let w := (ha * hb)%Z in
      I (Fin (Z.min (Z.min x y) (Z.min z w))) (Fin (Z.max (Z.max x y) (Z.max z w)))
    | _, _ => top
    end.
  Definition udiv a b :=
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I (Fin la) (Fin ha), I (Fin lb) (Fin hb) =>
      if (Z.leb 0 la && Z.ltb 0 lb)%bool then I (Fin (la / hb)) (Fin (ha / lb)) else top
    | _, _ => top
    end%Z.
  Definition urem a b :=
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I (Fin la) (Fin ha), I (Fin lb) (Fin hb) =>
      if (Z.leb 0 la && Z.ltb 0 lb)%bool then I (Fin 0) (Fin (Z.min ha (hb - 1))) else top
    | _, _ => top
    end%Z.
  Definition bitand a b :=
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I (Fin la) (Fin ha), I (Fin lb) (Fin hb) =>
      if (Z.leb 0 la && Z.leb 0 lb)%bool then I (Fin 0) (Fin (Z.min ha hb)) else top
    | _, _ => top
    end%Z.
  Definition bitor a b :=
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I (Fin la) (Fin ha), I (Fin lb) (Fin hb) =>
      if (Z.leb 0 la && Z.leb 0 lb)%bool then
        let h := Z.max ha hb in I (Fin 0) (Fin (Z.ones (Z.log2 h + 1)))
      else top
    | _, _ => top
    end%Z.
  Definition bnd_bits b := match b with Fin z => Z.size_nat z | _ => 0%nat end.
  Definition itv_bits a :=
    match a with IBot => 0%nat | I lo hi => Nat.max (bnd_bits lo) (bnd_bits hi) end.
  Definition shl a b :=
    let k := Z.of_nat (itv_bits a + itv_bits b + 1) in
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I (Fin la) ha, I (Fin lb) hb =>
      if (Z.leb 0 la && Z.leb 0 lb)%bool then
        match ha, hb with
        | Fin ha, Fin hb =>
          if Z.leb hb k then I (Fin (Z.shiftl la lb)) (Fin (Z.shiftl ha hb))
          else I (Fin la) PosInf
        | _, _ => I (Fin la) PosInf
        end
      else top
    | _, _ => top
    end.
  Definition truth (b : bool) := if b then abst 1 else abst 0.
  Definition cmp c a b :=
    match a, b with
    | IBot, _ | _, IBot => IBot
    | _, _ =>
      match point a, point b with
      | Some x, Some y => truth (match Z.compare x y, c with
                                  | Eq, Eq | Lt, Lt | Gt, Gt => true | _, _ => false end)
      | _, _ => I (Fin 0) (Fin 1)
      end
    end.
  Definition add_back r a b := (meet a (sub r b), meet b (sub r a)).
  Definition sub_back r a b := (meet a (add r b), meet b (sub a r)).
  Definition mul_preimage r x :=
    match point x with
    | Some z =>
      if Z.eqb z 1 then r
      else if Z.eqb z (-1) then sub (abst 0) r else top
    | None => top
    end.
  Definition mul_back r a b := (meet a (mul_preimage r b), meet b (mul_preimage r a)).
  Definition unsigned_back (a b : itv) :=
    (meet a (I (Fin 0) PosInf), meet b (I (Fin 1) PosInf)).
  Definition udiv_back (_ : itv) (a b : itv) := unsigned_back a b.
  Definition urem_back (_ : itv) (a b : itv) := unsigned_back a b.
  Definition ult_back r a b :=
    match point r, a, b with
    | Some z, I (Fin la) _, I _ (Fin hb) =>
      if Z.eqb z 1 then
        (meet a (I NegInf (Fin (hb - 1))), meet b (I (Fin (la + 1)) PosInf))%Z
      else (a, b)
    | _, _, _ => (a, b)
    end.
  Definition signed_split w a :=
    let modulus := Z.pow 2 (Zpos w) in
    let half := Z.pow 2 (Zpos w - 1) in
    let low := meet a (I (Fin 0) (Fin (half - 1))) in
    let high := meet a (I (Fin half) (Fin (modulus - 1))) in
    low :: sub high (abst modulus) :: nil.
  Definition forward o xs :=
    match L.view o, xs with
    | ZConst z, nil => abst z
    | ZAdd, a :: b :: nil => add a b
    | ZSub, a :: b :: nil => sub a b
    | ZMul, a :: b :: nil => mul a b
    | ZDiv, a :: b :: nil => udiv a b
    | ZRem, a :: b :: nil => urem a b
    | ZAnd, a :: b :: nil => bitand a b
    | ZOr, a :: b :: nil => bitor a b
    | ZShl, a :: b :: nil => shl a b
    | ZCmp c, a :: b :: nil => cmp c a b
    | _, _ => top
    end.
  Definition backward o r xs :=
    match L.view o, xs with
    | ZAdd, a :: b :: nil => let p := add_back r a b in fst p :: snd p :: nil
    | ZSub, a :: b :: nil => let p := sub_back r a b in fst p :: snd p :: nil
    | ZMul, a :: b :: nil => let p := mul_back r a b in fst p :: snd p :: nil
    | ZDiv, a :: b :: nil => let p := udiv_back r a b in fst p :: snd p :: nil
    | ZRem, a :: b :: nil => let p := urem_back r a b in fst p :: snd p :: nil
    | _, _ => xs
    end.
  Definition strict_back a b :=
    match a, b with
    | I la _, I _ hb =>
      let upper := match hb with Fin z => Fin (z - 1) | _ => hb end in
      let lower := match la with Fin z => Fin (z + 1) | _ => la end in
      (meet a (I NegInf upper), meet b (I lower PosInf))
    | _, _ => (IBot, IBot)
    end.
  Definition guard g xs :=
    match L.gview g, xs with
    | ZGuardUlt, a :: b :: nil =>
      let p := ult_back (abst 1) a b in fst p :: snd p :: nil
    | ZGuardCmp Eq, a :: b :: nil => meet a b :: meet b a :: nil
    | ZGuardCmp Lt, a :: b :: nil =>
      let p := strict_back a b in fst p :: snd p :: nil
    | ZGuardCmp Gt, a :: b :: nil =>
      let p := strict_back b a in snd p :: fst p :: nil
    | _, _ => xs
    end.
End IntervalCode.
