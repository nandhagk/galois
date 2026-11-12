(** * Known-bit masks

    Known-bit masks describe zeros and ones that hold across every represented word.
    For example, an eight-bit mask can record that the low nibble is zero.
    Builds on: KnownBitsSig, WordSig and the bit-vector operations. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Argent Require Import Time.
From Galois.Base Require Import Loop.
From Galois.Bits Require Import Word Op Fun Testbit Arith.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import WordSig KnownBitsSig.
Import List.ListNotations.


Local Open Scope Z_scope.

Definition tnum_normalise (w : width) (t : tnum) : tnum :=
  Tnum (wrap w (zeros t)) (wrap w (ones t)).

Definition tnum_join (w : width) (a b : tnum) : tnum :=
  Tnum (wand w (zeros a) (zeros b)) (wand w (ones a) (ones b)).

Definition tnum_meet (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (zeros a) (zeros b)) (wor w (ones a) (ones b)).

Definition tnum_subset (w : width) (a b : Z) : bool :=
  Z.eqb (wand w a b) (wrap w a).

Definition tnum_top : tnum := Tnum 0 0.

Definition tnum_const (w : width) (z : Z) : tnum := Tnum (wnot w z) (wrap w z).

Definition tnum_min (w : width) (a : tnum) : Z := wrap w (ones a).

Definition tnum_max (w : width) (a : tnum) : Z := wnot w (zeros a).

Definition tnum_mask (w : width) (a : tnum) : Z := wnot w (wor w (zeros a) (ones a)).

Definition tnum_constant (w : width) (a : tnum) : option Z :=
  if wrap w (zeros a) =? wnot w (ones a) then Some (tnum_min w a) else None.

Definition tnum_empty (w : width) (a : tnum) : bool :=
  negb (Z.eqb (wand w (zeros a) (ones a)) 0).

Definition tnum_not (w : width) (a : tnum) : tnum :=
  Tnum (wrap w (ones a)) (wrap w (zeros a)).

Definition tnum_and (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (zeros a) (zeros b)) (wand w (ones a) (ones b)).

Definition tnum_or (w : width) (a b : tnum) : tnum :=
  Tnum (wand w (zeros a) (zeros b)) (wor w (ones a) (ones b)).

Definition tnum_xor (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (wand w (zeros a) (zeros b)) (wand w (ones a) (ones b)))
    (wor w (wand w (zeros a) (ones b)) (wand w (ones a) (zeros b))).

Definition tnum_adc_uncertain (w : width) (a b : tnum) (initial : bool) : Z :=
  Z.lor (Z.lxor (tnum_min w a + tnum_min w b + Z.b2z initial)
      (tnum_max w a + tnum_max w b + Z.b2z initial))
    (Z.lor (tnum_mask w a) (tnum_mask w b)).

Definition tnum_adc (w : width) (a b : tnum) (initial : bool) : tnum :=
  let v := tnum_min w a + tnum_min w b + Z.b2z initial in
  let m := tnum_adc_uncertain w a b initial in
  Tnum (wrap w (Z.lnot (Z.lor v m))) (wrap w (Z.land v (Z.lnot m))).

Definition tnum_add (w : width) (a b : tnum) : tnum := tnum_adc w a b false.

Definition tnum_sub (w : width) (a b : tnum) : tnum := tnum_adc w a (tnum_not w b) true.

Definition tnum_neg (w : width) (a : tnum) : tnum := tnum_sub w (tnum_const w 0) a.

Definition tnum_bitlen (h : Z) : Z := if h =? 0 then 0 else Z.succ (Z.log2 h).

Definition tnum_upper (w : width) (h : Z) : tnum :=
  Tnum (wnot w (Z.ones (tnum_bitlen h))) 0.

Definition tnum_udiv (w : width) (a b : tnum) : tnum :=
  if wrap w (ones b) =? 0 then tnum_top else tnum_upper w (tnum_max w a).

Definition tnum_urem (w : width) (a : tnum) : tnum := tnum_upper w (tnum_max w a).

Definition tnum_linux_add (w : width) (a b : tnum) : tnum :=
  let v := tnum_min w a + tnum_min w b in
  let m := Z.lor (Z.lxor (v + (tnum_mask w a + tnum_mask w b)) v)
    (Z.lor (tnum_mask w a) (tnum_mask w b)) in
  Tnum (wrap w (Z.lnot (Z.lor v m))) (wrap w (Z.land v (Z.lnot m))).

Definition tnum_trailing (w : width) (a : tnum) : Z := wctz w (wnot w (zeros a)).

Definition tnum_mul_low (w : width) (a b : tnum) : tnum :=
  Tnum (wrap w (Z.ones (tnum_trailing w a + tnum_trailing w b))) 0.

Definition tnum_mul (w : width) (a b : tnum) : tnum :=
  match tnum_constant w a, tnum_constant w b with
  | Some x, Some y => tnum_const w (wmul w x y)
  | _, _ => tnum_mul_low w a b
  end.

Definition tnum_map (sw rw : width) (f : Z -> Z) (a : tnum) : tnum :=
  Tnum (wnot rw (f (tnum_max sw a))) (wrap rw (f (tnum_min sw a))).

Definition tnum_shl_scalar_value (w : width) (k x : Z) : Z :=
  wshl w x (Z.min k (Zpos w)).

Definition tnum_shl_scalar (w : width) (k : Z) (a : tnum) : tnum :=
  tnum_map w w (tnum_shl_scalar_value w k) a.

Definition tnum_uncertain (w : width) (m : Z) : tnum := Tnum (wnot w m) 0.

Definition tnum_mul_acc_done (w : width) (b : tnum) (i : Z) : bool :=
  (Z.shiftr (tnum_min w b) i =? 0) && (Z.shiftr (tnum_mask w b) i =? 0).

Definition tnum_scalar_value (o : op) (w : width) (k x : Z) : Z :=
  match o with
  | bvshl => wshl w x (Z.min k (Zpos w))
  | bvlshr => wlshr w x (Z.min k (Zpos w))
  | bvashr => washr w x (Z.min k (Zpos w))
  | bvrotl => wrotl w x (k mod Zpos w)
  | bvrotr => wrotl w x ((-k) mod Zpos w)
  | _ => wrap w x
  end.

Definition tnum_scalar (o : op) (w : width) (k : Z) (a : tnum) : tnum :=
  tnum_map w w (tnum_scalar_value o w k) a.

Definition tnum_concat (w v : width) (a b : tnum) : tnum :=
  Tnum (wrap (w + v)%positive (wrap w (zeros a) * modulus v + wrap v (zeros b)))
    (wrap (w + v)%positive (wrap w (ones a) * modulus v + wrap v (ones b))).

Definition tnum_rotation (o : op) : bool :=
  match o with
  | bvrotl | bvrotr => true
  | _ => false
  end.

Definition tnum_stride (o : op) (w : width) (d : Z) : Z :=
  if tnum_rotation o then (2 * d) mod Zpos w else 2 * d.

Definition tnum_bot (w : width) : tnum := Tnum (modulus w - 1) (modulus w - 1).

Definition tnum_mul_stage_step (w : width) (a b : tnum) (s : Z * tnum)
    : (Z * tnum) + tnum :=
  let '(i, r) := s in
  inl (Z.succ i,
    if Z.testbit (zeros b) i then r
    else let sum := tnum_add w r (tnum_shl_scalar w i a) in
      if Z.testbit (ones b) i then sum else tnum_join w r sum).

Definition tnum_mul_stages (w : width) (a b : tnum) : tnum :=
  if tnum_empty w a || tnum_empty w b then tnum_bot w else
  match loopN (tnum_mul_stage_step w a b) (N.pos w) (0, tnum_const w 0) with
  | inl s => snd s
  | inr r => r
  end.

Definition tnum_mul_acc_step (w : width) (a b : tnum) (s : Z * tnum)
    : (Z * tnum) + tnum :=
  let '(i, r) := s in
  if tnum_mul_acc_done w b i then inr r else
  inl (i + 1,
    if Z.testbit (zeros b) i then r else
    let m := if Z.testbit (ones b) i then tnum_mask w a
      else wor w (tnum_min w a) (tnum_mask w a) in
    tnum_add w r (tnum_shl_scalar w i (tnum_uncertain w m))).

Definition tnum_mul_acc (w : width) (a b : tnum) : tnum :=
  if tnum_empty w a || tnum_empty w b then tnum_bot w else
  let value_acc := tnum_const w (wmul w (tnum_min w a) (tnum_min w b)) in
  let mask_acc :=
    match loopN (tnum_mul_acc_step w a b) (N.pos w) (0, tnum_const w 0) with
    | inl s => snd s
    | inr r => r
    end in
  tnum_add w value_acc mask_acc.

Definition tnum_mul_with (choice : mulchoice) (w : width) (a b : tnum) : tnum :=
  match choice with
  | MulLow => tnum_mul w a b
  | MulStages => tnum_mul_stages w a b
  | MulAcc => tnum_mul_acc w a b
  | MulBoth => tnum_meet w (tnum_mul_stages w a b) (tnum_mul_acc w a b)
  end.

Fixpoint tnum_expand (o : op) (w : width) (p : positive) (d : Z) (r : tnum) : tnum :=
  match p with
  | xH => tnum_join w r (tnum_scalar o w d r)
  | xO q => tnum_expand o w q (tnum_stride o w d) r
  | xI q => tnum_expand o w q (tnum_stride o w d)
      (tnum_join w r (tnum_scalar o w d r))
  end.

Definition tnum_expand_mask (o : op) (w : width) (u : Z) (r : tnum) : tnum :=
  match u with
  | Zpos p => tnum_expand o w p 1 r
  | _ => tnum_normalise w r
  end.

Definition tnum_shift_cutoff (w : width) : Z := tnum_bitlen (Zpos w - 1).

Definition tnum_variable_raw (o : op) (w : width) (a b : tnum) : tnum :=
  let base := tnum_min w b in
  let u := tnum_mask w b in
  let r := tnum_scalar o w base a in
  if tnum_rotation o then tnum_expand_mask o w u r else
  let cutoff := 2 ^ tnum_shift_cutoff w in
  let low := tnum_expand_mask o w (u mod cutoff) r in
  if u <? cutoff then low else tnum_join w low (tnum_scalar o w (Zpos w) a).

Definition tnum_variable (o : op) (w : width) (a b : tnum) : tnum :=
  if tnum_empty w a || tnum_empty w b then tnum_bot w
  else tnum_variable_raw o w a b.

Module KnownBitsCode (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG) <: KNOWN_BITS_OPS L C.
  Definition p := tnum.
  Definition pleb w a b := tnum_subset w (zeros b) (zeros a) &&
    tnum_subset w (ones b) (ones a).
  Definition pjoin := tnum_join.
  Definition pmeet := tnum_meet.
  Definition pbot := tnum_bot.
  Definition ptop (_ : positive) := tnum_top.
  Definition pis_bot := tnum_empty.
  Definition pconst := tnum_const.
  Definition ppoint := tnum_constant.
  Definition pwparam := unit.
  Definition pwiden (_ : unit) := pjoin.
  Definition pnarrow (_ : positive) (a _ : p) := a.
  Definition tnum_normalise := tnum_normalise.
  Definition tnum_not := tnum_not.
  Definition tnum_neg := tnum_neg.
  Definition tnum_add := tnum_add.
  Definition tnum_sub := tnum_sub.
  Definition tnum_and := tnum_and.
  Definition tnum_or := tnum_or.
  Definition tnum_xor := tnum_xor.
  Definition tnum_mul_with := tnum_mul_with.
  Definition tnum_mul := tnum_mul_with C.multiplier.
  Definition tnum_variable := tnum_variable.
End KnownBitsCode.
Definition tnum_shift (o : op) (w : width) (a : tnum) (k : Z) : tnum :=
  match word_fun2 o with
  | Some f => tnum_map w w (fun x => eval_binary_tag f w x k) a
  | None => tnum_top
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

Definition tnum_order (strict : bool) (w : width) (a b : tnum) : tnum :=
  if (if strict then tnum_max w a <? tnum_min w b
      else tnum_max w a <=? tnum_min w b) then tnum_const 1%positive 1
  else if (if strict then tnum_max w b <=? tnum_min w a
           else tnum_max w b <? tnum_min w a) then tnum_const 1%positive 0
  else tnum_top.

Definition tnum_equal (w : width) (a b : tnum) : tnum :=
  if tnum_empty w (tnum_meet w a b) then tnum_const 1%positive 0 else
  match tnum_constant w a, tnum_constant w b with
  | Some x, Some y => tnum_const 1%positive (if x =? y then 1 else 0)
  | _, _ => tnum_top
  end.

Definition tnum_bias (w : width) (a : tnum) : tnum :=
  tnum_xor w a (tnum_const w (half w)).

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

Definition tnum_count (w : width) : tnum := tnum_upper w (Zpos w).

Definition tnum_srem (w : width) (a : tnum) : tnum :=
  Tnum (wand w (zeros a) (half w)) 0.

Definition tnum_ite (w : width) (c a b : tnum) : tnum :=
  match tnum_constant 1%positive c with
  | Some k => tnum_normalise w (if k =? 1 then a else b)
  | None => tnum_join w a b
  end.

Definition tnum_leb (w : width) (a b : tnum) : bool :=
  tnum_subset w (zeros b) (zeros a) && tnum_subset w (ones b) (ones a).

Definition tnum_gamma (w : width) (a : tnum) (z : Z) : Prop :=
  Z.land z (wrap w (zeros a)) = 0 /\ Z.land (wrap w (ones a)) (Z.lnot z) = 0.

Definition tnum_mul_stage_count (w : width) (a b : tnum) : Z :=
  if tnum_empty w a || tnum_empty w b then 0 else
  match loopN (tnum_mul_stage_step w a b) (N.pos w) (0, tnum_const w 0) with
  | inl s => fst s
  | inr _ => 0
  end.
