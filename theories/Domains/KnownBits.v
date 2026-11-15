(** * Known-bit masks

    Known-bit masks describe zeros and ones that hold across every represented word.
    For example, an eight-bit mask can record that the low nibble is zero.
    Builds on: KnownBitsSig, WordSig and the bit-vector operations. *)

From Stdlib Require Import ZArith NArith Zpow_facts List Bool Lia.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Loop.
From Galois.Bits Require Import Word Op Fun Testbit Arith.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import WordSig KnownBitsSig BitsLang.
Import List.ListNotations.


Local Open Scope Z_scope.

Module Z.
  TimeFun Z.b2z.
  TimeFun Z.lnot.
End Z.

Definition tnum_wand (w : width) (x y : Z) : Z := tnum_wrap w (Z.land x y).
TimeFun tnum_wand.

Definition tnum_wor (w : width) (x y : Z) : Z := tnum_wrap w (Z.lor x y).
TimeFun tnum_wor.

Definition tnum_wnot (w : width) (x : Z) : Z := tnum_wrap w (Z.lnot x).
TimeFun tnum_wnot.

(** Masking an integer agrees with reduction modulo the word modulus. *)
Lemma tnum_wrap_agrees : forall w z, tnum_wrap w z = wrap w z.
Proof.
  intros w z. unfold tnum_wrap, wrap, modulus.
  apply Z.land_ones. lia.
Qed.

(** Masked conjunction agrees with the concrete word operation. *)
Lemma tnum_wand_agrees : forall w x y, tnum_wand w x y = wand w x y.
Proof.
  intros w x y. unfold tnum_wand, wand.
  rewrite tnum_wrap_agrees. apply Z.bits_inj'. intros i Hi.
  rewrite !testbit_wrap, !Z.land_spec, !testbit_wrap by exact Hi.
  destruct (i <? Zpos w); reflexivity.
Qed.

(** Masked disjunction agrees with the concrete word operation. *)
Lemma tnum_wor_agrees : forall w x y, tnum_wor w x y = wor w x y.
Proof.
  intros w x y. unfold tnum_wor, wor.
  rewrite tnum_wrap_agrees. apply Z.bits_inj'. intros i Hi.
  rewrite !testbit_wrap, !Z.lor_spec, !testbit_wrap by exact Hi.
  destruct (i <? Zpos w); reflexivity.
Qed.

(** Masked complement agrees with the concrete word operation. *)
Lemma tnum_wnot_agrees : forall w x, tnum_wnot w x = wnot w x.
Proof.
  intros w x. unfold tnum_wnot.
  rewrite tnum_wrap_agrees. apply Z.bits_inj'. intros i Hi.
  rewrite testbit_wrap, Z.lnot_spec, testbit_wnot_full by exact Hi.
  destruct (i <? Zpos w), (Z.testbit x i); reflexivity.
Qed.

Definition tnum_normalise (w : width) (t : tnum) : tnum :=
  Tnum (tnum_wrap w (zeros t)) (tnum_wrap w (ones t)).
TimeFun tnum_normalise.

Definition tnum_join (w : width) (a b : tnum) : tnum :=
  Tnum (tnum_wand w (zeros a) (zeros b)) (tnum_wand w (ones a) (ones b)).
TimeFun tnum_join.

Definition tnum_meet (w : width) (a b : tnum) : tnum :=
  Tnum (tnum_wor w (zeros a) (zeros b)) (tnum_wor w (ones a) (ones b)).
TimeFun tnum_meet.

Definition tnum_subset (w : width) (a b : Z) : bool :=
  Z.eqb (tnum_wand w a b) (tnum_wrap w a).
TimeFun tnum_subset.

Definition tnum_top : tnum := Tnum 0 0.
TimeFun tnum_top.

Definition tnum_const (w : width) (z : Z) : tnum := Tnum (tnum_wnot w z) (tnum_wrap w z).
TimeFun tnum_const.

Definition tnum_min (w : width) (a : tnum) : Z := tnum_wrap w (ones a).
TimeFun tnum_min.

Definition tnum_max (w : width) (a : tnum) : Z := tnum_wnot w (zeros a).
TimeFun tnum_max.

Definition tnum_mask (w : width) (a : tnum) : Z := tnum_wnot w (tnum_wor w (zeros a) (ones a)).
TimeFun tnum_mask.

(** The minimum endpoint lies within its word width. *)
Lemma tnum_min_word : forall w a, is_word w (tnum_min w a).
Proof.
  intros w a. unfold tnum_min. rewrite tnum_wrap_agrees. apply wrap_is_word.
Qed.

(** The maximum endpoint lies within its word width. *)
Lemma tnum_max_word : forall w a, is_word w (tnum_max w a).
Proof.
  intros w a. unfold tnum_max. rewrite tnum_wnot_agrees. apply wnot_is_word.
Qed.

(** The uncertainty mask lies within its word width. *)
Lemma tnum_mask_word : forall w a, is_word w (tnum_mask w a).
Proof.
  intros w a. unfold tnum_mask. rewrite tnum_wnot_agrees. apply wnot_is_word.
Qed.

Definition tnum_constant (w : width) (a : tnum) : option Z :=
  if tnum_wrap w (zeros a) =? tnum_wnot w (ones a) then Some (tnum_min w a) else None.
TimeFun tnum_constant.

Definition tnum_empty (w : width) (a : tnum) : bool :=
  negb (Z.eqb (tnum_wand w (zeros a) (ones a)) 0).
TimeFun tnum_empty.

Definition tnum_not (w : width) (a : tnum) : tnum :=
  Tnum (tnum_wrap w (ones a)) (tnum_wrap w (zeros a)).
TimeFun tnum_not.

Definition tnum_and (w : width) (a b : tnum) : tnum :=
  Tnum (tnum_wor w (zeros a) (zeros b)) (tnum_wand w (ones a) (ones b)).
TimeFun tnum_and.

Definition tnum_or (w : width) (a b : tnum) : tnum :=
  Tnum (tnum_wand w (zeros a) (zeros b)) (tnum_wor w (ones a) (ones b)).
TimeFun tnum_or.

Definition tnum_xor (w : width) (a b : tnum) : tnum :=
  Tnum (tnum_wor w (tnum_wand w (zeros a) (zeros b)) (tnum_wand w (ones a) (ones b)))
    (tnum_wor w (tnum_wand w (zeros a) (ones b)) (tnum_wand w (ones a) (zeros b))).
TimeFun tnum_xor.

Definition tnum_adc_uncertain (w : width) (a b : tnum) (initial : bool) : Z :=
  Z.lor (Z.lxor (tnum_min w a + tnum_min w b + Z.b2z initial)
      (tnum_max w a + tnum_max w b + Z.b2z initial))
    (Z.lor (tnum_mask w a) (tnum_mask w b)).
TimeFun tnum_adc_uncertain.

Definition tnum_adc (w : width) (a b : tnum) (initial : bool) : tnum :=
  let v := tnum_min w a + tnum_min w b + Z.b2z initial in
  let m := tnum_adc_uncertain w a b initial in
  Tnum (tnum_wrap w (Z.lnot (Z.lor v m))) (tnum_wrap w (Z.land v (Z.lnot m))).
TimeFun tnum_adc.

Definition tnum_add (w : width) (a b : tnum) : tnum := tnum_adc w a b false.
TimeFun tnum_add.

Definition tnum_sub (w : width) (a b : tnum) : tnum := tnum_adc w a (tnum_not w b) true.
TimeFun tnum_sub.

Definition tnum_neg (w : width) (a : tnum) : tnum := tnum_sub w (tnum_const w 0) a.
TimeFun tnum_neg.

Definition tnum_bitlen (h : Z) : Z := if h =? 0 then 0 else Z.succ (Z.log2 h).
TimeFun tnum_bitlen.

Definition tnum_upper (w : width) (h : Z) : tnum :=
  Tnum (tnum_wnot w (Z.ones (tnum_bitlen h))) 0.
TimeFun tnum_upper.

Definition tnum_udiv (w : width) (a b : tnum) : tnum :=
  if tnum_wrap w (ones b) =? 0 then tnum_top else tnum_upper w (tnum_max w a).
TimeFun tnum_udiv.

Definition tnum_urem (w : width) (a : tnum) : tnum := tnum_upper w (tnum_max w a).
TimeFun tnum_urem.

Definition tnum_linux_add (w : width) (a b : tnum) : tnum :=
  let v := tnum_min w a + tnum_min w b in
  let m := Z.lor (Z.lxor (v + (tnum_mask w a + tnum_mask w b)) v)
    (Z.lor (tnum_mask w a) (tnum_mask w b)) in
  Tnum (tnum_wrap w (Z.lnot (Z.lor v m))) (tnum_wrap w (Z.land v (Z.lnot m))).

Definition tnum_trailing (w : width) (a : tnum) : Z := wctz w (tnum_wnot w (zeros a)).
TimeFun tnum_trailing.

Definition tnum_mul_low (w : width) (a b : tnum) : tnum :=
  Tnum (tnum_wrap w (Z.ones (tnum_trailing w a + tnum_trailing w b))) 0.
TimeFun tnum_mul_low.

Definition tnum_mul (w : width) (a b : tnum) : tnum :=
  match tnum_constant w a, tnum_constant w b with
  | Some x, Some y => tnum_const w (wmul w x y)
  | _, _ => tnum_mul_low w a b
  end.
TimeFun tnum_mul.

Definition tnum_map (sw rw : width) (f : Z -> Z) (a : tnum) : tnum :=
  Tnum (tnum_wnot rw (f (tnum_max sw a))) (tnum_wrap rw (f (tnum_min sw a))).
TimeFun tnum_map.

Definition tnum_shl_value (w : width) (k x : Z) : Z :=
  if Zpos w <=? k then 0 else tnum_wrap w (Z.shiftl x k).
TimeFun tnum_shl_value.

Definition tnum_lshr_value (w : width) (k x : Z) : Z :=
  if Zpos w <=? k then 0 else Z.shiftr (tnum_wrap w x) k.
TimeFun tnum_lshr_value.

Definition tnum_ashr_value (w : width) (k x : Z) : Z :=
  let x' := tnum_wrap w x in
  let k' := Z.min k (Zpos w - 1) in
  if Z.testbit x' (Zpos w - 1)
  then Z.lor (Z.shiftr x' k') (tnum_wrap w (Z.lnot (Z.ones (Zpos w - k'))))
  else Z.shiftr x' k'.
TimeFun tnum_ashr_value.

Definition tnum_rotl_value (w : width) (k x : Z) : Z :=
  let x' := tnum_wrap w x in
  tnum_wrap w (Z.lor (Z.shiftl x' k) (Z.shiftr x' (Zpos w - k))).
TimeFun tnum_rotl_value.

Definition tnum_shl_scalar_value (w : width) (k x : Z) : Z :=
  tnum_shl_value w (Z.min k (Zpos w)) x.
TimeFun tnum_shl_scalar_value.

Definition tnum_shl_scalar (w : width) (k : Z) (a : tnum) : tnum :=
  tnum_map w w (tnum_shl_scalar_value w k) a.
TimeFun tnum_shl_scalar.

Definition tnum_uncertain (w : width) (m : Z) : tnum := Tnum (tnum_wnot w m) 0.
TimeFun tnum_uncertain.

Definition tnum_mul_acc_done (w : width) (b : tnum) (i : Z) : bool :=
  (Z.shiftr (tnum_min w b) i =? 0) && (Z.shiftr (tnum_mask w b) i =? 0).
TimeFun tnum_mul_acc_done.

Definition tnum_scalar_value (o : op) (w : width) (k x : Z) : Z :=
  match o with
  | bvshl => tnum_shl_value w (Z.min (Z.max 0 k) (Zpos w)) x
  | bvlshr => tnum_lshr_value w (Z.min (Z.max 0 k) (Zpos w)) x
  | bvashr => tnum_ashr_value w (Z.min (Z.max 0 k) (Zpos w)) x
  | bvrotl => tnum_rotl_value w (k mod Zpos w) x
  | bvrotr => tnum_rotl_value w ((-k) mod Zpos w) x
  | _ => tnum_wrap w x
  end.
TimeFun tnum_scalar_value.

Definition tnum_scalar (o : op) (w : width) (k : Z) (a : tnum) : tnum :=
  tnum_map w w (tnum_scalar_value o w k) a.
TimeFun tnum_scalar.

Definition tnum_concat (w v : width) (a b : tnum) : tnum :=
  Tnum (tnum_wrap (w + v)%positive (tnum_wrap w (zeros a) * modulus v + tnum_wrap v (zeros b)))
    (tnum_wrap (w + v)%positive (tnum_wrap w (ones a) * modulus v + tnum_wrap v (ones b))).
TimeFun tnum_concat.

Definition tnum_rotation (o : op) : bool :=
  match o with
  | bvrotl | bvrotr => true
  | _ => false
  end.
TimeFun tnum_rotation.

Definition tnum_stride (o : op) (w : width) (d : Z) : Z :=
  if tnum_rotation o then (2 * d) mod Zpos w else 2 * d.
TimeFun tnum_stride.

Definition tnum_bot (w : width) : tnum := Tnum (modulus w - 1) (modulus w - 1).
TimeFun tnum_bot.

Definition tnum_mul_stage_step (w : width) (a b : tnum) (s : Z * tnum)
    : (Z * tnum) + tnum :=
  let '(i, r) := s in
  inl (Z.succ i,
    if Z.testbit (zeros b) i then r
    else let sum := tnum_add w r (tnum_shl_scalar w i a) in
      if Z.testbit (ones b) i then sum else tnum_join w r sum).
TimeFun tnum_mul_stage_step.

Definition tnum_mul_stages (w : width) (a b : tnum) : tnum :=
  let a := tnum_normalise w a in
  let b := tnum_normalise w b in
  if tnum_empty w a || tnum_empty w b then tnum_bot w else
  match loopN (tnum_mul_stage_step w a b) (N.pos w) (0, tnum_const w 0) with
  | inl s => snd s
  | inr r => r
  end.
TimeFun tnum_mul_stages.

Definition tnum_mul_acc_step (w : width) (a b : tnum) (s : Z * tnum)
    : (Z * tnum) + tnum :=
  let '(i, r) := s in
  if tnum_mul_acc_done w b i then inr r else
  inl (i + 1,
    if Z.testbit (zeros b) i then r else
    let m := if Z.testbit (ones b) i then tnum_mask w a
      else tnum_wor w (tnum_min w a) (tnum_mask w a) in
    tnum_add w r (tnum_shl_scalar w i (tnum_uncertain w m))).
TimeFun tnum_mul_acc_step.

Definition tnum_mul_acc (w : width) (a b : tnum) : tnum :=
  let a := tnum_normalise w a in
  let b := tnum_normalise w b in
  if tnum_empty w a || tnum_empty w b then tnum_bot w else
  let value_acc := tnum_const w (wmul w (tnum_min w a) (tnum_min w b)) in
  let mask_acc :=
    match loopN (tnum_mul_acc_step w a b) (N.pos w) (0, tnum_const w 0) with
    | inl s => snd s
    | inr r => r
    end in
  tnum_add w value_acc mask_acc.
TimeFun tnum_mul_acc.

Definition tnum_mul_with (choice : mulchoice) (w : width) (a b : tnum) : tnum :=
  match choice with
  | MulLow => tnum_mul w a b
  | MulStages => tnum_mul_stages w a b
  | MulAcc => tnum_mul_acc w a b
  | MulBoth => tnum_meet w (tnum_mul_stages w a b) (tnum_mul_acc w a b)
  end.
TimeFun tnum_mul_with.

Fixpoint tnum_expand (o : op) (w : width) (p : positive) (d : Z) (r : tnum) : tnum :=
  match p with
  | xH => tnum_join w r (tnum_scalar o w d r)
  | xO q => tnum_expand o w q (tnum_stride o w d) r
  | xI q => tnum_expand o w q (tnum_stride o w d)
      (tnum_join w r (tnum_scalar o w d r))
  end.
TimeFun tnum_expand.

Definition tnum_expand_mask (o : op) (w : width) (u : Z) (r : tnum) : tnum :=
  match u with
  | Zpos p => tnum_expand o w p 1 r
  | _ => tnum_normalise w r
  end.
TimeFun tnum_expand_mask.

Definition tnum_shift_cutoff (w : width) : Z := tnum_bitlen (Zpos w - 1).
TimeFun tnum_shift_cutoff.

Definition tnum_variable_raw (o : op) (w : width) (a b : tnum) : tnum :=
  let base := tnum_min w b in
  let u := tnum_mask w b in
  let r := tnum_scalar o w base a in
  if tnum_rotation o then tnum_expand_mask o w u r else
  let cutoff := 2 ^ tnum_shift_cutoff w in
  let low := tnum_expand_mask o w (u mod cutoff) r in
  if u <? cutoff then low else tnum_join w low (tnum_scalar o w (Zpos w) a).
TimeFun tnum_variable_raw.

Definition tnum_variable (o : op) (w : width) (a b : tnum) : tnum :=
  let a := tnum_normalise w a in
  let b := tnum_normalise w b in
  if tnum_empty w a || tnum_empty w b then tnum_bot w
  else tnum_variable_raw o w a b.
TimeFun tnum_variable.

(** A finite sequence records the pure counterpart of the landed charged driver. *)
Inductive tnum_runs {S R : Type} (step : S -> S + R) : nat -> S -> S + R -> Prop :=
  | tnum_runs_zero s : tnum_runs step O s (inl s)
  | tnum_runs_stop n s r : step s = inr r -> tnum_runs step (Datatypes.S n) s (inr r)
  | tnum_runs_next n s s' result : step s = inl s' -> tnum_runs step n s' result ->
      tnum_runs step (Datatypes.S n) s result.

(** The binary-fuel driver has the same finite-step trace for every accessibility proof. *)
Local Lemma tnum_loop_runs_acc {S R : Type} (step : S -> S + R) :
  forall fs (H : Acc loopN_lt fs),
    tnum_runs step (N.to_nat (fst fs)) (snd fs)
      (loop loopN_lt (loopN_step step) fs H).
Proof.
  intros fs H. induction H as [[fuel s] Hacc IH] using Acc_ind_dep.
  cbn [fst snd]. destruct fuel as [|p].
  - cbn [loop loopN_step]. constructor.
  - assert (Hfuel : N.to_nat (N.pos p) =
      Datatypes.S (N.to_nat (N.pred (N.pos p)))).
    { rewrite <- N2Nat.inj_succ, N.succ_pred by discriminate. reflexivity. }
    rewrite Hfuel at 1. cbn [loop loopN_step Acc_inv].
    destruct (step s) as [next|r] eqn:Hstep.
    + eapply tnum_runs_next; [exact Hstep|].
      apply (IH (N.pred (N.pos p), next)).
    + apply tnum_runs_stop. exact Hstep.
Qed.

(** A pure binary-fuel execution supplies a trace for the multiplication invariants. *)
Lemma tnum_loop_runs : forall S R (step : S -> S + R) fuel s,
  tnum_runs step (N.to_nat fuel) s (loopN step fuel s).
Proof.
  intros S R step fuel s. unfold loopN.
  apply (tnum_loop_runs_acc step (fuel, s)).
Qed.

Module KnownBitsCode (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG) <: KNOWN_BITS_OPS L C.
  Definition p := tnum.
  Definition pleb w a b := tnum_empty w a ||
    (tnum_subset w (zeros b) (zeros a) &&
    tnum_subset w (ones b) (ones a)).
  Definition pjoin := tnum_join.
  Definition pmeet := tnum_meet.
  Definition pbot := tnum_bot.
  Definition ptop (_ : positive) := tnum_top.
  Definition pis_bot := tnum_empty.
  Definition pconst := tnum_const.
  Definition ppoint := tnum_constant.
  Definition pwparam := unit.
  Definition pwiden (_ : unit) w a b := if pleb w b a then a else pjoin w a b.
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
TimeFun tnum_shift.

Definition tnum_source (o : op) (w : width) (k i : Z) : option Z :=
  match o with
  | bvshl => if k <=? i then Some (i - k) else None
  | bvlshr => if i + k <? Zpos w then Some (i + k) else None
  | bvashr => Some (Z.min (i + k) (Zpos w - 1))
  | bvrotl => Some ((i - k) mod Zpos w)
  | bvrotr => Some ((i + k) mod Zpos w)
  | _ => Some i
  end.
TimeFun tnum_source.

Definition tnum_order (strict : bool) (w : width) (a b : tnum) : tnum :=
  if (if strict then tnum_max w a <? tnum_min w b
      else tnum_max w a <=? tnum_min w b) then tnum_const 1%positive 1
  else if (if strict then tnum_max w b <=? tnum_min w a
           else tnum_max w b <? tnum_min w a) then tnum_const 1%positive 0
  else tnum_top.
TimeFun tnum_order.

Definition tnum_equal (w : width) (a b : tnum) : tnum :=
  if tnum_empty w (tnum_meet w a b) then tnum_const 1%positive 0 else
  match tnum_constant w a, tnum_constant w b with
  | Some x, Some y => tnum_const 1%positive (if x =? y then 1 else 0)
  | _, _ => tnum_top
  end.
TimeFun tnum_equal.

Definition tnum_bias (w : width) (a : tnum) : tnum :=
  tnum_xor w a (tnum_const w (half w)).
TimeFun tnum_bias.

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
TimeFun tnum_compare.

Definition tnum_count (w : width) : tnum := tnum_upper w (Zpos w).
TimeFun tnum_count.

Definition tnum_srem (w : width) (a : tnum) : tnum :=
  Tnum (tnum_wand w (zeros a) (half w)) 0.
TimeFun tnum_srem.

Definition tnum_ite (w : width) (c a b : tnum) : tnum :=
  match tnum_constant 1%positive c with
  | Some k => tnum_normalise w (if k =? 1 then a else b)
  | None => tnum_join w a b
  end.
TimeFun tnum_ite.

Definition tnum_leb (w : width) (a b : tnum) : bool :=
  tnum_subset w (zeros b) (zeros a) && tnum_subset w (ones b) (ones a).
TimeFun tnum_leb.

Definition tnum_gamma (w : width) (a : tnum) (z : Z) : Prop :=
  Z.land z (wrap w (zeros a)) = 0 /\ Z.land (wrap w (ones a)) (Z.lnot z) = 0.

Definition tnum_mul_stage_count (w : width) (a b : tnum) : Z :=
  if tnum_empty w a || tnum_empty w b then 0 else
  match loopN (tnum_mul_stage_step w a b) (N.pos w) (0, tnum_const w 0) with
  | inl s => fst s
  | inr _ => 0
  end.

Definition tnum_equiv (w : width) (a b : tnum) : Prop :=
  wrap w (zeros a) = wrap w (zeros b) /\ wrap w (ones a) = wrap w (ones b).

Definition tnum_mul_residual (w : width) (a b : tnum) (x y i : Z) : Z :=
  x * (y mod 2 ^ i) - tnum_min w a * (tnum_min w b mod 2 ^ i).

Definition tnum_bit_copy (sw rw : width) (f : Z -> Z) : Prop :=
  forall i, 0 <= i < Zpos rw ->
    (forall x, is_word sw x -> Z.testbit (f x) i = false) \/
    exists j, 0 <= j < Zpos sw /\
      forall x, is_word sw x -> Z.testbit (f x) i = Z.testbit x j.

Definition tnum_shift_op (o : op) : Prop :=
  o = bvshl \/ o = bvlshr \/ o = bvashr \/ o = bvrotl \/ o = bvrotr.

Fixpoint tnum_choices (p : positive) (c : Z) : Prop :=
  match p with
  | xH => c = 0 \/ c = 1
  | xO q => exists t, tnum_choices q t /\ c = 2 * t
  | xI q => exists t, tnum_choices q t /\ (c = 2 * t \/ c = 2 * t + 1)
  end.

Definition tnum_unknown (w : width) (m : Z) : nat :=
  length (filter (fun i => negb (Z.testbit m (Z.of_nat i))) (seq 0 (Pos.to_nat w))).

Definition tnum_rank (w : width) (a : tnum) : nat :=
  (tnum_unknown w (zeros a) + tnum_unknown w (ones a))%nat.

Fixpoint tnum_unknown_from (n i : nat) (m : Z) : nat :=
  match n with
  | O => O
  | S n => let rest := tnum_unknown_from n (S i) m in
    if Z.testbit m (Z.of_nat i) then rest else S rest
  end.

Theorem tnum_wrap_bit : forall w m i, 0 <= i < Zpos w ->
  Z.testbit (wrap w m) i = Z.testbit m i.
Proof.
  intros w m i [Hi Hiw]. rewrite testbit_wrap by exact Hi.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) Hiw).
Qed.

Theorem tnum_and_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wand w a b) i = (Z.testbit a i && Z.testbit b i).
Proof.
  intros w a b i Hi. rewrite testbit_wand_full by lia.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

Theorem tnum_or_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wor w a b) i = (Z.testbit a i || Z.testbit b i).
Proof.
  intros w a b i Hi. rewrite testbit_wor_full by lia.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

Theorem tnum_not_bit : forall w a i, 0 <= i < Zpos w ->
  Z.testbit (wnot w a) i = negb (Z.testbit a i).
Proof.
  intros w a i Hi. rewrite testbit_wnot_full by lia.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

Theorem tnum_xor_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wxor w a b) i = xorb (Z.testbit a i) (Z.testbit b i).
Proof.
  intros w a b i Hi. unfold wxor.
  now rewrite Z.lxor_spec, !tnum_wrap_bit by exact Hi.
Qed.

Theorem tnum_subset_bits : forall w a b,
  tnum_subset w a b = true <->
  forall i, 0 <= i < Zpos w -> Z.testbit a i = true -> Z.testbit b i = true.
Proof.
  intros w a b. unfold tnum_subset. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.eqb_eq. split.
  - intros Heq i Hi Hbit.
    apply (f_equal (fun z => Z.testbit z i)) in Heq.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_and_bit, tnum_wrap_bit, Hbit in Heq by exact Hi.
    exact Heq.
  - intros Hbits. apply (word_ext w); [apply wand_is_word|apply wrap_is_word|].
    intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
    + rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_and_bit, tnum_wrap_bit by lia.
      destruct (Z.testbit a i) eqn:Ha; [|reflexivity].
      now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Hbits i ltac:(lia) Ha).
    + rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !(word_bits_high w) by
        (try apply wand_is_word; try apply wrap_is_word; lia). reflexivity.
Qed.

Theorem tnum_equiv_bits : forall w a b,
  tnum_equiv w a b <->
  forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros a) i = Z.testbit (zeros b) i /\
    Z.testbit (ones a) i = Z.testbit (ones b) i.
Proof.
  intros w a b. unfold tnum_equiv. split.
  - intros [Hz Ho] i Hi. apply (f_equal (fun z => Z.testbit z i)) in Hz, Ho.
    rewrite !tnum_wrap_bit in Hz, Ho by exact Hi. exact (conj Hz Ho).
  - intro Hbits. split; apply Z.bits_inj'; intros i Hi;
      rewrite !testbit_wrap by exact Hi;
      destruct (i <? Zpos w) eqn:Hlow; cbn; try reflexivity;
      apply Z.ltb_lt in Hlow;
      first [apply (proj1 (Hbits i ltac:(lia)))|apply (proj2 (Hbits i ltac:(lia)))].
Qed.

Theorem tnum_leb_bits : forall w a b,
  tnum_leb w a b = true <->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros b) i = true -> Z.testbit (zeros a) i = true) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (ones b) i = true -> Z.testbit (ones a) i = true).
Proof.
  intros w a b.
  change (tnum_subset w (zeros b) (zeros a) &&
    tnum_subset w (ones b) (ones a) = true <->
    (forall i, 0 <= i < Zpos w ->
      Z.testbit (zeros b) i = true -> Z.testbit (zeros a) i = true) /\
    (forall i, 0 <= i < Zpos w ->
      Z.testbit (ones b) i = true -> Z.testbit (ones a) i = true)).
  rewrite andb_true_iff, !tnum_subset_bits. reflexivity.
Qed.

Theorem tnum_join_bits : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (zeros (tnum_join w a b)) i =
    (Z.testbit (zeros a) i && Z.testbit (zeros b) i) /\
  Z.testbit (ones (tnum_join w a b)) i =
    (Z.testbit (ones a) i && Z.testbit (ones b) i).
Proof.
  intros w a b i Hi. split; cbn [tnum_join zeros ones];
    rewrite tnum_wand_agrees; apply tnum_and_bit; exact Hi.
Qed.

Theorem tnum_all_bits : forall w i, 0 <= i < Zpos w ->
  Z.testbit (modulus w - 1) i = true.
Proof.
  intros w i Hi. rewrite all_ones_bits by lia.
  now apply Z.ltb_lt.
Qed.

Theorem tnum_gamma_bits : forall w t z,
  tnum_gamma w t z <->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros t) i = true -> Z.testbit z i = false) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (ones t) i = true -> Z.testbit z i = true).
Proof.
  intros w t z. unfold tnum_gamma. split.
  - intros [Hz Ho]. split; intros i Hi Hbit.
    + apply (f_equal (fun x => Z.testbit x i)) in Hz.
      rewrite Z.land_spec, tnum_wrap_bit, Z.bits_0, Hbit, andb_true_r in Hz
        by exact Hi. exact Hz.
    + apply (f_equal (fun x => Z.testbit x i)) in Ho.
      rewrite Z.land_spec, tnum_wrap_bit, Z.lnot_spec, Z.bits_0, Hbit in Ho
        by lia. cbn in Ho. now apply negb_false_iff in Ho.
  - intros [Hz Ho]. split; apply Z.bits_inj'; intros i Hi;
      rewrite Z.land_spec, testbit_wrap, ?Z.lnot_spec, Z.bits_0 by exact Hi;
      destruct (i <? Zpos w) eqn:Hlow; cbn; try apply andb_false_r; try reflexivity;
      apply Z.ltb_lt in Hlow.
    + destruct (Z.testbit (zeros t) i) eqn:Hbit; [rewrite (Hz i ltac:(lia) Hbit)|];
        cbn; now rewrite ?andb_false_r.
    + destruct (Z.testbit (ones t) i) eqn:Hbit; [rewrite (Ho i ltac:(lia) Hbit)|];
        reflexivity.
Qed.

Theorem tnum_gamma_monotone : forall w a b z,
  tnum_leb w a b = true -> tnum_gamma w a z -> tnum_gamma w b z.
Proof.
  intros w a b z Hle Hgamma. apply tnum_leb_bits in Hle.
  apply tnum_gamma_bits in Hgamma. apply tnum_gamma_bits.
  destruct Hle as [Hlez Hleo], Hgamma as [Hz Ho].
  split; intros i Hi Hbit; [apply Hz, Hlez|apply Ho, Hleo]; assumption.
Qed.

Theorem tnum_gamma_bot_empty : forall w z, ~ tnum_gamma w (tnum_bot w) z.
Proof.
  intros w z Hgamma. apply tnum_gamma_bits in Hgamma. destruct Hgamma as [Hz Ho].
  pose proof (tnum_all_bits w 0 ltac:(lia)) as Hbit.
  specialize (Hz 0 ltac:(lia) Hbit). specialize (Ho 0 ltac:(lia) Hbit). congruence.
Qed.

Theorem tnum_top_sound : forall w z, tnum_gamma w tnum_top z.
Proof.
  intros w z. unfold tnum_gamma, tnum_top. cbn [zeros ones].
  rewrite wrap_0, Z.land_0_r, Z.land_0_l. auto.
Qed.

Theorem tnum_const_sound : forall w z, tnum_gamma w (tnum_const w z) (wrap w z).
Proof.
  intros w z. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_const zeros ones] in Hbit.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit in Hbit by exact Hi.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit by exact Hi. now apply negb_true_iff in Hbit.
  - now rewrite tnum_wrap_agrees in Hbit.
Qed.

Theorem tnum_normalise_sound : forall w a z,
  tnum_gamma w (tnum_normalise w a) z <-> tnum_gamma w a z.
Proof.
  intros w a z. unfold tnum_gamma, tnum_normalise. cbn [zeros ones].
  now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !wrap_wrap.
Qed.

Theorem tnum_meet_gamma : forall w a b z,
  tnum_gamma w (tnum_meet w a b) z <-> tnum_gamma w a z /\ tnum_gamma w b z.
Proof.
  intros w a b z. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !tnum_gamma_bits. split.
  - intros [Hz Ho]. split; split; intros i Hi Hbit;
      first [apply (Hz i Hi)|apply (Ho i Hi)];
      cbn [tnum_meet zeros ones]; rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_or_bit, Hbit by exact Hi;
      now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, ?orb_true_r.
  - intros [[Haz Hao] [Hbz Hbo]]. split; intros i Hi Hbit;
      cbn [tnum_meet zeros ones] in Hbit;
      rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_or_bit in Hbit by exact Hi;
      apply orb_true_iff in Hbit as [Hbit|Hbit]; auto.
Qed.

Theorem tnum_meet_sound : forall w a b z,
  tnum_gamma w a z -> tnum_gamma w b z -> tnum_gamma w (tnum_meet w a b) z.
Proof.
  intros w a b z Ha Hb. apply tnum_meet_gamma. now split.
Qed.

Theorem tnum_meet_lower_left : forall w a b,
  tnum_leb w (tnum_meet w a b) a = true.
Proof.
  intros w a b. apply tnum_leb_bits. split; intros i Hi Hbit;
    cbn [tnum_meet zeros ones]; rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_or_bit, Hbit by exact Hi; reflexivity.
Qed.

Theorem tnum_join_sound : forall w a b z,
  tnum_gamma w a z \/ tnum_gamma w b z -> tnum_gamma w (tnum_join w a b) z.
Proof.
  intros w a b z Hgamma. destruct Hgamma as [Hgamma|Hgamma];
    apply tnum_gamma_bits in Hgamma; destruct Hgamma as [Hz Ho];
    apply tnum_gamma_bits; split; intros i Hi Hbit;
    cbn [tnum_join zeros ones] in Hbit;
    rewrite tnum_wand_agrees, tnum_and_bit in Hbit by exact Hi;
    apply andb_true_iff in Hbit as [Ha Hb]; eauto.
Qed.

Theorem tnum_value_bounds : forall w a x, tnum_gamma w a x ->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (tnum_min w a) i = true -> Z.testbit x i = true) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit x i = true -> Z.testbit (tnum_max w a) i = true).
Proof.
  intros w a x Hgamma. apply tnum_gamma_bits in Hgamma. destruct Hgamma as [Hz Ho].
  split; intros i Hi Hbit.
  - unfold tnum_min in Hbit. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hbit by exact Hi. now apply Ho.
  - unfold tnum_max. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit by exact Hi.
    destruct (Z.testbit (zeros a) i) eqn:Hknown; [|reflexivity].
    specialize (Hz i Hi Hknown). congruence.
Qed.

Theorem tnum_known_bit : forall w a x i,
  tnum_gamma w a x -> 0 <= i < Zpos w -> Z.testbit (tnum_mask w a) i = false ->
  Z.testbit (tnum_min w a) i = Z.testbit x i /\
  Z.testbit (tnum_max w a) i = Z.testbit x i.
Proof.
  intros w a x i Hgamma Hi Hmask. apply tnum_gamma_bits in Hgamma.
  destruct Hgamma as [Hz Ho]. unfold tnum_mask in Hmask.
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit, tnum_or_bit in Hmask by exact Hi.
  unfold tnum_min, tnum_max. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit, tnum_not_bit by exact Hi.
  specialize (Hz i Hi). specialize (Ho i Hi).
  destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
    cbn in *; intuition discriminate.
Qed.

Theorem tnum_bitwise_le : forall w x y,
  is_word w x -> is_word w y ->
  (forall i, 0 <= i < Zpos w -> Z.testbit x i = true -> Z.testbit y i = true) -> x <= y.
Proof.
  intros w x y Hx Hy Hbits.
  assert (Hdiff : Z.ldiff x y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
    - specialize (Hbits i ltac:(lia)).
      destruct (Z.testbit x i), (Z.testbit y i); cbn in *; intuition discriminate.
    - rewrite (word_bits_high w x i Hx ltac:(lia)). reflexivity. }
  exact (proj2 (Z.ldiff_le x y (proj1 Hy) Hdiff)).
Qed.

Theorem tnum_unsigned_bounds : forall w a x,
  is_word w x -> tnum_gamma w a x -> tnum_min w a <= x <= tnum_max w a.
Proof.
  intros w a x Hx Ha. destruct (tnum_value_bounds w a x Ha) as [Hlo Hhi].
  split; apply (tnum_bitwise_le w); try assumption;
    unfold tnum_min, tnum_max;
    rewrite ?tnum_wrap_agrees, ?tnum_wnot_agrees;
    first [apply wrap_is_word | apply wnot_is_word].
Qed.

Theorem tnum_constant_value : forall w a x c,
  is_word w x -> tnum_gamma w a x -> tnum_constant w a = Some c -> x = c.
Proof.
  intros w a x c Hx Ha Hconst. unfold tnum_constant in Hconst.
  rewrite tnum_wrap_agrees, tnum_wnot_agrees in Hconst.
  destruct (wrap w (zeros a) =? wnot w (ones a)) eqn:Heq; [|discriminate].
  inversion Hconst; subst c. apply Z.eqb_eq in Heq.
  apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho]. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - unfold tnum_min. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit by lia.
    apply (f_equal (fun z => Z.testbit z i)) in Heq.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit, tnum_not_bit in Heq by lia.
    specialize (Hz i ltac:(lia)). specialize (Ho i ltac:(lia)).
    destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
      cbn in *; intuition discriminate.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (word_bits_high w x i Hx ltac:(lia)).
    symmetry. apply (word_bits_high w (tnum_min w a) i).
    + unfold tnum_min. rewrite tnum_wrap_agrees. apply wrap_is_word.
    + lia.
Qed.

Theorem tnum_empty_sound : forall w a x,
  tnum_gamma w a x -> tnum_empty w a = false.
Proof.
  intros w a x Ha. unfold tnum_empty. apply negb_false_iff, Z.eqb_eq.
  apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
  apply Z.bits_inj'. intros i Hi. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, testbit_wand_full, Z.bits_0 by exact Hi.
  destruct (i <? Zpos w) eqn:Hlow; [|reflexivity]. apply Z.ltb_lt in Hlow.
  specialize (Hz i ltac:(lia)). specialize (Ho i ltac:(lia)).
  destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i); cbn; auto.
  exfalso. specialize (Hz eq_refl). specialize (Ho eq_refl). congruence.
Qed.

Theorem tnum_endpoints_sound : forall w a,
  tnum_empty w a = false ->
  tnum_gamma w a (tnum_min w a) /\ tnum_gamma w a (tnum_max w a).
Proof.
  intros w a Hempty. unfold tnum_empty in Hempty.
  apply negb_false_iff, Z.eqb_eq in Hempty.
  assert (Hdisjoint : forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros a) i && Z.testbit (ones a) i = false).
  { intros i Hi. apply (f_equal (fun z => Z.testbit z i)) in Hempty.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_and_bit, Z.bits_0 in Hempty by exact Hi. exact Hempty. }
  split; apply tnum_gamma_bits; split; intros i Hi Hbit;
    unfold tnum_min, tnum_max; rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, ?tnum_wrap_bit, ?tnum_not_bit by exact Hi.
  - specialize (Hdisjoint i Hi). rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hbit in Hdisjoint. exact Hdisjoint.
  - exact Hbit.
  - now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hbit.
  - specialize (Hdisjoint i Hi). rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hbit, andb_true_r in Hdisjoint.
    now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hdisjoint.
Qed.

Theorem tnum_mask_bit : forall w a i, 0 <= i < Zpos w ->
  Z.testbit (tnum_mask w a) i =
    negb (Z.testbit (zeros a) i || Z.testbit (ones a) i).
Proof.
  intros w a i Hi. unfold tnum_mask. now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit, tnum_or_bit by exact Hi.
Qed.

Theorem tnum_amount_disjoint : forall w a c,
  Z.land c (tnum_mask w a) = c -> Z.land (tnum_min w a) c = 0.
Proof.
  intros w a c Hsub. apply Z.bits_inj'. intros i Hi. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.land_spec, Z.bits_0.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - apply (f_equal (fun z => Z.testbit z i)) in Hsub.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.land_spec, tnum_mask_bit in Hsub by lia.
    unfold tnum_min. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit by lia.
    destruct (Z.testbit c i), (Z.testbit (zeros a) i), (Z.testbit (ones a) i);
      cbn in *; congruence.
  - unfold tnum_min. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)).
    reflexivity.
Qed.

Theorem tnum_decompose : forall w a x,
  is_word w x -> tnum_gamma w a x ->
  exists c, Z.land c (tnum_mask w a) = c /\ x = tnum_min w a + c.
Proof.
  intros w a x Hx Ha. exists (Z.land x (tnum_mask w a)). split.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, <- Z.land_assoc, Z.land_diag. reflexivity.
  - assert (Hdisjoint : Z.land (tnum_min w a) (Z.land x (tnum_mask w a)) = 0).
    { apply tnum_amount_disjoint. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, <- Z.land_assoc, Z.land_diag. reflexivity. }
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.add_nocarry_lxor by exact Hdisjoint.
    apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
    apply Z.bits_inj'. intros i Hi. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.lxor_spec, Z.land_spec.
    destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
    + unfold tnum_min. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit, tnum_mask_bit by lia.
      specialize (Hz i ltac:(lia)). specialize (Ho i ltac:(lia)).
      destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
        cbn in *; intuition discriminate.
    + rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (word_bits_high w x i Hx ltac:(lia)). unfold tnum_min.
      rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)). reflexivity.
Qed.

Theorem tnum_max_value_mask : forall w a,
  tnum_empty w a = false -> tnum_max w a = tnum_min w a + tnum_mask w a.
Proof.
  intros w a Hempty.
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.add_nocarry_lxor by (apply tnum_amount_disjoint; apply Z.land_diag).
  destruct (tnum_endpoints_sound w a Hempty) as [Hmin _].
  apply tnum_gamma_bits in Hmin. destruct Hmin as [Hz _].
  apply Z.bits_inj'. intros i Hi. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.lxor_spec.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - unfold tnum_max, tnum_min. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit, tnum_wrap_bit, tnum_mask_bit by lia.
    specialize (Hz i ltac:(lia)). unfold tnum_min in Hz.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hz by lia.
    destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i); cbn in *;
      intuition discriminate.
  - unfold tnum_max, tnum_min, tnum_mask.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (word_bits_high w _ i (wnot_is_word w _) ltac:(lia)),
      (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)),
      (word_bits_high w _ i (wnot_is_word w _) ltac:(lia)). reflexivity.
Qed.

Theorem tnum_gamma_wrap : forall w a z,
  tnum_gamma w a (wrap w z) <-> tnum_gamma w a z.
Proof.
  intros w a z. rewrite !tnum_gamma_bits. split; intros [Hz Ho]; split;
    intros i Hi Hbit; specialize (Hz i Hi); specialize (Ho i Hi);
    rewrite ?tnum_wrap_bit in * by exact Hi; auto.
Qed.

Theorem tnum_not_sound : forall w a z,
  tnum_gamma w a z -> tnum_gamma w (tnum_not w a) (wnot w z).
Proof.
  intros w a z Hgamma. apply tnum_gamma_bits in Hgamma.
  destruct Hgamma as [Hz Ho]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_not zeros ones] in Hbit;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hbit by exact Hi; rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit by exact Hi.
  - now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Ho i Hi Hbit).
  - now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Hz i Hi Hbit).
Qed.

Theorem tnum_and_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_and w a b) (wand w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_and zeros ones] in Hbit;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_and_bit by exact Hi.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_or_bit in Hbit by exact Hi. apply orb_true_iff in Hbit as [Hz|Hz].
    + now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Haz i Hi Hz).
    + rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Hbz i Hi Hz). apply andb_false_r.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Ho Ho'].
    now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Hao i Hi Ho), (Hbo i Hi Ho').
Qed.

Theorem tnum_or_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_or w a b) (wor w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_or zeros ones] in Hbit;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_or_bit by exact Hi.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Hz Hz'].
    now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Haz i Hi Hz), (Hbz i Hi Hz').
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_or_bit in Hbit by exact Hi. apply orb_true_iff in Hbit as [Ho|Ho].
    + now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Hao i Hi Ho).
    + rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Hbo i Hi Ho). apply orb_true_r.
Qed.

Theorem tnum_xor_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_xor w a b) (wxor w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_xor zeros ones] in Hbit;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_or_bit, !tnum_and_bit in Hbit by exact Hi;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_xor_bit by exact Hi;
    apply orb_true_iff in Hbit as [Hbit|Hbit]; apply andb_true_iff in Hbit as [Hl Hr].
  - now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Haz i Hi Hl), (Hbz i Hi Hr).
  - now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Hao i Hi Hl), (Hbo i Hi Hr).
  - now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Haz i Hi Hl), (Hbo i Hi Hr).
  - now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (Hao i Hi Hl), (Hbz i Hi Hr).
Qed.

Definition tnum_carry (a b c : Z) (initial : bool) : Prop :=
  c / 2 = Z.lor (Z.land a b) (Z.land c (Z.lor a b)) /\ Z.testbit c 0 = initial.

Local Lemma tnum_carry_step : forall a b c initial i,
  tnum_carry a b c initial -> 0 <= i ->
  Z.testbit c (Z.succ i) =
    ((Z.testbit a i && Z.testbit b i) ||
      (Z.testbit c i && (Z.testbit a i || Z.testbit b i))).
Proof.
  intros a b c initial i [Hstep _] Hi.
  rewrite <- Z.div2_bits by exact Hi.
  rewrite Hstep, !Z.lor_spec, !Z.land_spec, !Z.lor_spec. reflexivity.
Qed.

Local Lemma tnum_carry_monotone : forall w a b a' b' c c' initial,
  tnum_carry a b c initial -> tnum_carry a' b' c' initial ->
  (forall i, 0 <= i < Zpos w -> Z.testbit a i = true -> Z.testbit a' i = true) ->
  (forall i, 0 <= i < Zpos w -> Z.testbit b i = true -> Z.testbit b' i = true) ->
  forall i, 0 <= i <= Zpos w -> Z.testbit c i = true -> Z.testbit c' i = true.
Proof.
  intros w a b a' b' c c' initial Hc Hc' Ha Hb i Hi.
  assert (Hnat : forall n, (n <= Pos.to_nat w)%nat ->
    Z.testbit c (Z.of_nat n) = true -> Z.testbit c' (Z.of_nat n) = true).
  { intro n. induction n as [|n IH]; intros Hn Hbit.
    - change (Z.testbit c 0 = true) in Hbit. rewrite (proj2 Hc) in Hbit.
      change (Z.testbit c' 0 = true). now rewrite (proj2 Hc').
    - rewrite Nat2Z.inj_succ,
        (tnum_carry_step a b c initial (Z.of_nat n) Hc ltac:(lia)) in Hbit.
      rewrite Nat2Z.inj_succ,
        (tnum_carry_step a' b' c' initial (Z.of_nat n) Hc' ltac:(lia)).
      pose proof (Ha (Z.of_nat n) ltac:(rewrite <- positive_nat_Z; lia)) as Haa.
      pose proof (Hb (Z.of_nat n) ltac:(rewrite <- positive_nat_Z; lia)) as Hbb.
      specialize (IH ltac:(lia)).
      destruct (Z.testbit a (Z.of_nat n)), (Z.testbit b (Z.of_nat n)),
        (Z.testbit a' (Z.of_nat n)), (Z.testbit b' (Z.of_nat n)),
        (Z.testbit c (Z.of_nat n)), (Z.testbit c' (Z.of_nat n));
        cbn in *; intuition discriminate. }
  replace i with (Z.of_nat (Z.to_nat i)) by (rewrite Z2Nat.id; lia).
  apply Hnat. apply Nat2Z.inj_le. rewrite positive_nat_Z, Z2Nat.id by lia. lia.
Qed.

Local Lemma tnum_sum_known : forall w a b x y initial i,
  tnum_gamma w a x -> tnum_gamma w b y -> 0 <= i < Zpos w ->
  Z.testbit (tnum_mask w a) i = false -> Z.testbit (tnum_mask w b) i = false ->
  Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i =
    Z.testbit (tnum_max w a + tnum_max w b + Z.b2z initial) i ->
  Z.testbit (x + y + Z.b2z initial) i =
    Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i.
Proof.
  intros w a b x y initial i Ha Hb Hi Hma Hmb Heq.
  destruct (Z.add_carry_bits x y initial) as [c [Hsum [Hstep Hzero]]].
  destruct (Z.add_carry_bits (tnum_min w a) (tnum_min w b) initial)
    as [cl [Hsuml [Hstepl Hzerol]]].
  destruct (Z.add_carry_bits (tnum_max w a) (tnum_max w b) initial)
    as [ch [Hsumh [Hsteph Hzeroh]]].
  destruct (tnum_value_bounds w a x Ha) as [Hal Hah].
  destruct (tnum_value_bounds w b y Hb) as [Hbl Hbh].
  pose proof (tnum_carry_monotone w _ _ _ _ _ _ initial (conj Hstepl Hzerol)
    (conj Hstep Hzero) Hal Hbl i ltac:(lia)) as Hlower.
  pose proof (tnum_carry_monotone w _ _ _ _ _ _ initial (conj Hstep Hzero)
    (conj Hsteph Hzeroh) Hah Hbh i ltac:(lia)) as Hupper.
  destruct (tnum_known_bit w a x i Ha Hi Hma) as [Halbit Hahbit].
  destruct (tnum_known_bit w b y i Hb Hi Hmb) as [Hblbit Hbhbit].
  rewrite Hsuml, Hsumh, !Z.lxor_spec, Halbit, Hahbit, Hblbit, Hbhbit in Heq.
  rewrite Hsum, Hsuml, !Z.lxor_spec, Halbit, Hblbit.
  destruct (Z.testbit x i), (Z.testbit y i), (Z.testbit c i),
    (Z.testbit cl i), (Z.testbit ch i); cbn in *; intuition discriminate.
Qed.

Local Lemma tnum_adc_known : forall w a b x y initial i,
  tnum_gamma w a x -> tnum_gamma w b y -> 0 <= i < Zpos w ->
  Z.testbit (tnum_adc_uncertain w a b initial) i = false ->
  Z.testbit (x + y + Z.b2z initial) i =
    Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i.
Proof.
  intros w a b x y initial i Ha Hb Hi Hm.
  unfold tnum_adc_uncertain in Hm. rewrite !Z.lor_spec, Z.lxor_spec in Hm.
  apply orb_false_iff in Hm as [Hsum Hm]. apply orb_false_iff in Hm as [Hma Hmb].
  eapply tnum_sum_known; try eassumption.
  destruct (Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i),
    (Z.testbit (tnum_max w a + tnum_max w b + Z.b2z initial) i);
    cbn in Hsum; congruence.
Qed.

Theorem tnum_adc_sound : forall w a b x y initial,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_adc w a b initial) (wrap w (x + y + Z.b2z initial)).
Proof.
  intros w a b x y initial Ha Hb. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_adc zeros ones] in Hbit;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit, ?Z.land_spec, ?Z.lnot_spec, ?Z.lor_spec in Hbit by
      (try exact Hi; lia).
  - apply negb_true_iff in Hbit. apply orb_false_iff in Hbit as [Hv Hm].
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit, (tnum_adc_known w a b x y initial i Ha Hb Hi Hm)
      by exact Hi. exact Hv.
  - apply andb_true_iff in Hbit as [Hv Hm]. apply negb_true_iff in Hm.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit, (tnum_adc_known w a b x y initial i Ha Hb Hi Hm)
      by exact Hi. exact Hv.
Qed.

Theorem tnum_add_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w (tnum_add w a b) (wadd w x y).
Proof.
  intros w a b x y Ha Hb. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, wadd_value. unfold tnum_add.
  replace (x + y) with (x + y + Z.b2z false) by (cbn [Z.b2z]; ring).
  now apply tnum_adc_sound.
Qed.

Theorem tnum_sub_sound : forall w a b x y,
  is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_sub w a b) (wsub w x y).
Proof.
  intros w a b x y Hy Ha Hb.
  pose proof (tnum_adc_sound w a (tnum_not w b) x (wnot w y) true Ha
    (tnum_not_sound w b y Hb)) as Hresult.
  unfold tnum_sub. cbn [Z.b2z] in Hresult.
  assert (Hnot : wnot w y = modulus w - 1 - y).
  { pose proof (wnot_lnot w y) as Hnot.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (wrap_id w y Hy), lnot_value in Hnot.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, wrap_mod in Hnot. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hnot.
    symmetry. apply Z.mod_unique with (q := -1).
    - left. unfold is_word in Hy. lia.
    - ring. }
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hnot in Hresult.
  replace (x + (modulus w - 1 - y) + 1) with ((x - y) + 1 * modulus w)
    in Hresult by ring.
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, wrap_add_modulus in Hresult. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, wsub_value. exact Hresult.
Qed.

Theorem tnum_neg_sound : forall w a x,
  is_word w x -> tnum_gamma w a x -> tnum_gamma w (tnum_neg w a) (wneg w x).
Proof.
  intros w a x Hx Ha. rewrite wneg_value.
  replace (-x) with (0 - x) by ring. rewrite <- wsub_value.
  apply tnum_sub_sound; try assumption.
  pose proof (tnum_const_sound w 0) as Hzero. now rewrite wrap_0 in Hzero.
Qed.

Local Lemma tnum_bitlen_bound : forall h, 0 <= h ->
  0 <= tnum_bitlen h /\ h < 2 ^ tnum_bitlen h.
Proof.
  intros h Hh. unfold tnum_bitlen. destruct (h =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. subst h. cbn. lia.
  - apply Z.eqb_neq in Hz. pose proof (Z.log2_nonneg h).
    pose proof (Z.log2_spec h ltac:(lia)). lia.
Qed.

Theorem tnum_upper_sound : forall w h x,
  0 <= x <= h -> tnum_gamma w (tnum_upper w h) x.
Proof.
  intros w h x Hx. pose proof (tnum_bitlen_bound h ltac:(lia)) as [Hk Hbound].
  apply tnum_gamma_bits. split; intros i Hi Hbit.
  - cbn [tnum_upper zeros] in Hbit. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit in Hbit by exact Hi.
    apply negb_true_iff in Hbit.
    assert (Hhigh : tnum_bitlen h <= i).
    { destruct (Z_lt_ge_dec i (tnum_bitlen h)); [|lia].
      rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.ones_spec_low in Hbit by lia. discriminate. }
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, <- (Z.mod_small x (2 ^ tnum_bitlen h) ltac:(lia)).
    apply Z.mod_pow2_bits_high. lia.
  - cbn [tnum_upper ones] in Hbit. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.bits_0 in Hbit. discriminate.
Qed.

Theorem tnum_udiv_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_udiv w a b) (wudiv w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_udiv. rewrite tnum_wrap_agrees.
  destruct (wrap w (ones b) =? 0) eqn:Hnonzero; [apply tnum_top_sound|].
  apply Z.eqb_neq in Hnonzero.
  pose proof (tnum_unsigned_bounds w b y Hy Hb) as Hbounds.
  pose proof (wrap_is_word w (ones b)) as Hones.
  assert (Hynz : y <> 0).
  { unfold tnum_min, is_word in *. rewrite tnum_wrap_agrees in Hbounds. lia. }
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hdividend.
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, wudiv_spec by assumption. apply tnum_upper_sound.
  split; [apply Z.div_pos; unfold is_word in *; lia|].
  eapply Z.le_trans; [|exact (proj2 Hdividend)].
  apply Z.div_le_upper_bound; unfold is_word in *; nia.
Qed.

Theorem tnum_urem_sound : forall w a x y,
  is_word w x -> is_word w y -> tnum_gamma w a x ->
  tnum_gamma w (tnum_urem w a) (wurem w x y).
Proof.
  intros w a x y Hx Hy Ha.
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hbounds. unfold tnum_urem.
  destruct (Z.eq_dec y 0) as [->|Hnz].
  - rewrite wurem_zero, (wrap_id w x Hx). apply tnum_upper_sound.
    unfold is_word in Hx. lia.
  - rewrite wurem_spec by assumption. apply tnum_upper_sound. split.
    + apply Z.mod_pos_bound. unfold is_word in Hy. lia.
    + eapply Z.le_trans; [|exact (proj2 Hbounds)].
      apply Z.mod_le; unfold is_word in *; lia.
Qed.

Theorem tnum_add_linux_agrees : forall w a b,
  tnum_empty w a = false -> tnum_empty w b = false ->
  tnum_add w a b = tnum_linux_add w a b.
Proof.
  intros w a b Ha Hb. unfold tnum_add, tnum_adc, tnum_adc_uncertain, tnum_linux_add.
  cbn [Z.b2z]. rewrite !Z.add_0_r, (tnum_max_value_mask w a Ha),
    (tnum_max_value_mask w b Hb).
  replace (tnum_min w a + tnum_mask w a + (tnum_min w b + tnum_mask w b)) with
    (tnum_min w a + tnum_min w b + (tnum_mask w a + tnum_mask w b)) by ring.
  rewrite Z.lxor_comm. reflexivity.
Qed.

Theorem tnum_map_sound : forall sw rw f a x,
  tnum_bit_copy sw rw f -> is_word sw x -> tnum_gamma sw a x ->
  tnum_gamma rw (tnum_map sw rw f a) (f x).
Proof.
  intros sw rw f a x Hcopy Hx Ha. apply tnum_gamma_bits in Ha.
  destruct Ha as [Hz Ho].
  assert (Hmin : is_word sw (tnum_min sw a)).
  { unfold tnum_min. rewrite tnum_wrap_agrees. apply wrap_is_word. }
  assert (Hmax : is_word sw (tnum_max sw a)).
  { unfold tnum_max. rewrite tnum_wnot_agrees. apply wnot_is_word. }
  apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_map zeros ones] in Hbit.
  - rewrite tnum_wnot_agrees, tnum_not_bit in Hbit by exact Hi.
    apply negb_true_iff in Hbit.
    destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]]; [now apply Hclear|].
    rewrite (Hsource _ Hmax) in Hbit. rewrite (Hsource _ Hx).
    unfold tnum_max in Hbit.
    rewrite tnum_wnot_agrees, tnum_not_bit in Hbit by exact Hj.
    apply negb_false_iff in Hbit. now apply Hz.
  - rewrite tnum_wrap_agrees, tnum_wrap_bit in Hbit by exact Hi.
    destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]].
    + rewrite (Hclear _ Hmin) in Hbit. discriminate.
    + rewrite (Hsource _ Hmin) in Hbit. rewrite (Hsource _ Hx).
      unfold tnum_min in Hbit.
      rewrite tnum_wrap_agrees, tnum_wrap_bit in Hbit by exact Hj. now apply Ho.
Qed.

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

Theorem tnum_ashr_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => washr w x k).
Proof.
  intros w k Hk i Hi. right. exists (Z.min (i + k) (Zpos w - 1)).
  split; [unfold is_word in Hk; lia|]. intros x Hx.
  rewrite testbit_washr by (try assumption; lia).
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

Theorem tnum_shift_sound : forall o w a x k f,
  (o = bvshl \/ o = bvlshr \/ o = bvashr) ->
  word_fun2 o = Some f -> is_word w x -> is_word w k -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shift o w a k) (eval_binary_tag f w x k).
Proof.
  intros o w a x k f Ho Hf Hx Hk Ha. unfold tnum_shift. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hf.
  apply (tnum_map_sound w w (fun z => eval_binary_tag f w z k) a x); try assumption.
  destruct Ho as [Ho|[Ho|Ho]]; subst o; injection Hf as <-.
  - now apply tnum_shl_copy.
  - now apply tnum_lshr_copy.
  - now apply tnum_ashr_copy.
Qed.

Theorem tnum_zext_copy : forall sw rw, (sw <= rw)%positive ->
  tnum_bit_copy sw rw (fun x => wrap rw x).
Proof.
  intros sw rw Hwidth i Hi. destruct (Z_lt_ge_dec i (Zpos sw)) as [Hlow|Hhigh].
  - right. exists i. split; [lia|]. intros x Hx. now rewrite tnum_wrap_bit by exact Hi.
  - left. intros x Hx. rewrite tnum_wrap_bit by exact Hi.
    apply (word_bits_high sw x i Hx). lia.
Qed.

Theorem tnum_trunc_copy : forall sw rw, (rw <= sw)%positive ->
  tnum_bit_copy sw rw (fun x => wrap rw x).
Proof.
  intros sw rw Hwidth i Hi. right. exists i. split.
  - apply Pos2Z.pos_le_pos in Hwidth. lia.
  - intros x Hx. now rewrite tnum_wrap_bit by exact Hi.
Qed.

Theorem tnum_extract_copy : forall sw rw lo,
  0 <= lo -> Zpos rw + lo <= Zpos sw ->
  tnum_bit_copy sw rw (fun x => wrap rw (x / 2 ^ lo)).
Proof.
  intros sw rw lo Hlo Hwidth i Hi. right. exists (i + lo). split; [lia|].
  intros x Hx. rewrite tnum_wrap_bit by exact Hi. now rewrite Z.div_pow2_bits by lia.
Qed.

(** A bounded masked left shift agrees with the concrete word operation. *)
Lemma tnum_shl_value_agrees : forall w k x, 0 <= k <= Zpos w ->
  tnum_shl_value w k x = wshl w x k.
Proof.
  intros w k x Hk. unfold tnum_shl_value, wshl.
  rewrite (wrap_id w k) by (apply count_is_word; exact Hk).
  destruct (Zpos w <=? k); [reflexivity|].
  rewrite tnum_wrap_agrees, Z.shiftl_mul_pow2 by lia.
  unfold wrap. now rewrite Z.mul_mod_idemp_l by apply modulus_nonzero.
Qed.

(** A bounded masked logical right shift agrees with the concrete word operation. *)
Lemma tnum_lshr_value_agrees : forall w k x, 0 <= k <= Zpos w ->
  tnum_lshr_value w k x = wlshr w x k.
Proof.
  intros w k x Hk. unfold tnum_lshr_value, wlshr.
  rewrite (wrap_id w k) by (apply count_is_word; exact Hk).
  destruct (Zpos w <=? k); [reflexivity|].
  now rewrite tnum_wrap_agrees, Z.shiftr_div_pow2 by lia.
Qed.

(** The wrapped high part of a rotation fits below its low shift boundary. *)
Lemma tnum_rotation_high_bound : forall w k x, 0 <= k < Zpos w ->
  0 <= Z.shiftr (wrap w x) (Zpos w - k) < 2 ^ k.
Proof.
  intros w k x Hk. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (wrap_is_word w x) as Hx.
  assert (Hd : 0 < 2 ^ (Zpos w - k)) by (apply Z.pow_pos_nonneg; lia).
  split.
  - apply Z.div_pos; [exact (proj1 Hx)|lia].
  - apply Z.div_lt_upper_bound; [exact Hd|].
    rewrite <- Z.pow_add_r by lia.
    replace (Zpos w - k + k) with (Zpos w) by lia. exact (proj2 Hx).
Qed.

(** Saturating the shift and filling the high bits implements arithmetic right shift. *)
Lemma tnum_ashr_value_agrees : forall w k x, 0 <= k <= Zpos w ->
  tnum_ashr_value w k x = washr w x k.
Proof.
  intros w k x Hk.
  pose proof (word_fun2_normalised bvashr BAshr w x k eq_refl) as Hnormal.
  cbn [eval_binary_tag] in Hnormal.
  rewrite (wrap_id w k) in Hnormal by (apply count_is_word; exact Hk).
  rewrite <- Hnormal. apply Z.bits_inj'. intros i Hi.
  rewrite testbit_washr by
    (try apply wrap_is_word; try (apply count_is_word; exact Hk); exact Hi).
  unfold tnum_ashr_value. rewrite !tnum_wrap_agrees.
  set (k' := Z.min k (Zpos w - 1)).
  assert (Hk' : 0 <= k' <= Zpos w - 1) by (unfold k'; lia).
  assert (Hindex : Z.min (i + k') (Zpos w - 1) =
    Z.min (i + k) (Zpos w - 1)) by (unfold k'; lia).
  rewrite <- Hindex.
  destruct (Z.testbit (wrap w x) (Zpos w - 1)) eqn:Hsign.
  - rewrite Z.lor_spec, Z.shiftr_spec by lia.
    rewrite (testbit_wrap w (Z.lnot (Z.ones (Zpos w - k'))) i Hi),
      Z.lnot_spec by lia.
    destruct (i <? Zpos w) eqn:Hlow; cbn [andb].
    + apply Z.ltb_lt in Hlow.
      destruct (Z_lt_ge_dec (i + k') (Zpos w)) as [Hsource|Hsource].
      * rewrite Z.ones_spec_low, Z.min_l by lia. now rewrite orb_false_r.
      * rewrite Z.ones_spec_high, Z.min_r by lia. now rewrite orb_true_r, Hsign.
    + apply Z.ltb_ge in Hlow.
      rewrite (word_bits_high w (wrap w x) (i + k') (wrap_is_word w x)) by lia.
      reflexivity.
  - rewrite Z.shiftr_spec by lia.
    destruct (i <? Zpos w) eqn:Hlow; cbn [andb].
    + apply Z.ltb_lt in Hlow.
      destruct (Z_lt_ge_dec (i + k') (Zpos w)) as [Hsource|Hsource].
      * now rewrite Z.min_l by lia.
      * rewrite Z.min_r by lia.
        rewrite (word_bits_high w (wrap w x) (i + k') (wrap_is_word w x)) by lia.
        symmetry. exact Hsign.
    + apply Z.ltb_ge in Hlow.
      apply word_bits_high with (w := w); [apply wrap_is_word|lia].
Qed.

(** The two pieces of a rotation occupy disjoint bit positions. *)
Lemma tnum_rotation_disjoint : forall w k x, 0 <= k < Zpos w ->
  Z.land (Z.shiftl (wrap w x) k) (Z.shiftr (wrap w x) (Zpos w - k)) = 0.
Proof.
  intros w k x Hk. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_ge_dec i k) as [Hlow|Hhigh].
  - rewrite Z.shiftl_spec, Z.testbit_neg_r by lia. reflexivity.
  - rewrite <- (Z.mod_small _ _ (tnum_rotation_high_bound w k x Hk)).
    rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

(** A reduced masked rotation agrees with the concrete word operation. *)
Lemma tnum_rotl_value_agrees : forall w k x, 0 <= k < Zpos w ->
  tnum_rotl_value w k x = wrotl w x k.
Proof.
  intros w k x Hk. unfold tnum_rotl_value, wrotl.
  rewrite !tnum_wrap_agrees, (wrap_id w k) by (apply small_amount_word; exact Hk).
  rewrite Z.mod_small by exact Hk.
  rewrite <- Z.lxor_lor by (apply tnum_rotation_disjoint; exact Hk).
  rewrite <- Z.add_nocarry_lxor by (apply tnum_rotation_disjoint; exact Hk).
  now rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
Qed.

(** The masked scalar dispatcher agrees with its saturating word operations. *)
Lemma tnum_scalar_value_agrees : forall o w k x, 0 <= k ->
  tnum_scalar_value o w k x =
    match o with
    | bvshl => wshl w x (Z.min k (Zpos w))
    | bvlshr => wlshr w x (Z.min k (Zpos w))
    | bvashr => washr w x (Z.min k (Zpos w))
    | bvrotl => wrotl w x (k mod Zpos w)
    | bvrotr => wrotl w x ((-k) mod Zpos w)
    | _ => wrap w x
    end.
Proof.
  intros o w k x Hk. destruct o; cbn [tnum_scalar_value];
    rewrite ?Z.max_r by lia; try apply tnum_wrap_agrees.
  - apply tnum_shl_value_agrees. lia.
  - apply tnum_lshr_value_agrees. lia.
  - apply tnum_ashr_value_agrees. lia.
  - apply tnum_rotl_value_agrees. apply Z.mod_pos_bound. lia.
  - apply tnum_rotl_value_agrees. apply Z.mod_pos_bound. lia.
Qed.

(** Pointwise agreement on source words preserves the bit-copy property. *)
Lemma tnum_bit_copy_ext : forall sw rw f g,
  (forall x, is_word sw x -> f x = g x) ->
  tnum_bit_copy sw rw f -> tnum_bit_copy sw rw g.
Proof.
  intros sw rw f g Hfg Hcopy i Hi.
  destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]].
  - left. intros x Hx. rewrite <- Hfg by exact Hx. now apply Hclear.
  - right. exists j. split; [exact Hj|].
    intros x Hx. rewrite <- Hfg by exact Hx. now apply Hsource.
Qed.

Theorem tnum_shl_scalar_sound : forall w k a x,
  0 <= k -> is_word w x -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shl_scalar w k a) (tnum_shl_scalar_value w k x).
Proof.
  intros w k a x Hk Hx Ha. apply tnum_map_sound; try assumption.
  eapply tnum_bit_copy_ext with (f := fun z => wshl w z (Z.min k (Zpos w))).
  - intros z Hz. unfold tnum_shl_scalar_value.
    symmetry. apply tnum_shl_value_agrees. lia.
  - apply tnum_shl_copy. apply count_is_word. lia.
Qed.

Lemma tnum_scalar_word : forall o w k x,
  is_word w (tnum_scalar_value o w k x).
Proof.
  intros o w k x. destruct o; cbn [tnum_scalar_value];
    try (rewrite tnum_wrap_agrees; apply wrap_is_word).
  - rewrite tnum_shl_value_agrees by lia. apply wshl_is_word.
  - rewrite tnum_lshr_value_agrees by lia. apply wlshr_is_word.
  - rewrite tnum_ashr_value_agrees by lia. apply washr_is_word.
  - rewrite tnum_rotl_value_agrees by (apply Z.mod_pos_bound; lia).
    unfold wrotl. apply wrap_is_word.
  - rewrite tnum_rotl_value_agrees by (apply Z.mod_pos_bound; lia).
    unfold wrotl. apply wrap_is_word.
Qed.

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
  rewrite tnum_scalar_value_agrees by exact Hk.
  destruct o; cbn [tnum_source];
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

Theorem tnum_scalar_sound : forall o w k a x,
  0 <= k -> is_word w x -> tnum_gamma w a x ->
  tnum_gamma w (tnum_scalar o w k a) (tnum_scalar_value o w k x).
Proof.
  intros o w k a x Hk Hx Ha. apply tnum_map_sound; try assumption.
  now apply tnum_scalar_copy.
Qed.

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

Theorem tnum_scalar_agrees : forall o w f k x,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w k -> is_word w x ->
  tnum_scalar_value o w k x = eval_binary_tag f w x k.
Proof.
  intros o w f k x Ho Hf Hk Hx. assert (Hk0 : 0 <= k) by exact (proj1 Hk).
  apply (word_ext w); [apply tnum_scalar_word|now apply (word_fun2_is_word o f)|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite tnum_scalar_bits by (try assumption; lia).
    destruct Ho as [Ho|[Ho|[Ho|[Ho|Ho]]]]; subst o; injection Hf as <-;
      cbn [tnum_source eval_binary_tag].
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

Theorem tnum_sext_copy : forall sw rw,
  tnum_bit_copy sw rw (fun x => wrap rw (signed sw x)).
Proof.
  intros sw rw i Hi. right. exists (Z.min i (Zpos sw - 1)). split; [lia|].
  intros x Hx. rewrite tnum_wrap_bit by exact Hi. rewrite signed_bits by (try exact Hx; lia).
  destruct (i <? Zpos sw) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. rewrite Z.min_l by lia. reflexivity.
  - apply Z.ltb_ge in Hlow. rewrite Z.min_r by lia. apply msb_testbit.
Qed.

Theorem tnum_concat_sound : forall w v a b x y,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  tnum_gamma (w + v)%positive (tnum_concat w v a b) (x * modulus v + y).
Proof.
  intros w v a b x y Hx Hy Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_concat zeros ones] in Hbit;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hbit by exact Hi;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !modulus_value in Hbit |- *;
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, split_sum_bits in Hbit by
      (try (rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, <- modulus_value; apply wrap_is_word); lia);
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, split_sum_bits by (try (rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, <- modulus_value; exact Hy); lia);
    destruct (i <? Zpos v) eqn:Hpart.
  - apply Z.ltb_lt in Hpart. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hbit by lia. now apply Hbz.
  - apply Z.ltb_ge in Hpart. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hbit by
      (rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Pos2Z.inj_add in Hi; lia). apply Haz; [rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Pos2Z.inj_add in Hi; lia|exact Hbit].
  - apply Z.ltb_lt in Hpart. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hbit by lia. now apply Hbo.
  - apply Z.ltb_ge in Hpart. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hbit by
      (rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Pos2Z.inj_add in Hi; lia). apply Hao; [rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Pos2Z.inj_add in Hi; lia|exact Hbit].
Qed.

Theorem tnum_ctz_range : forall w x, 0 <= wctz w x <= Zpos w.
Proof.
  intros w x.
  pose proof (word_fun1_normalised bvctz UCtz w x eq_refl) as Hnorm.
  cbn [eval_unary_tag] in Hnorm.
  destruct (Z.eq_dec (wrap w x) 0) as [Hz|Hnz].
  - rewrite <- Hnorm, Hz, wctz_zero. lia.
  - rewrite <- Hnorm.
    destruct (wctz_spec w _ (wrap_is_word w x) Hnz) as [Hset _].
    split.
    + destruct (Z_le_gt_dec 0 (wctz w (wrap w x))); [assumption|].
      rewrite Z.testbit_neg_r in Hset by lia. discriminate.
    + destruct (Z_lt_ge_dec (wctz w (wrap w x)) (Zpos w)); [lia|].
      rewrite (word_bits_high w (wrap w x) (wctz w (wrap w x))
        (wrap_is_word w x) ltac:(lia)) in Hset. discriminate.
Qed.

Lemma tnum_trailing_clear : forall w a x i,
  tnum_gamma w a x -> 0 <= i < tnum_trailing w a -> Z.testbit x i = false.
Proof.
  intros w a x i Ha Hi. unfold tnum_trailing in Hi. rewrite tnum_wnot_agrees in Hi. apply tnum_gamma_bits in Ha. destruct Ha as [Hz _].
  pose proof (tnum_ctz_range w (wnot w (zeros a))) as Hrange.
  apply (Hz i ltac:(unfold tnum_trailing in Hi; lia)).
  assert (Hclear : Z.testbit (wnot w (zeros a)) i = false).
  { destruct (Z.eq_dec (wnot w (zeros a)) 0) as [Hnone|Hsome].
    - now rewrite Hnone, Z.bits_0.
    - apply (proj2 (wctz_spec w _ (wnot_is_word w _) Hsome)). exact Hi. }
  rewrite tnum_not_bit in Hclear by (unfold tnum_trailing in Hi; lia).
  now apply negb_false_iff in Hclear.
Qed.

Lemma tnum_trailing_factor : forall w a x,
  tnum_gamma w a x -> exists q, x = q * 2 ^ tnum_trailing w a.
Proof.
  intros w a x Ha. pose proof (tnum_ctz_range w (tnum_wnot w (zeros a))) as Hrange.
  assert (Hmod : x mod 2 ^ tnum_trailing w a = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
    destruct (Z_lt_ge_dec i (tnum_trailing w a)) as [Hlow|Hhigh].
    - rewrite Z.mod_pow2_bits_low by exact Hlow.
      eapply tnum_trailing_clear; [exact Ha|lia].
    - apply Z.mod_pow2_bits_high. unfold tnum_trailing in *. lia. }
  exists (x / 2 ^ tnum_trailing w a).
  pose proof (Z.div_mod x (2 ^ tnum_trailing w a)
    ltac:(pose proof (Z.pow_pos_nonneg 2 (tnum_trailing w a) ltac:(lia)
      ltac:(unfold tnum_trailing; lia)); lia)) as Heq.
  rewrite Hmod in Heq. lia.
Qed.

Theorem tnum_mul_low_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_low w a b) (wmul w x y).
Proof.
  intros w a b x y Ha Hb.
  destruct (tnum_trailing_factor w a x Ha) as [qa Hx].
  destruct (tnum_trailing_factor w b y Hb) as [qb Hy].
  pose proof (tnum_ctz_range w (tnum_wnot w (zeros a))) as Hra.
  pose proof (tnum_ctz_range w (tnum_wnot w (zeros b))) as Hrb.
  change (0 <= tnum_trailing w a <= Zpos w) in Hra.
  change (0 <= tnum_trailing w b <= Zpos w) in Hrb.
  apply tnum_gamma_bits. split; intros i Hi Hbit.
  - cbn [tnum_mul_low zeros] in Hbit. rewrite tnum_wrap_agrees, tnum_wrap_bit in Hbit by exact Hi.
    assert (Hlow : i < tnum_trailing w a + tnum_trailing w b).
    { destruct (Z_lt_ge_dec i (tnum_trailing w a + tnum_trailing w b)); [assumption|].
      rewrite Z.ones_spec_high in Hbit by lia. discriminate. }
    rewrite wmul_value, tnum_wrap_bit by exact Hi. rewrite Hx, Hy.
    replace (qa * 2 ^ tnum_trailing w a * (qb * 2 ^ tnum_trailing w b)) with
      ((qa * qb) * 2 ^ (tnum_trailing w a + tnum_trailing w b)) by
      (rewrite Z.pow_add_r by lia; ring).
    apply Z.mul_pow2_bits_low. exact Hlow.
  - cbn [tnum_mul_low ones] in Hbit. rewrite Z.bits_0 in Hbit. discriminate.
Qed.

Theorem tnum_mul_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_mul.
  destruct (tnum_constant w a) as [ca|] eqn:Hca,
    (tnum_constant w b) as [cb|] eqn:Hcb; try now apply tnum_mul_low_sound.
  rewrite (tnum_constant_value w a x ca Hx Ha Hca),
    (tnum_constant_value w b y cb Hy Hb Hcb).
  rewrite <- (wrap_id w (wmul w ca cb) (word_fun2_is_word bvmul BMul w ca cb eq_refl))
    at 2. apply tnum_const_sound.
Qed.

Lemma tnum_mul_prefix : forall y i, 0 <= i ->
  y mod 2 ^ (i + 1) = y mod 2 ^ i + Z.b2z (Z.testbit y i) * 2 ^ i.
Proof.
  intros y i Hi.
  pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) Hi) as Hpower.
  destruct (Z.testbit_spec y i Hi) as [l [h [Hl Heq]]].
  assert (Hlow : y mod 2 ^ i = l).
  { symmetry. apply Z.mod_unique with (q := Z.b2z (Z.testbit y i) + 2 * h).
    - left. exact Hl.
    - nia. }
  rewrite Hlow. symmetry. apply Z.mod_unique with (q := h).
  - left. rewrite Z.pow_add_r, Z.pow_1_r by lia.
    destruct (Z.testbit y i); cbn [Z.b2z]; lia.
  - rewrite Z.pow_add_r, Z.pow_1_r by lia. nia.
Qed.

Lemma tnum_mul_partial_add : forall w x y i, 0 <= i < Zpos w -> is_word w x ->
  wrap w (x * (y mod 2 ^ (i + 1))) =
    if Z.testbit y i then
      wadd w (wrap w (x * (y mod 2 ^ i))) (tnum_shl_scalar_value w i x)
    else wrap w (x * (y mod 2 ^ i)).
Proof.
  intros w x y i Hi Hx. rewrite tnum_mul_prefix by lia.
  destruct (Z.testbit y i); cbn [Z.b2z].
  - unfold tnum_shl_scalar_value. rewrite tnum_shl_value_agrees by lia. rewrite Z.min_l by lia.
    rewrite <- (wmul_wshl w x i Hx Hi).
    rewrite wadd_value, wmul_value, <- wrap_add. f_equal. ring.
  - f_equal. ring.
Qed.

Lemma tnum_mul_step_sound : forall w a b x y i r,
  0 <= i < Zpos w -> is_word w x -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w r (wrap w (x * (y mod 2 ^ i))) ->
  match tnum_mul_stage_step w a b (i, r) with
  | inl (j, q) => j = i + 1 /\ tnum_gamma w q (wrap w (x * (y mod 2 ^ (i + 1))))
  | inr _ => False
  end.
Proof.
  intros w a b x y i r Hi Hx Ha Hb Hr.
  pose proof (tnum_shl_scalar_sound w i a x ltac:(lia) Hx Ha) as Hshift.
  pose proof (tnum_add_sound w r _ _ _ Hr Hshift) as Hsum.
  apply tnum_gamma_bits in Hb. destruct Hb as [Hz Ho].
  change (Z.succ i = i + 1 /\
    tnum_gamma w
      (if Z.testbit (zeros b) i then r else
        if Z.testbit (ones b) i then tnum_add w r (tnum_shl_scalar w i a)
        else tnum_join w r (tnum_add w r (tnum_shl_scalar w i a)))
      (wrap w (x * (y mod 2 ^ (i + 1))))).
  split; [lia|]. rewrite tnum_mul_partial_add by assumption.
  destruct (Z.testbit (zeros b) i) eqn:Hbz.
  - rewrite (Hz i Hi Hbz). exact Hr.
  - destruct (Z.testbit (ones b) i) eqn:Hbo.
    + rewrite (Ho i Hi Hbo). exact Hsum.
    + apply tnum_join_sound. destruct (Z.testbit y i); auto.
Qed.

Lemma tnum_mul_runs_index : forall w a b n s result,
  tnum_runs (tnum_mul_stage_step w a b) n s result ->
  match result with
  | inl s' => fst s' = fst s + Z.of_nat n
  | inr _ => False
  end.
Proof.
  intros w a b n s result Hrun.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH].
  - cbn. lia.
  - destruct s as [i q]. discriminate Hstop.
  - destruct s as [i q], next as [j q']. injection Hnext as Hj Hq.
    cbn [fst] in Hj. destruct result as [[k q'']|r]; [|exact IH].
    cbn [fst] in *. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma tnum_mul_runs_sound : forall w a b x y,
  is_word w x -> tnum_gamma w a x -> tnum_gamma w b y ->
  forall n s result, tnum_runs (tnum_mul_stage_step w a b) n s result ->
  0 <= fst s -> fst s + Z.of_nat n <= Zpos w ->
  tnum_gamma w (snd s) (wrap w (x * (y mod 2 ^ fst s))) ->
  match result with
  | inl s' => tnum_gamma w (snd s') (wrap w (x * (y mod 2 ^ fst s')))
  | inr _ => False
  end.
Proof.
  intros w a b x y Hx Ha Hb n s result Hrun.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH];
    intros Hnonneg Hbound Hgamma.
  - exact Hgamma.
  - destruct s as [i q]. discriminate Hstop.
  - destruct s as [i q], next as [j q']. cbn [fst snd] in *.
    pose proof (tnum_mul_step_sound w a b x y i q ltac:(lia) Hx Ha Hb Hgamma) as Hstep.
    rewrite Hnext in Hstep. cbn [fst snd] in Hstep. destruct Hstep as [Hj Hq].
    apply IH; rewrite ?Hj; try lia.
    exact Hq.
Qed.

Theorem tnum_mul_stages_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_stages w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_mul_stages.
  set (a' := tnum_normalise w a). set (b' := tnum_normalise w b).
  assert (Ha' : tnum_gamma w a' x) by (now apply tnum_normalise_sound).
  assert (Hb' : tnum_gamma w b' y) by (now apply tnum_normalise_sound).
  rewrite (tnum_empty_sound w a' x Ha'), (tnum_empty_sound w b' y Hb').
  cbn [orb].
  pose proof (tnum_loop_runs _ _ (tnum_mul_stage_step w a' b')
    (N.pos w) (0, tnum_const w 0)) as Hrun.
  pose proof (tnum_mul_runs_index w a' b' _ _ _ Hrun) as Hindex.
  assert (Hzero : tnum_gamma w (tnum_const w 0) (wrap w (x * (y mod 2 ^ 0)))).
  { rewrite Z.pow_0_r, Z.mod_1_r, Z.mul_0_r. apply tnum_const_sound. }
  pose proof (tnum_mul_runs_sound w a' b' x y Hx Ha' Hb' _ _ _ Hrun
    ltac:(cbn; lia) ltac:(cbn; rewrite positive_nat_Z; lia) Hzero) as Hsound.
  destruct (loopN (tnum_mul_stage_step w a' b') (N.pos w) (0, tnum_const w 0))
    as [[i r]|r]; [|contradiction].
  cbn [fst snd N.to_nat] in Hindex, Hsound |- *.
  rewrite positive_nat_Z, Z.add_0_l in Hindex. subst i.
  rewrite <- modulus_value, (Z.mod_small y (modulus w) Hy) in Hsound.
  rewrite wmul_value. exact Hsound.
Qed.

Theorem tnum_mul_stage_bound : forall w a b, 0 <= tnum_mul_stage_count w a b <= Zpos w.
Proof.
  intros w a b. unfold tnum_mul_stage_count.
  destruct (tnum_empty w a || tnum_empty w b); [lia|].
  pose proof (tnum_loop_runs _ _ (tnum_mul_stage_step w a b)
    (N.pos w) (0, tnum_const w 0)) as Hrun.
  pose proof (tnum_mul_runs_index w a b _ _ _ Hrun) as Hindex.
  destruct (loopN (tnum_mul_stage_step w a b) (N.pos w) (0, tnum_const w 0))
    as [[i r]|r]; [|contradiction].
  cbn [fst N.to_nat] in Hindex |- *. rewrite positive_nat_Z in Hindex. lia.
Qed.

Lemma tnum_uncertain_sound : forall w m x,
  Z.land x m = x -> tnum_gamma w (tnum_uncertain w m) x.
Proof.
  intros w m x Hsub. apply tnum_gamma_bits. split; intros i Hi Hbit.
  - change (Z.testbit (tnum_wnot w m) i = true) in Hbit.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit in Hbit by exact Hi. apply negb_true_iff in Hbit.
    apply (f_equal (fun z => Z.testbit z i)) in Hsub.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.land_spec, Hbit, andb_false_r in Hsub. now symmetry.
  - change (Z.testbit 0 i = true) in Hbit. now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.bits_0 in Hbit.
Qed.

Lemma tnum_uncertain_zero : forall w m, tnum_gamma w (tnum_uncertain w m) 0.
Proof.
  intros w m. apply tnum_uncertain_sound. apply Z.land_0_l.
Qed.

Lemma tnum_uncertain_value : forall w a x,
  tnum_gamma w a x ->
  tnum_gamma w (tnum_uncertain w (wor w (tnum_min w a) (tnum_mask w a))) x.
Proof.
  intros w a x Ha. apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
  apply tnum_gamma_bits. split; intros i Hi Hbit.
  2: { change (Z.testbit 0 i = true) in Hbit. now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.bits_0 in Hbit. }
  change (Z.testbit (tnum_wnot w (wor w (tnum_min w a) (tnum_mask w a))) i = true) in Hbit.
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit, tnum_or_bit, tnum_mask_bit in Hbit by exact Hi.
  unfold tnum_min in Hbit. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_wrap_bit in Hbit by exact Hi.
  specialize (Hz i Hi). specialize (Ho i Hi).
  destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
    cbn in *; intuition discriminate.
Qed.

Lemma tnum_mul_residual_step : forall w a b x y i,
  0 <= i < Zpos w ->
  tnum_mul_residual w a b x y (i + 1) =
    tnum_mul_residual w a b x y i +
      (x * Z.b2z (Z.testbit y i) -
        tnum_min w a * Z.b2z (Z.testbit (ones b) i)) * 2 ^ i.
Proof.
  intros w a b x y i Hi. unfold tnum_mul_residual.
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !tnum_mul_prefix by lia.
  assert (Hbit : Z.testbit (tnum_min w b) i = Z.testbit (ones b) i)
    by (unfold tnum_min; rewrite tnum_wrap_agrees; apply tnum_wrap_bit; exact Hi).
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hbit. ring.
Qed.

Lemma tnum_shift_clear : forall z i j,
  0 <= i -> i <= j -> Z.shiftr z i = 0 -> Z.testbit z j = false.
Proof.
  intros z i j Hi Hj Hzero.
  apply (f_equal (fun x => Z.testbit x (j - i))) in Hzero.
  rewrite Z.shiftr_spec, Z.bits_0 in Hzero by lia.
  now replace (j - i + i) with j in Hzero by ring.
Qed.

Lemma tnum_low_complete : forall z i,
  0 <= i -> (forall j, i <= j -> Z.testbit z j = false) -> z mod 2 ^ i = z.
Proof.
  intros z i Hi Hhigh. apply Z.bits_inj'. intros j Hj.
  destruct (Z_lt_ge_dec j i) as [Hlow|Hge].
  - now rewrite Z.mod_pow2_bits_low.
  - rewrite Z.mod_pow2_bits_high by lia. symmetry. apply Hhigh. lia.
Qed.

Lemma tnum_mul_acc_done_sound : forall w b y i,
  is_word w y -> tnum_gamma w b y -> 0 <= i ->
  tnum_mul_acc_done w b i = true ->
  y mod 2 ^ i = y /\ tnum_min w b mod 2 ^ i = tnum_min w b.
Proof.
  intros w b y i Hy Hb Hi Hdone. unfold tnum_mul_acc_done in Hdone.
  apply andb_true_iff in Hdone as [Hv Hm]. apply Z.eqb_eq in Hv, Hm.
  apply tnum_gamma_bits in Hb. destruct Hb as [Hz Ho]. split; apply tnum_low_complete;
    try exact Hi.
  - intros j Hj. destruct (Z_lt_ge_dec j (Zpos w)) as [Hlow|Hhigh].
    + pose proof (tnum_shift_clear _ i j Hi Hj Hv) as Hvbit.
      pose proof (tnum_shift_clear _ i j Hi Hj Hm) as Hmbit.
      unfold tnum_min in Hvbit. rewrite tnum_wrap_agrees, tnum_wrap_bit in Hvbit by lia.
      rewrite tnum_mask_bit in Hmbit by lia.
      specialize (Hz j ltac:(lia)). specialize (Ho j ltac:(lia)).
      destruct (Z.testbit (zeros b) j), (Z.testbit (ones b) j), (Z.testbit y j);
        cbn in *; intuition discriminate.
    + apply (word_bits_high w y j Hy). lia.
  - intros j Hj. now apply (tnum_shift_clear _ i j Hi Hj Hv).
Qed.

Lemma tnum_mul_acc_increment : forall w a b x y i r q delta,
  0 <= i < Zpos w -> is_word w delta ->
  tnum_gamma w r (wrap w (tnum_mul_residual w a b x y i)) ->
  tnum_gamma w q delta ->
  tnum_gamma w (tnum_add w r (tnum_shl_scalar w i q))
    (wrap w (tnum_mul_residual w a b x y i + delta * 2 ^ i)).
Proof.
  intros w a b x y i r q delta Hi Hdelta Hr Hq.
  pose proof (tnum_add_sound w r (tnum_shl_scalar w i q) _ _
    Hr (tnum_shl_scalar_sound w i q delta ltac:(lia) Hdelta Hq)) as Hsum.
  unfold tnum_shl_scalar_value in Hsum. rewrite tnum_shl_value_agrees in Hsum by lia. rewrite Z.min_l in Hsum by lia.
  rewrite <- (wmul_wshl w delta i Hdelta Hi), wadd_value, wmul_value,
    <- wrap_add in Hsum. exact Hsum.
Qed.

Lemma tnum_mul_acc_next : forall w a b x y i r,
  0 <= i < Zpos w -> is_word w x -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w r (wrap w (tnum_mul_residual w a b x y i)) ->
  tnum_gamma w
    (if Z.testbit (zeros b) i then r else
      let m := if Z.testbit (ones b) i then tnum_mask w a
        else wor w (tnum_min w a) (tnum_mask w a) in
      tnum_add w r (tnum_shl_scalar w i (tnum_uncertain w m)))
    (wrap w (tnum_mul_residual w a b x y (i + 1))).
Proof.
  intros w a b x y i r Hi Hx Ha Hb Hr.
  destruct (tnum_decompose w a x Hx Ha) as [c [Hsub Hxc]].
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hbounds.
  pose proof (tnum_min_word w a) as Hvalue.
  apply tnum_gamma_bits in Hb. destruct Hb as [Hz Ho].
  rewrite tnum_mul_residual_step by exact Hi.
  destruct (Z.testbit (zeros b) i) eqn:Hbz.
  - rewrite (Hz i Hi Hbz).
    assert (Hbo : Z.testbit (ones b) i = false).
    { destruct (Z.testbit (ones b) i) eqn:Hbo; [|reflexivity].
      specialize (Ho i Hi Hbo). specialize (Hz i Hi Hbz). congruence. }
    rewrite Hbo. cbn [Z.b2z]. replace (_ + (x * 0 - _ * 0) * _) with
      (tnum_mul_residual w a b x y i) by ring. exact Hr.
  - destruct (Z.testbit (ones b) i) eqn:Hbo.
    + rewrite (Ho i Hi Hbo). cbn [Z.b2z].
      replace (x * 1 - tnum_min w a * 1) with c by lia.
      apply tnum_mul_acc_increment; try assumption.
      * change (0 <= tnum_min w a < modulus w) in Hvalue.
        unfold is_word in *. lia.
      * now apply tnum_uncertain_sound.
    + cbn [Z.b2z]. destruct (Z.testbit y i).
      * cbn [Z.b2z]. replace (x * 1 - tnum_min w a * 0) with x by ring.
        apply tnum_mul_acc_increment; try assumption. now apply tnum_uncertain_value.
      * cbn [Z.b2z]. replace (x * 0 - tnum_min w a * 0) with 0 by ring.
        apply tnum_mul_acc_increment; try assumption.
        -- apply zero_is_word.
        -- apply tnum_uncertain_zero.
Qed.

Theorem tnum_mul_acc_runs_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  forall n s result, tnum_runs (tnum_mul_acc_step w a b) n s result ->
  0 <= fst s -> fst s + Z.of_nat n <= Zpos w ->
  tnum_gamma w (snd s) (wrap w (tnum_mul_residual w a b x y (fst s))) ->
  match result with
  | inl s' =>
    fst s' = fst s + Z.of_nat n /\
    tnum_gamma w (snd s') (wrap w (tnum_mul_residual w a b x y (fst s')))
  | inr r =>
    tnum_gamma w r (wrap w (x * y - tnum_min w a * tnum_min w b))
  end.
Proof.
  intros w a b x y Hx Hy Ha Hb n s result Hrun.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH];
    intros Hi Hbound Hr.
  - cbn. split; [lia|exact Hr].
  - destruct s as [i q]. cbn [fst snd] in *.
    cbn [tnum_mul_acc_step] in Hstop.
    destruct (tnum_mul_acc_done w b i) eqn:Hdone; [|discriminate].
    injection Hstop as <-.
    destruct (tnum_mul_acc_done_sound w b y i Hy Hb Hi Hdone) as [Hlow Hvlow].
    unfold tnum_mul_residual in Hr. now rewrite Hlow, Hvlow in Hr.
  - destruct s as [i q], next as [j q']. cbn [fst snd] in *.
    cbn [tnum_mul_acc_step] in Hnext.
    destruct (tnum_mul_acc_done w b i) eqn:Hdone; [discriminate|].
    injection Hnext as Hj Hq. subst j q'.
    rewrite tnum_wor_agrees in IH.
    specialize (IH ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hbound; lia)
      (tnum_mul_acc_next w a b x y i q ltac:(rewrite Nat2Z.inj_succ in Hbound; lia)
        Hx Ha Hb Hr)).
    destruct result as [[k q'']|r]; [|exact IH]. cbn [fst snd] in *.
    destruct IH as [Hk Hgamma]. split; [rewrite Nat2Z.inj_succ; lia|exact Hgamma].
Qed.

Theorem tnum_mul_acc_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_acc w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_mul_acc.
  set (a' := tnum_normalise w a). set (b' := tnum_normalise w b).
  assert (Ha' : tnum_gamma w a' x) by (now apply tnum_normalise_sound).
  assert (Hb' : tnum_gamma w b' y) by (now apply tnum_normalise_sound).
  rewrite (tnum_empty_sound w a' x Ha'), (tnum_empty_sound w b' y Hb').
  cbn [orb].
  pose proof (tnum_loop_runs _ _ (tnum_mul_acc_step w a' b')
    (N.pos w) (0, tnum_const w 0)) as Hrun.
  assert (Hzero : tnum_gamma w (tnum_const w 0)
    (wrap w (tnum_mul_residual w a' b' x y 0))).
  { unfold tnum_mul_residual. rewrite !Z.mod_1_r, !Z.mul_0_r, Z.sub_0_r.
    apply tnum_const_sound. }
  pose proof (tnum_mul_acc_runs_sound w a' b' x y Hx Hy Ha' Hb' _ _ _ Hrun
    ltac:(cbn; lia) ltac:(cbn; rewrite positive_nat_Z; lia) Hzero) as Hsound.
  assert (Hmask : tnum_gamma w
    (match loopN (tnum_mul_acc_step w a' b') (N.pos w) (0, tnum_const w 0) with
     | inl s => snd s
     | inr r => r
     end) (wrap w (x * y - tnum_min w a' * tnum_min w b'))).
  { destruct (loopN (tnum_mul_acc_step w a' b') (N.pos w) (0, tnum_const w 0))
      as [[i r]|r]; [|exact Hsound].
    cbn [fst snd N.to_nat] in Hsound |- *. destruct Hsound as [Hi Hgamma].
    rewrite positive_nat_Z, Z.add_0_l in Hi. subst i.
    unfold tnum_mul_residual in Hgamma. rewrite <- modulus_value,
      (Z.mod_small y (modulus w) Hy),
      (Z.mod_small (tnum_min w b') (modulus w) (tnum_min_word w _)) in Hgamma.
    exact Hgamma. }
  pose proof (tnum_add_sound w
    (tnum_const w (wmul w (tnum_min w a') (tnum_min w b'))) _ _ _
    (tnum_const_sound w (wmul w (tnum_min w a') (tnum_min w b'))) Hmask) as Hsum.
  rewrite wadd_value, wmul_value, wrap_wrap, <- wrap_add in Hsum.
  replace (tnum_min w a' * tnum_min w b' +
    (x * y - tnum_min w a' * tnum_min w b')) with (x * y) in Hsum by ring.
  rewrite wmul_value. exact Hsum.
Qed.

Theorem tnum_mul_with_sound : forall choice w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_with choice w a b) (wmul w x y).
Proof.
  intros choice w a b x y Hx Hy Ha Hb. destruct choice; cbn [tnum_mul_with].
  - now apply tnum_mul_sound.
  - now apply tnum_mul_stages_sound.
  - now apply tnum_mul_acc_sound.
  - apply tnum_meet_sound.
    + now apply tnum_mul_stages_sound.
    + now apply tnum_mul_acc_sound.
Qed.

Theorem tnum_mul_both_gamma : forall w a b z,
  tnum_gamma w (tnum_mul_with MulBoth w a b) z <->
  tnum_gamma w (tnum_mul_with MulStages w a b) z /\
    tnum_gamma w (tnum_mul_with MulAcc w a b) z.
Proof.
  intros w a b z. cbn [tnum_mul_with]. apply tnum_meet_gamma.
Qed.

Lemma tnum_equiv_leb : forall w a b c,
  tnum_equiv w a b ->
  (tnum_leb w a c = true <-> tnum_leb w b c = true).
Proof.
  intros w a b c Heq. pose proof (proj1 (tnum_equiv_bits w a b) Heq) as Hbits.
  rewrite !tnum_leb_bits. split; intros [Hz Ho]; split; intros i Hi Hbit;
    specialize (Hbits i Hi) as [Heqz Heqo];
    first [rewrite <- Heqz; now apply Hz|rewrite <- Heqo; now apply Ho|
      rewrite Heqz; now apply Hz|rewrite Heqo; now apply Ho].
Qed.

Lemma tnum_join_leb : forall w a b c,
  tnum_leb w (tnum_join w a b) c = true <->
  tnum_leb w a c = true /\ tnum_leb w b c = true.
Proof.
  intros w a b c. rewrite !tnum_leb_bits. split.
  - intros [Hz Ho]. split; split; intros i Hi Hbit.
    + specialize (Hz i Hi Hbit).
      rewrite (proj1 (tnum_join_bits w a b i Hi)) in Hz.
      now apply andb_true_iff in Hz as [Hz _].
    + specialize (Ho i Hi Hbit).
      rewrite (proj2 (tnum_join_bits w a b i Hi)) in Ho.
      now apply andb_true_iff in Ho as [Ho _].
    + specialize (Hz i Hi Hbit).
      rewrite (proj1 (tnum_join_bits w a b i Hi)) in Hz.
      now apply andb_true_iff in Hz as [_ Hz].
    + specialize (Ho i Hi Hbit).
      rewrite (proj2 (tnum_join_bits w a b i Hi)) in Ho.
      now apply andb_true_iff in Ho as [_ Ho].
  - intros [[Haz Hao] [Hbz Hbo]]. split; intros i Hi Hbit.
    + rewrite (proj1 (tnum_join_bits w a b i Hi)). apply andb_true_iff. auto.
    + rewrite (proj2 (tnum_join_bits w a b i Hi)). apply andb_true_iff. auto.
Qed.

Lemma tnum_map_join : forall sw rw f a b,
  tnum_bit_copy sw rw f ->
  tnum_equiv rw (tnum_map sw rw f (tnum_join sw a b))
    (tnum_join rw (tnum_map sw rw f a) (tnum_map sw rw f b)).
Proof.
  intros sw rw f a b Hcopy. apply tnum_equiv_bits. intros i Hi.
  destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]];
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (proj1 (tnum_join_bits rw _ _ i Hi)),
      (proj2 (tnum_join_bits rw _ _ i Hi));
    cbn [tnum_map zeros ones]; rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !tnum_not_bit, !tnum_wrap_bit by exact Hi.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !Hclear by first [apply tnum_max_word|apply tnum_min_word|apply wnot_is_word|apply wrap_is_word]. auto.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !Hsource by first [apply tnum_max_word|apply tnum_min_word|apply wnot_is_word|apply wrap_is_word].
    unfold tnum_min, tnum_max. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !tnum_not_bit, !tnum_wrap_bit by exact Hj.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (proj1 (tnum_join_bits sw a b j Hj)),
      (proj2 (tnum_join_bits sw a b j Hj)), !negb_involutive. auto.
Qed.

Lemma tnum_map_composition : forall sw mw rw f g a,
  tnum_bit_copy mw rw g -> (forall x, is_word sw x -> is_word mw (f x)) ->
  tnum_equiv rw (tnum_map mw rw g (tnum_map sw mw f a))
    (tnum_map sw rw (fun x => g (f x)) a).
Proof.
  intros sw mw rw f g a Hcopy Hword. apply tnum_equiv_bits. intros i Hi.
  destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]];
    cbn [tnum_map zeros ones]; rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !tnum_not_bit, !tnum_wrap_bit by exact Hi.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !Hclear by first [apply tnum_max_word|apply tnum_min_word|apply wnot_is_word|apply wrap_is_word|apply Hword;
      first [apply tnum_max_word|apply tnum_min_word|apply wnot_is_word|apply wrap_is_word]]. auto.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !Hsource by first [apply tnum_max_word|apply tnum_min_word|apply wnot_is_word|apply wrap_is_word|apply Hword;
      first [apply tnum_max_word|apply tnum_min_word|apply wnot_is_word|apply wrap_is_word]].
    unfold tnum_min, tnum_max, tnum_map. cbn [zeros ones].
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !tnum_not_bit, !tnum_wrap_bit by exact Hj. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, negb_involutive.
    unfold tnum_min, tnum_max. rewrite ?tnum_wrap_agrees, ?tnum_wnot_agrees. auto.
Qed.

Lemma tnum_source_composition : forall o w h k i,
  0 <= h -> 0 <= k -> 0 <= i < Zpos w ->
  (match tnum_source o w k i with
   | Some j => tnum_source o w h j
   | None => None
   end) = tnum_source o w (h + k) i.
Proof.
  intros o w h k i Hh Hk Hi. destruct o; cbn [tnum_source]; try reflexivity.
  - destruct (k <=? i) eqn:Hki.
    + apply Z.leb_le in Hki. destruct (h <=? i - k) eqn:Hhi.
      * apply Z.leb_le in Hhi. rewrite (proj2 (Z.leb_le (h + k) i)) by lia. f_equal. lia.
      * apply Z.leb_gt in Hhi. rewrite (proj2 (Z.leb_gt (h + k) i)) by lia. reflexivity.
    + apply Z.leb_gt in Hki. rewrite (proj2 (Z.leb_gt (h + k) i)) by lia. reflexivity.
  - destruct (i + k <? Zpos w) eqn:Hki.
    + apply Z.ltb_lt in Hki. destruct (i + k + h <? Zpos w) eqn:Hhi.
      * apply Z.ltb_lt in Hhi. rewrite (proj2 (Z.ltb_lt (i + (h + k)) (Zpos w)))
          by lia. f_equal. lia.
      * apply Z.ltb_ge in Hhi. rewrite (proj2 (Z.ltb_ge (i + (h + k)) (Zpos w)))
          by lia. reflexivity.
    + apply Z.ltb_ge in Hki. rewrite (proj2 (Z.ltb_ge (i + (h + k)) (Zpos w)))
        by lia. reflexivity.
  - f_equal. lia.
  - rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia. f_equal. f_equal. ring.
  - rewrite Zplus_mod, Z.mod_mod, <- Zplus_mod by lia. f_equal. f_equal. ring.
Qed.

Lemma tnum_scalar_value_composition : forall o w h k x,
  0 <= h -> 0 <= k -> is_word w x ->
  tnum_scalar_value o w k (tnum_scalar_value o w h x) =
  tnum_scalar_value o w (h + k) x.
Proof.
  intros o w h k x Hh Hk Hx. apply (word_ext w);
    [apply tnum_scalar_word|apply tnum_scalar_word|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite !tnum_scalar_bits by (try assumption; try apply tnum_scalar_word; lia).
    pose proof (tnum_source_composition o w h k i Hh Hk ltac:(lia)) as Hcomp.
    destruct (tnum_source o w k i) as [j|] eqn:Hsource.
    + rewrite tnum_scalar_bits by
        (try assumption; exact (tnum_source_range o w k i j Hk ltac:(lia) Hsource)).
      cbn in Hcomp. now rewrite <- Hcomp.
    + cbn in Hcomp. now rewrite <- Hcomp.
  - rewrite !(word_bits_high w) by (try apply tnum_scalar_word; lia). reflexivity.
Qed.

Lemma tnum_scalar_composition : forall o w h k a,
  0 <= h -> 0 <= k ->
  tnum_equiv w (tnum_scalar o w k (tnum_scalar o w h a))
    (tnum_scalar o w (h + k) a).
Proof.
  intros o w h k a Hh Hk.
  pose proof (tnum_map_composition w w w (tnum_scalar_value o w h)
    (tnum_scalar_value o w k) a (tnum_scalar_copy o w k Hk)
    (fun x _ => tnum_scalar_word o w h x)) as Hcomp.
  assert (Hmap : tnum_map w w
    (fun x => tnum_scalar_value o w k (tnum_scalar_value o w h x)) a =
      tnum_scalar o w (h + k) a).
  { unfold tnum_scalar, tnum_map.
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !tnum_scalar_value_composition by
      (try assumption; first [apply tnum_max_word|apply tnum_min_word|apply wnot_is_word|apply wrap_is_word]). reflexivity. }
  now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Hmap in Hcomp.
Qed.

Lemma tnum_scalar_zero : forall o w a, tnum_equiv w (tnum_scalar o w 0 a) a.
Proof.
  intros o w a. apply tnum_equiv_bits. intros i Hi.
  assert (Hsource : tnum_source o w 0 i = Some i).
  { destruct o; cbn [tnum_source]; try reflexivity.
    - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, (proj2 (Z.leb_le 0 i)) by lia. now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.sub_0_r.
    - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.add_0_r, (proj2 (Z.ltb_lt i (Zpos w))) by lia. reflexivity.
    - change (Some (Z.min (i + 0) (Zpos w - 1)) = Some i). f_equal. lia.
    - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.sub_0_r, Z.mod_small by exact Hi. reflexivity.
    - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.add_0_r, Z.mod_small by exact Hi. reflexivity. }
  unfold tnum_scalar, tnum_map. cbn [zeros ones].
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit, tnum_wrap_bit by exact Hi.
  rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, !tnum_scalar_bits, Hsource by
    (try lia; try exact Hi; first [apply tnum_max_word|apply tnum_min_word|apply wnot_is_word|apply wrap_is_word]).
  unfold tnum_min, tnum_max. rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_not_bit, tnum_wrap_bit by exact Hi.
  now rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, negb_involutive.
Qed.

Lemma tnum_scalar_period : forall o w h k a,
  tnum_rotation o = true -> h mod Zpos w = k mod Zpos w ->
  tnum_scalar o w h a = tnum_scalar o w k a.
Proof.
  intros o w h k a Hrot Hmod. unfold tnum_scalar, tnum_scalar_value.
  destruct o; cbn [tnum_rotation] in Hrot; try discriminate.
  - now rewrite Hmod.
  - assert (Hneg : (-h) mod Zpos w = (-k) mod Zpos w).
    { replace (-h) with (0 - h) by ring. replace (-k) with (0 - k) by ring.
      rewrite (Zminus_mod 0 h), (Zminus_mod 0 k) by lia. now rewrite Hmod. }
    now rewrite Hneg.
Qed.

Lemma tnum_stride_nonnegative : forall o w d, 0 <= d -> 0 <= tnum_stride o w d.
Proof.
  intros o w d Hd. unfold tnum_stride. destruct (tnum_rotation o);
    [apply Z.mod_pos_bound; lia|lia].
Qed.

Lemma tnum_stride_offset_agrees : forall o w d c b a,
  tnum_scalar o w (b + tnum_stride o w d * c) a =
    tnum_scalar o w (b + d * (2 * c)) a.
Proof.
  intros o w d c b a. unfold tnum_stride. destruct (tnum_rotation o) eqn:Hrot.
  - apply tnum_scalar_period; [exact Hrot|].
    rewrite Zplus_mod, Zmult_mod, Z.mod_mod, <- Zmult_mod, <- Zplus_mod by lia.
    f_equal. ring.
  - f_equal. ring.
Qed.

Lemma tnum_stride_agrees : forall o w d c a,
  tnum_scalar o w (tnum_stride o w d * c) a = tnum_scalar o w (d * (2 * c)) a.
Proof.
  intros o w d c a.
  pose proof (tnum_stride_offset_agrees o w d c 0 a) as H.
  now rewrite !Z.add_0_l in H.
Qed.

Lemma tnum_choices_nonnegative : forall p c, tnum_choices p c -> 0 <= c.
Proof.
  intro p. induction p as [p IH|p IH|]; intros c Hchoice; cbn [tnum_choices] in Hchoice.
  - destruct Hchoice as [t [Ht [Hc|Hc]]]; subst c; specialize (IH t Ht); lia.
  - destruct Hchoice as [t [Ht ->]]. specialize (IH t Ht). lia.
  - destruct Hchoice as [Hc|Hc]; subst c; lia.
Qed.

Theorem tnum_expand_equation : forall o w p d r,
  tnum_expand o w p d r =
  match p with
  | xH => tnum_join w r (tnum_scalar o w d r)
  | xO q => tnum_expand o w q (tnum_stride o w d) r
  | xI q => tnum_expand o w q (tnum_stride o w d)
      (tnum_join w r (tnum_scalar o w d r))
  end.
Proof.
  intros o w p d r. destruct p; reflexivity.
Qed.

Lemma tnum_scalar_stage_leb : forall o w d k r target,
  0 <= d -> 0 <= k ->
  (tnum_leb w (tnum_scalar o w k
     (tnum_join w r (tnum_scalar o w d r))) target = true <->
   tnum_leb w (tnum_scalar o w k r) target = true /\
   tnum_leb w (tnum_scalar o w (d + k) r) target = true).
Proof.
  intros o w d k r target Hd Hk.
  assert (Hjoin : tnum_equiv w
    (tnum_scalar o w k (tnum_join w r (tnum_scalar o w d r)))
    (tnum_join w (tnum_scalar o w k r) (tnum_scalar o w k (tnum_scalar o w d r))))
    by (apply tnum_map_join; now apply tnum_scalar_copy).
  rewrite (tnum_equiv_leb w _ _ target Hjoin).
  rewrite tnum_join_leb.
  rewrite (tnum_equiv_leb w _ _ target (tnum_scalar_composition o w d k r Hd Hk)).
  reflexivity.
Qed.

Theorem tnum_expand_join : forall o w p d r target,
  0 <= d ->
  (tnum_leb w (tnum_expand o w p d r) target = true <->
   forall c, tnum_choices p c ->
     tnum_leb w (tnum_scalar o w (d * c) r) target = true).
Proof.
  intros o w p. induction p as [p IH|p IH|]; intros d r target Hd;
    rewrite tnum_expand_equation.
  - rewrite IH by (now apply tnum_stride_nonnegative).
    assert (Hstage : forall t, tnum_choices p t ->
      (tnum_leb w
        (tnum_scalar o w (tnum_stride o w d * t)
          (tnum_join w r (tnum_scalar o w d r))) target = true <->
       tnum_leb w (tnum_scalar o w (d * (2 * t)) r) target = true /\
       tnum_leb w (tnum_scalar o w (d * (2 * t + 1)) r) target = true)).
    { intros t Ht. pose proof (tnum_choices_nonnegative p t Ht) as Ht0.
      rewrite tnum_scalar_stage_leb by
        (try assumption; pose proof (tnum_stride_nonnegative o w d Hd); nia).
      rewrite tnum_stride_agrees, tnum_stride_offset_agrees.
      replace (d + d * (2 * t)) with (d * (2 * t + 1)) by ring. reflexivity. }
    split.
    + intros H c [t [Ht [Hc|Hc]]]; subst c; specialize (H t Ht);
        apply (Hstage t Ht) in H; tauto.
    + intros H t Ht. apply (Hstage t Ht). split; apply H; exists t; auto.
  - rewrite IH by (now apply tnum_stride_nonnegative). split.
    + intros H c [t [Ht ->]]. rewrite <- tnum_stride_agrees. now apply H.
    + intros H t Ht. rewrite tnum_stride_agrees. apply H. exists t. auto.
  - rewrite tnum_join_leb. split.
    + intros [Hr Hshift] c [-> | ->].
      * replace (d * 0) with 0 by ring.
        apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)). exact Hr.
      * now replace (d * 1) with d by ring.
    + intro H. split.
      * apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)).
        replace 0 with (d * 0) by ring. apply H. now left.
      * replace d with (d * 1) by ring. apply H. now right.
Qed.

Lemma tnum_land_div2 : forall c u,
  Z.land c u = c <->
  Z.land (c / 2) (u / 2) = c / 2 /\
    (Z.testbit c 0 = true -> Z.testbit u 0 = true).
Proof.
  intros c u. split.
  - intro Hland. split.
    + apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.div2_bits by exact Hi.
      apply (f_equal (fun z => Z.testbit z (Z.succ i))) in Hland.
      now rewrite Z.land_spec in Hland.
    + apply (f_equal (fun z => Z.testbit z 0)) in Hland.
      rewrite Z.land_spec in Hland. destruct (Z.testbit c 0), (Z.testbit u 0);
        cbn in *; congruence.
  - intros [Htail Hlow]. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hnonzero].
    + destruct (Z.testbit c 0), (Z.testbit u 0); cbn in *; intuition discriminate.
    + apply (f_equal (fun z => Z.testbit z (i - 1))) in Htail.
      rewrite Z.land_spec, !Z.div2_bits in Htail by lia.
      replace (Z.succ (i - 1)) with i in Htail by lia. exact Htail.
Qed.

Lemma tnum_double_div2 : forall t, (2 * t) / 2 = t /\ (2 * t + 1) / 2 = t.
Proof.
  intro t. split.
  - replace (2 * t) with (t * 2) by ring. apply Z.div_mul. lia.
  - replace (2 * t + 1) with (1 + t * 2) by ring.
    rewrite Z.div_add by lia. cbn. ring.
Qed.

Lemma tnum_choices_land : forall p c, tnum_choices p c <-> Z.land c (Zpos p) = c.
Proof.
  intro p. induction p as [p IH|p IH|]; intro c.
  - rewrite tnum_land_div2, (Pos2Z.inj_xI p).
    rewrite (proj2 (tnum_double_div2 (Zpos p))), Z.testbit_odd_0.
    cbn [tnum_choices]. split.
    + intros [t [Ht [-> | ->]]]; rewrite ?(proj1 (tnum_double_div2 t)),
        ?(proj2 (tnum_double_div2 t)); split; try reflexivity; now apply IH.
    + intros [Htail _]. apply IH in Htail. exists (c / 2). split; [exact Htail|].
      pose proof (Z.div2_odd c) as Hsplit. rewrite Z.div2_div in Hsplit.
      destruct (Z.odd c); cbn [Z.b2z] in Hsplit; [right|left]; lia.
  - rewrite tnum_land_div2, (Pos2Z.inj_xO p).
    rewrite (proj1 (tnum_double_div2 (Zpos p))), Z.testbit_even_0.
    cbn [tnum_choices]. split.
    + intros [t [Ht ->]]. rewrite (proj1 (tnum_double_div2 t)), Z.testbit_even_0.
      split; [now apply IH|discriminate].
    + intros [Htail Hlow]. apply IH in Htail. exists (c / 2). split; [exact Htail|].
      pose proof (Z.div2_odd c) as Hsplit. rewrite Z.div2_div, <- Z.bit0_odd in Hsplit.
      destruct (Z.testbit c 0); cbn [Z.b2z] in *;
        [specialize (Hlow eq_refl); discriminate|lia].
  - cbn [tnum_choices]. split.
    + intros [-> | ->]; reflexivity.
    + intro Hland. change (Z.land c (Z.ones 1) = c) in Hland.
      rewrite Z.land_ones in Hland by lia.
      pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as Hbounds.
      change (c mod 2 = c) in Hland. lia.
Qed.

Theorem tnum_expand_mask_join : forall o w u r target,
  0 <= u ->
  (tnum_leb w (tnum_expand_mask o w u r) target = true <->
   forall c, Z.land c u = c ->
     tnum_leb w (tnum_scalar o w c r) target = true).
Proof.
  intros o w [|p|p] r target Hu; [| |lia].
  - change (tnum_leb w (tnum_normalise w r) target = true <->
      forall c, Z.land c 0 = c ->
        tnum_leb w (tnum_scalar o w c r) target = true).
    assert (Hnorm : tnum_equiv w (tnum_normalise w r) r).
    { unfold tnum_equiv, tnum_normalise. cbn [zeros ones]. now rewrite !tnum_wrap_agrees, !wrap_wrap. }
    rewrite (tnum_equiv_leb w _ _ target Hnorm). split.
    + intros Hr c Hc. rewrite Z.land_0_r in Hc. subst c.
      apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)). exact Hr.
    + intro H. apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)).
      apply H. reflexivity.
  - change (tnum_leb w (tnum_expand o w p 1 r) target = true <->
      forall c, Z.land c (Zpos p) = c ->
        tnum_leb w (tnum_scalar o w c r) target = true).
    rewrite tnum_expand_join by lia. setoid_rewrite tnum_choices_land.
    split; intros H c Hc; specialize (H c Hc);
      replace (1 * c) with c in * by ring; exact H.
Qed.

Lemma tnum_expand_base_join : forall o w u base a target,
  0 <= u -> 0 <= base ->
  (tnum_leb w
     (tnum_expand_mask o w u (tnum_scalar o w base a)) target = true <->
   forall c, Z.land c u = c ->
     tnum_leb w (tnum_scalar o w (base + c) a) target = true).
Proof.
  intros o w u base a target Hu Hb. rewrite tnum_expand_mask_join by exact Hu.
  split; intros H c Hc;
    assert (Hnonneg : 0 <= c) by
      (rewrite <- Hc; apply Z.land_nonneg; right; exact Hu);
    specialize (H c Hc);
    apply (tnum_equiv_leb w _ _ target (tnum_scalar_composition o w base c a Hb Hnonneg));
    exact H.
Qed.

Lemma tnum_submask_word : forall w u c,
  is_word w u -> Z.land c u = c -> is_word w c.
Proof.
  intros w u c Hu Hsub. apply word_of_bits. intros i Hi.
  apply (f_equal (fun z => Z.testbit z i)) in Hsub.
  rewrite Z.land_spec, (word_bits_high w u i Hu Hi), andb_false_r in Hsub. now symmetry.
Qed.

Lemma tnum_submask_bound : forall w u c,
  is_word w u -> Z.land c u = c -> 0 <= c <= u.
Proof.
  intros w u c Hu Hsub. pose proof (tnum_submask_word w u c Hu Hsub) as Hc.
  split; [exact (proj1 Hc)|]. apply (tnum_bitwise_le w); try assumption.
  intros i Hi Hbit. apply (f_equal (fun z => Z.testbit z i)) in Hsub.
  rewrite Z.land_spec, Hbit in Hsub. cbn in Hsub. now symmetry.
Qed.

Lemma tnum_submask_mod : forall c u n,
  0 <= n -> Z.land c u = c ->
  Z.land (c mod 2 ^ n) (u mod 2 ^ n) = c mod 2 ^ n.
Proof.
  intros c u n Hn Hsub. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z_lt_ge_dec i n) as [Hlow|Hhigh].
  - rewrite !Z.mod_pow2_bits_low by exact Hlow.
    apply (f_equal (fun z => Z.testbit z i)) in Hsub. now rewrite Z.land_spec in Hsub.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma tnum_scalar_oversized : forall o w k a,
  tnum_rotation o = false -> Zpos w <= k ->
  tnum_scalar o w k a = tnum_scalar o w (Zpos w) a.
Proof.
  intros o w k a Hrot Hk. unfold tnum_scalar, tnum_scalar_value.
  destruct o; cbn [tnum_rotation] in Hrot; try discriminate; try reflexivity;
    rewrite !Z.min_r by lia; reflexivity.
Qed.

Lemma tnum_shift_cutoff_bound : forall w,
  0 <= tnum_shift_cutoff w /\ Zpos w <= 2 ^ tnum_shift_cutoff w.
Proof.
  intro w. unfold tnum_shift_cutoff, tnum_bitlen.
  destruct (Zpos w - 1 =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. cbn. lia.
  - apply Z.eqb_neq in Hz. pose proof (Z.log2_nonneg (Zpos w - 1)).
    pose proof (Z.log2_spec (Zpos w - 1) ltac:(lia)). lia.
Qed.

Theorem tnum_variable_raw_equation : forall o w a b,
  tnum_variable_raw o w a b =
  let base := tnum_min w b in
  let u := tnum_mask w b in
  let r := tnum_scalar o w base a in
  if tnum_rotation o then tnum_expand_mask o w u r else
  let cutoff := 2 ^ tnum_shift_cutoff w in
  let low := tnum_expand_mask o w (u mod cutoff) r in
  if u <? cutoff then low else tnum_join w low (tnum_scalar o w (Zpos w) a).
Proof.
  reflexivity.
Qed.

Theorem tnum_variable_raw_amount_bound : forall o w a b k,
  is_word w k -> tnum_gamma w b k ->
  tnum_leb w (tnum_scalar o w k a) (tnum_variable_raw o w a b) = true.
Proof.
  intros o w a b k Hk Hb. destruct (tnum_decompose w b k Hk Hb) as [c [Hc ->]].
  set (target := tnum_variable_raw o w a b).
  assert (Hself : tnum_leb w (tnum_variable_raw o w a b) target = true)
    by (apply tnum_leb_bits; auto).
  rewrite tnum_variable_raw_equation in Hself.
  cbn zeta in Hself.
  pose proof (tnum_min_word w b) as Hbase.
  pose proof (tnum_mask_word w b) as Hu.
  destruct (tnum_rotation o) eqn:Hrot.
  - apply (proj1 (tnum_expand_base_join o w _ _ a target (proj1 Hu) (proj1 Hbase))
      Hself c Hc).
  - pose proof (tnum_shift_cutoff_bound w) as [Hcut Hwidth].
    pose proof (tnum_submask_bound w _ c Hu Hc) as Hcbound.
    destruct (tnum_mask w b <? 2 ^ tnum_shift_cutoff w) eqn:Hhigh.
    + apply Z.ltb_lt in Hhigh. rewrite Z.mod_small in Hself by (unfold is_word in Hu; lia).
      apply (proj1 (tnum_expand_base_join o w _ _ a target (proj1 Hu) (proj1 Hbase))
        Hself c Hc).
    + apply tnum_join_leb in Hself as [Hsmall Hbig].
      destruct (c <? 2 ^ tnum_shift_cutoff w) eqn:Hcsmall.
      * apply Z.ltb_lt in Hcsmall.
        assert (Hpow : 0 < 2 ^ tnum_shift_cutoff w) by (apply Z.pow_pos_nonneg; lia).
        apply (proj1 (tnum_expand_base_join o w _ _ a target
          (proj1 (Z.mod_pos_bound _ _ Hpow)) (proj1 Hbase)) Hsmall).
        pose proof (tnum_submask_mod c (tnum_mask w b) (tnum_shift_cutoff w) Hcut Hc)
          as Hmod. now rewrite Z.mod_small in Hmod by lia.
      * apply Z.ltb_ge in Hcsmall.
        rewrite tnum_scalar_oversized by (try exact Hrot; unfold is_word in Hbase; lia).
        exact Hbig.
Qed.

Theorem tnum_variable_sound : forall o w f a b x k,
  tnum_shift_op o -> word_fun2 o = Some f ->
  is_word w x -> is_word w k -> tnum_gamma w a x -> tnum_gamma w b k ->
  tnum_gamma w (tnum_variable o w a b) (eval_binary_tag f w x k).
Proof.
  intros o w f a b x k Ho Hf Hx Hk Ha Hb.
  pose proof (proj2 (tnum_normalise_sound w a x) Ha) as Han.
  pose proof (proj2 (tnum_normalise_sound w b k) Hb) as Hbn.
  unfold tnum_variable.
  rewrite (tnum_empty_sound w _ x Han), (tnum_empty_sound w _ k Hbn).
  cbn [orb].
  eapply tnum_gamma_monotone;
    [apply (tnum_variable_raw_amount_bound o w _ _ k Hk Hbn)|].
  rewrite <- (tnum_scalar_agrees o w f k x Ho Hf Hk Hx).
  apply tnum_scalar_sound; try assumption. exact (proj1 Hk).
Qed.

Theorem tnum_order_sound : forall strict w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_order strict w a b)
    (if (if strict then x <? y else x <=? y) then 1 else 0).
Proof.
  intros strict w a b x y Hx Hy Ha Hb.
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hax.
  pose proof (tnum_unsigned_bounds w b y Hy Hb) as Hby.
  unfold tnum_order. destruct strict.
  - destruct (tnum_max w a <? tnum_min w b) eqn:Htrue.
    + apply Z.ltb_lt in Htrue. rewrite (proj2 (Z.ltb_lt x y)) by lia.
      exact (tnum_const_sound 1%positive 1).
    + destruct (tnum_max w b <=? tnum_min w a) eqn:Hfalse; [|apply tnum_top_sound].
      apply Z.leb_le in Hfalse. rewrite (proj2 (Z.ltb_ge x y)) by lia.
      exact (tnum_const_sound 1%positive 0).
  - destruct (tnum_max w a <=? tnum_min w b) eqn:Htrue.
    + apply Z.leb_le in Htrue. rewrite (proj2 (Z.leb_le x y)) by lia.
      exact (tnum_const_sound 1%positive 1).
    + destruct (tnum_max w b <? tnum_min w a) eqn:Hfalse; [|apply tnum_top_sound].
      apply Z.ltb_lt in Hfalse. rewrite (proj2 (Z.leb_gt x y)) by lia.
      exact (tnum_const_sound 1%positive 0).
Qed.

Theorem tnum_equal_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_equal w a b) (if x =? y then 1 else 0).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_equal.
  destruct (tnum_empty w (tnum_meet w a b)) eqn:Hempty.
  - destruct (x =? y) eqn:Hxy.
    + apply Z.eqb_eq in Hxy. subst y.
      pose proof (tnum_empty_sound w _ x (tnum_meet_sound w a b x Ha Hb)). congruence.
    + exact (tnum_const_sound 1%positive 0).
  - destruct (tnum_constant w a) as [ca|] eqn:Hca,
      (tnum_constant w b) as [cb|] eqn:Hcb; try apply tnum_top_sound.
    rewrite (tnum_constant_value w a x ca Hx Ha Hca),
      (tnum_constant_value w b y cb Hy Hb Hcb).
    destruct (ca =? cb); apply tnum_const_sound.
Qed.

Lemma tnum_bias_sound : forall w a x,
  tnum_gamma w a x -> tnum_gamma w (tnum_bias w a) (wxor w x (half w)).
Proof.
  intros w a x Ha. unfold tnum_bias. apply tnum_xor_sound; [exact Ha|].
  rewrite <- (wrap_id w (half w)) at 2 by
    (unfold is_word; pose proof (half_pos w); pose proof (modulus_half w); lia).
  apply tnum_const_sound.
Qed.

Theorem tnum_compare_sound : forall o w f a b x y,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_compare o w a b) (if eval_comparison_tag f w x y then 1 else 0).
Proof.
  intros o w f a b x y Hf Hx Hy Ha Hb. destruct o;
    try discriminate Hf; injection Hf as <-; cbn [tnum_compare eval_comparison_tag].
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy). now apply tnum_equal_sound.
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy).
    pose proof (tnum_not_sound 1%positive (tnum_equal w a b)
      (if x =? y then 1 else 0) (tnum_equal_sound w a b x y Hx Hy Ha Hb)) as Hnot.
    destruct (x =? y); exact Hnot.
  - rewrite wult_value, (wrap_id w x Hx), (wrap_id w y Hy).
    exact (tnum_order_sound true w a b x y Hx Hy Ha Hb).
  - rewrite wule_value, (wrap_id w x Hx), (wrap_id w y Hy).
    exact (tnum_order_sound false w a b x y Hx Hy Ha Hb).
  - rewrite wslt_bias, wult_value. rewrite !wrap_id by apply wxor_is_word.
    apply (tnum_order_sound true w); try apply wxor_is_word; now apply tnum_bias_sound.
  - assert (Hbias : wsle w x y = (wxor w x (half w) <=? wxor w y (half w))).
    { rewrite wsle_value, !wxor_half_value.
      destruct (signed w x <=? signed w y) eqn:Hxy;
        destruct (signed w x + half w <=? signed w y + half w) eqn:Hbias;
        try reflexivity; apply Z.leb_le in Hxy || apply Z.leb_gt in Hxy;
        apply Z.leb_le in Hbias || apply Z.leb_gt in Hbias; lia. }
    rewrite Hbias. apply (tnum_order_sound false w);
      try apply wxor_is_word; now apply tnum_bias_sound.
Qed.

Theorem tnum_count_sound : forall o w f x,
  (o = bvclz \/ o = bvctz \/ o = bvpopcnt) -> word_fun1 o = Some f ->
  tnum_gamma w (tnum_count w) (eval_unary_tag f w x).
Proof.
  intros o w f x [Ho|[Ho|Ho]] Hf; subst o; injection Hf as <-;
    apply tnum_upper_sound; first [apply wclz_range|apply tnum_ctz_range|apply wpopcnt_range].
Qed.

Lemma tnum_half_value : forall w, half w = 2 ^ (Zpos w - 1).
Proof.
  intro w. pose proof (modulus_half w) as Hhalf. rewrite modulus_value in Hhalf.
  assert (Hpow : 2 ^ Zpos w = 2 * 2 ^ (Zpos w - 1)).
  { replace (Zpos w) with ((Zpos w - 1) + 1) at 1 by lia.
    rewrite Z.pow_add_r, Z.pow_1_r by lia. ring. }
  rewrite Hpow in Hhalf. lia.
Qed.

Lemma tnum_urem_bound : forall w x y,
  is_word w x -> is_word w y -> 0 <= wurem w x y <= x.
Proof.
  intros w x y Hx Hy. destruct (Z.eq_dec y 0) as [->|Hnz].
  - rewrite wurem_zero, (wrap_id w x Hx). unfold is_word in Hx. lia.
  - rewrite wurem_spec by assumption. split.
    + apply Z.mod_pos_bound. unfold is_word in Hy. lia.
    + apply Z.mod_le; unfold is_word in *; lia.
Qed.

Theorem tnum_srem_sound : forall w a x y,
  is_word w x -> is_word w y -> tnum_gamma w a x ->
  tnum_gamma w (tnum_srem w a) (wsrem w x y).
Proof.
  intros w a x y Hx Hy Ha. apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
  apply tnum_gamma_bits. split; intros i Hi Hbit; cbn [tnum_srem zeros ones] in Hbit.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Hclear Hsign].
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_half_value, Z.pow2_bits_eqb in Hsign by lia.
    apply Z.eqb_eq in Hsign. subst i.
    assert (Hmsb : msb w x = false) by (rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, msb_testbit; now apply Hz).
    assert (Hhalf : x < half w).
    { rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, msb_half, (wrap_id w x Hx) in Hmsb.
      apply negb_false_iff, Z.ltb_lt in Hmsb. exact Hmsb. }
    rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, wsrem_value, Hmsb. destruct (msb w y).
    + pose proof (tnum_urem_bound w x (wneg w y) Hx
        (word_fun1_is_word bvneg UNeg w y eq_refl)) as Hbound.
      rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, <- (Z.mod_small (wurem w x (wneg w y)) (half w) ltac:(lia)).
      rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_half_value. apply Z.mod_pow2_bits_high. lia.
    + pose proof (tnum_urem_bound w x y Hx Hy) as Hbound.
      rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, <- (Z.mod_small (wurem w x y) (half w) ltac:(lia)).
      rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, tnum_half_value. apply Z.mod_pow2_bits_high. lia.
  - rewrite ?tnum_wrap_agrees, ?tnum_wand_agrees,
      ?tnum_wor_agrees, ?tnum_wnot_agrees, Z.bits_0 in Hbit. discriminate.
Qed.

Theorem tnum_ite_sound : forall w c a b k x y,
  is_word 1%positive k -> tnum_gamma 1%positive c k ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_ite w c a b) (if k =? 1 then x else y).
Proof.
  intros w c a b k x y Hk Hc Ha Hb. unfold tnum_ite.
  destruct (tnum_constant 1%positive c) as [v|] eqn:Hconstant.
  - rewrite (tnum_constant_value 1%positive c k v Hk Hc Hconstant).
    apply tnum_normalise_sound. destruct (v =? 1); assumption.
  - apply tnum_join_sound. destruct (k =? 1); auto.
Qed.

(** * Stored mask size

    Every newly computed mask is restricted to its declared word width. *)

(** Word membership bounds the number of stored magnitude bits. *)
Lemma tnum_word_bits : forall w z, is_word w z ->
  (Z.size_nat z <= Pos.to_nat w)%nat.
Proof.
  intros w [|z|z] Hword; unfold is_word, modulus in Hword;
    cbn [Z.size_nat]; try lia.
  apply Zpower2_Psize. rewrite positive_nat_Z. exact (proj2 Hword).
Qed.

(** Two word-sized masks occupy at most twice the word width. *)
Lemma tnum_bounded_bits : forall w a,
  is_word w (zeros a) -> is_word w (ones a) ->
  (tnum_bits a <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a Hz Ho. unfold tnum_bits.
  pose proof (tnum_word_bits w _ Hz). pose proof (tnum_word_bits w _ Ho). lia.
Qed.

(** Normalization stores two masks within their declared width. *)
Lemma tnum_normalise_bits : forall w a,
  (tnum_bits (tnum_normalise w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a. apply tnum_bounded_bits; cbn [tnum_normalise zeros ones];
    rewrite tnum_wrap_agrees; apply wrap_is_word.
Qed.

(** Joining masks restricts both output masks to the declared width. *)
Lemma tnum_join_bits_bound : forall w a b,
  (tnum_bits (tnum_join w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. apply tnum_bounded_bits; cbn [tnum_join zeros ones];
    rewrite tnum_wand_agrees; apply wand_is_word.
Qed.

(** Meeting masks restricts both output masks to the declared width. *)
Lemma tnum_meet_bits : forall w a b,
  (tnum_bits (tnum_meet w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. apply tnum_bounded_bits; cbn [tnum_meet zeros ones];
    rewrite tnum_wor_agrees; apply wor_is_word.
Qed.

(** A constant abstraction stores two normalized masks. *)
Lemma tnum_const_bits : forall w z,
  (tnum_bits (tnum_const w z) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w z. apply tnum_bounded_bits; cbn [tnum_const zeros ones].
  - rewrite tnum_wnot_agrees. apply wnot_is_word.
  - rewrite tnum_wrap_agrees. apply wrap_is_word.
Qed.

(** The unrestricted mask has no stored bits. *)
Lemma tnum_top_bits : forall w, (tnum_bits tnum_top <= 2 * Pos.to_nat w)%nat.
Proof. intro w. apply tnum_bounded_bits; apply zero_is_word. Qed.

(** The contradictory bottom mask stores two words. *)
Lemma tnum_bot_bits : forall w, (tnum_bits (tnum_bot w) <= 2 * Pos.to_nat w)%nat.
Proof.
  intro w. apply tnum_bounded_bits; cbn [tnum_bot zeros ones];
    unfold is_word; pose proof (modulus_pos w); lia.
Qed.

(** Negating the known bits normalizes both output masks. *)
Lemma tnum_not_bits : forall w a,
  (tnum_bits (tnum_not w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a. apply tnum_bounded_bits; cbn [tnum_not zeros ones];
    rewrite tnum_wrap_agrees; apply wrap_is_word.
Qed.

(** Carry addition normalizes both masks independently of its raw operands. *)
Lemma tnum_adc_bits : forall w a b carry,
  (tnum_bits (tnum_adc w a b carry) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b carry. apply tnum_bounded_bits; cbn [tnum_adc zeros ones];
    rewrite tnum_wrap_agrees; apply wrap_is_word.
Qed.

(** Addition produces two normalized masks. *)
Lemma tnum_add_bits : forall w a b,
  (tnum_bits (tnum_add w a b) <= 2 * Pos.to_nat w)%nat.
Proof. intros. apply tnum_adc_bits. Qed.

(** Subtraction produces two normalized masks. *)
Lemma tnum_sub_bits : forall w a b,
  (tnum_bits (tnum_sub w a b) <= 2 * Pos.to_nat w)%nat.
Proof. intros. apply tnum_adc_bits. Qed.

(** Arithmetic negation produces two normalized masks. *)
Lemma tnum_neg_bits : forall w a,
  (tnum_bits (tnum_neg w a) <= 2 * Pos.to_nat w)%nat.
Proof. intros. apply tnum_sub_bits. Qed.

(** Conjunction produces two normalized masks. *)
Lemma tnum_and_bits : forall w a b,
  (tnum_bits (tnum_and w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. apply tnum_bounded_bits; cbn [tnum_and zeros ones].
  - rewrite tnum_wor_agrees. apply wor_is_word.
  - rewrite tnum_wand_agrees. apply wand_is_word.
Qed.

(** Disjunction produces two normalized masks. *)
Lemma tnum_or_bits : forall w a b,
  (tnum_bits (tnum_or w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. apply tnum_bounded_bits; cbn [tnum_or zeros ones].
  - rewrite tnum_wand_agrees. apply wand_is_word.
  - rewrite tnum_wor_agrees. apply wor_is_word.
Qed.

(** Exclusive disjunction produces two normalized masks. *)
Lemma tnum_xor_bits : forall w a b,
  (tnum_bits (tnum_xor w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. apply tnum_bounded_bits; cbn [tnum_xor zeros ones];
    rewrite tnum_wor_agrees; apply wor_is_word.
Qed.

(** Endpoint mapping normalizes the result even for an arbitrary mapping function. *)
Lemma tnum_map_bits : forall sw rw f a,
  (tnum_bits (tnum_map sw rw f a) <= 2 * Pos.to_nat rw)%nat.
Proof.
  intros sw rw f a. apply tnum_bounded_bits; cbn [tnum_map zeros ones].
  - rewrite tnum_wnot_agrees. apply wnot_is_word.
  - rewrite tnum_wrap_agrees. apply wrap_is_word.
Qed.

(** Scalar left shift produces two normalized masks. *)
Lemma tnum_shl_scalar_bits : forall w k a,
  (tnum_bits (tnum_shl_scalar w k a) <= 2 * Pos.to_nat w)%nat.
Proof. intros. apply tnum_map_bits. Qed.

(** Every scalar shift or rotation produces two normalized masks. *)
Lemma tnum_scalar_bits_bound : forall o w k a,
  (tnum_bits (tnum_scalar o w k a) <= 2 * Pos.to_nat w)%nat.
Proof. intros. apply tnum_map_bits. Qed.

(** The low-product approximation restricts its known zero mask to the width. *)
Lemma tnum_mul_low_bits : forall w a b,
  (tnum_bits (tnum_mul_low w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. apply tnum_bounded_bits; cbn [tnum_mul_low zeros ones].
  - rewrite tnum_wrap_agrees. apply wrap_is_word.
  - apply zero_is_word.
Qed.

(** The constant-or-low multiplier produces bounded masks. *)
Lemma tnum_mul_bits : forall w a b,
  (tnum_bits (tnum_mul w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. unfold tnum_mul.
  destruct (tnum_constant w a), (tnum_constant w b);
    first [apply tnum_const_bits|apply tnum_mul_low_bits].
Qed.

(** The upper-bound approximation stores a normalized zero mask. *)
Lemma tnum_upper_bits : forall w h,
  (tnum_bits (tnum_upper w h) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w h. apply tnum_bounded_bits; cbn [tnum_upper zeros ones].
  - rewrite tnum_wnot_agrees. apply wnot_is_word.
  - apply zero_is_word.
Qed.

(** Unsigned division produces masks within the result width. *)
Lemma tnum_udiv_bits : forall w a b,
  (tnum_bits (tnum_udiv w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. unfold tnum_udiv. destruct (tnum_wrap w (ones b) =? 0);
    [apply tnum_top_bits|apply tnum_upper_bits].
Qed.

(** Unsigned remainder produces masks within the result width. *)
Lemma tnum_urem_bits : forall w a,
  (tnum_bits (tnum_urem w a) <= 2 * Pos.to_nat w)%nat.
Proof. intros. apply tnum_upper_bits. Qed.

(** Signed remainder produces masks within the result width. *)
Lemma tnum_srem_bits : forall w a,
  (tnum_bits (tnum_srem w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a. apply tnum_bounded_bits; cbn [tnum_srem zeros ones].
  - rewrite tnum_wand_agrees. apply wand_is_word.
  - apply zero_is_word.
Qed.

(** Concatenation stores masks at the sum of the operand widths. *)
Lemma tnum_concat_bits : forall w v a b,
  (tnum_bits (tnum_concat w v a b) <= 2 * Pos.to_nat (w + v)%positive)%nat.
Proof.
  intros w v a b. apply tnum_bounded_bits; cbn [tnum_concat zeros ones];
    rewrite tnum_wrap_agrees; apply wrap_is_word.
Qed.

(** Conditional selection normalizes the chosen or joined masks. *)
Lemma tnum_ite_bits : forall w c a b,
  (tnum_bits (tnum_ite w c a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w c a b. unfold tnum_ite. destruct (tnum_constant 1%positive c);
    [apply tnum_normalise_bits|apply tnum_join_bits_bound].
Qed.

(** A trace preserves state and result invariants whenever each step does. *)
Lemma tnum_runs_preserved : forall S R (step : S -> S + R)
    (state_ok : S -> Prop) (result_ok : R -> Prop),
  (forall s, state_ok s ->
    match step s with inl next => state_ok next | inr r => result_ok r end) ->
  forall n s result, tnum_runs step n s result -> state_ok s ->
    match result with inl next => state_ok next | inr r => result_ok r end.
Proof.
  intros S R step state_ok result_ok Hstep n s result Hrun.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH]; intro Hstate.
  - exact Hstate.
  - pose proof (Hstep s Hstate) as Hresult. now rewrite Hstop in Hresult.
  - apply IH. pose proof (Hstep s Hstate) as Hresult. now rewrite Hnext in Hresult.
Qed.

(** A product stage preserves a bound on its accumulator's stored mask bits. *)
Lemma tnum_mul_step_bits : forall w a b s,
  (tnum_bits (snd s) <= 2 * Pos.to_nat w)%nat ->
  match tnum_mul_stage_step w a b s with
  | inl next => (tnum_bits (snd next) <= 2 * Pos.to_nat w)%nat
  | inr r => (tnum_bits r <= 2 * Pos.to_nat w)%nat
  end.
Proof.
  intros w a b [i r] Hr. cbn [tnum_mul_stage_step snd] in *.
  destruct (Z.testbit (zeros b) i); [exact Hr|].
  destruct (Z.testbit (ones b) i); [apply tnum_add_bits|apply tnum_join_bits_bound].
Qed.

(** Accumulator multiplication preserves its stored-mask bound on either exit. *)
Lemma tnum_acc_step_bits : forall w a b s,
  (tnum_bits (snd s) <= 2 * Pos.to_nat w)%nat ->
  match tnum_mul_acc_step w a b s with
  | inl next => (tnum_bits (snd next) <= 2 * Pos.to_nat w)%nat
  | inr r => (tnum_bits r <= 2 * Pos.to_nat w)%nat
  end.
Proof.
  intros w a b [i r] Hr. cbn [tnum_mul_acc_step snd] in *.
  destruct (tnum_mul_acc_done w b i); [exact Hr|]. cbn [snd].
  destruct (Z.testbit (zeros b) i); [exact Hr|apply tnum_add_bits].
Qed.

(** Every exhausted or completed stage loop returns masks within its width. *)
Lemma tnum_mul_stages_bits : forall w a b,
  (tnum_bits (tnum_mul_stages w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. unfold tnum_mul_stages.
  set (a' := tnum_normalise w a). set (b' := tnum_normalise w b).
  destruct (tnum_empty w a' || tnum_empty w b'); [apply tnum_bot_bits|].
  pose proof (tnum_runs_preserved (Z * tnum)%type tnum (tnum_mul_stage_step w a' b')
    (fun s => (tnum_bits (snd s) <= 2 * Pos.to_nat w)%nat)
    (fun r => (tnum_bits r <= 2 * Pos.to_nat w)%nat)
    (tnum_mul_step_bits w a' b') _ _ _
    (tnum_loop_runs _ _ (tnum_mul_stage_step w a' b') (N.pos w) (0, tnum_const w 0))
    (tnum_const_bits w 0)) as Hbound.
  destruct (loopN (tnum_mul_stage_step w a' b') (N.pos w) (0, tnum_const w 0));
    exact Hbound.
Qed.

(** The final addition of value and mask accumulators normalizes their masks. *)
Lemma tnum_mul_acc_bits : forall w a b,
  (tnum_bits (tnum_mul_acc w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w a b. unfold tnum_mul_acc.
  destruct (tnum_empty w (tnum_normalise w a) || tnum_empty w (tnum_normalise w b));
    [apply tnum_bot_bits|apply tnum_add_bits].
Qed.

(** Every selected multiplication algorithm returns bounded masks. *)
Lemma tnum_mul_with_bits : forall choice w a b,
  (tnum_bits (tnum_mul_with choice w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros choice w a b. destruct choice; cbn [tnum_mul_with].
  - apply tnum_mul_bits.
  - apply tnum_mul_stages_bits.
  - apply tnum_mul_acc_bits.
  - apply tnum_meet_bits.
Qed.

(** Positive-mask expansion always reaches a normalizing join. *)
Lemma tnum_expand_bits : forall o w p d r,
  (tnum_bits (tnum_expand o w p d r) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros o w p. induction p as [p IH|p IH|]; intros d r; cbn [tnum_expand];
    first [apply IH|apply tnum_join_bits_bound].
Qed.

(** Expanding any integer mask produces bounded masks. *)
Lemma tnum_expand_mask_bits : forall o w u r,
  (tnum_bits (tnum_expand_mask o w u r) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros o w [|p|p] r; cbn [tnum_expand_mask];
    first [apply tnum_normalise_bits|apply tnum_expand_bits].
Qed.

(** Every branch of factored shift expansion produces bounded masks. *)
Lemma tnum_variable_raw_bits : forall o w a b,
  (tnum_bits (tnum_variable_raw o w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros o w a b. unfold tnum_variable_raw.
  destruct (tnum_rotation o); [apply tnum_expand_mask_bits|].
  destruct (tnum_mask w b <? 2 ^ tnum_shift_cutoff w);
    [apply tnum_expand_mask_bits|apply tnum_join_bits_bound].
Qed.

(** Variable shifts and rotations produce masks within the result width. *)
Lemma tnum_variable_bits : forall o w a b,
  (tnum_bits (tnum_variable o w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros o w a b. unfold tnum_variable.
  destruct (tnum_empty w (tnum_normalise w a) || tnum_empty w (tnum_normalise w b));
    [apply tnum_bot_bits|apply tnum_variable_raw_bits].
Qed.

(** Count abstractions store masks within their result width. *)
Lemma tnum_count_bits : forall w,
  (tnum_bits (tnum_count w) <= 2 * Pos.to_nat w)%nat.
Proof. intros. apply tnum_upper_bits. Qed.

(** Endpoint comparison produces bounded one-bit masks. *)
Lemma tnum_order_bits : forall strict w a b,
  (tnum_bits (tnum_order strict w a b) <= 2)%nat.
Proof.
  intros strict w a b. unfold tnum_order.
  destruct (if strict then tnum_max w a <? tnum_min w b
    else tnum_max w a <=? tnum_min w b); [apply tnum_const_bits|].
  destruct (if strict then tnum_max w b <=? tnum_min w a
    else tnum_max w b <? tnum_min w a); [apply tnum_const_bits|apply (tnum_top_bits 1%positive)].
Qed.

(** Equality comparison produces bounded one-bit masks. *)
Lemma tnum_equal_bits : forall w a b,
  (tnum_bits (tnum_equal w a b) <= 2)%nat.
Proof.
  intros w a b. unfold tnum_equal.
  destruct (tnum_empty w (tnum_meet w a b)); [apply tnum_const_bits|].
  destruct (tnum_constant w a), (tnum_constant w b);
    first [apply tnum_const_bits|apply (tnum_top_bits 1%positive)].
Qed.

(** Every comparison produces bounded one-bit masks. *)
Lemma tnum_compare_bits : forall o w a b,
  (tnum_bits (tnum_compare o w a b) <= 2)%nat.
Proof.
  intros o w a b. destruct o; cbn [tnum_compare];
    first [apply tnum_equal_bits|apply tnum_not_bits|apply tnum_order_bits|
      apply (tnum_top_bits 1%positive)].
Qed.

(** * Primitive time and size bounds

    Bit-length bounds pay for the masked integer operations used by every transfer. *)

(** The counter potential pays for carries while a bit count is incremented. *)
Fixpoint tnum_counter_ones (p : positive) : N :=
  match p with
  | xH => 1%N
  | xO q => tnum_counter_ones q
  | xI q => (1 + tnum_counter_ones q)%N
  end.

(** Binary increment has constant amortized cost under the one-bit potential. *)
Lemma tnum_succ_credit : forall p,
  (Std.Pos.T_succ p + tnum_counter_ones (Pos.succ p) <=
    2 + tnum_counter_ones p)%N.
Proof.
  induction p as [p IH|p IH|]; time_unfold Std.Pos.T_succ; time_cbn; lia.
Qed.

(** Computing a positive bit count makes linearly many amortized increments. *)
Lemma tnum_size_credit : forall p,
  (Fun.Pos.T_size p + tnum_counter_ones (Pos.size p) <=
    3 * N.of_nat (Pos.size_nat p))%N.
Proof.
  induction p as [p IH|p IH|]; time_unfold Fun.Pos.T_size; time_cbn.
  all: try pose proof (tnum_succ_credit (Pos.size p)) as Hsucc.
  all: lia.
Qed.

(** Integer logarithm scans its input bits with a binary counter. *)
Lemma tnum_log2_time : forall z,
  (Fun.Z.T_log2 z <= 4 * N.of_nat (Z.size_nat z + 1))%N.
Proof.
  intros [|[p|p|]|p]; time_unfold Fun.Z.T_log2; time_cbn.
  all: try pose proof (tnum_size_credit p) as Hsize.
  all: rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ; lia.
Qed.

(** A positive bit count is bounded by the represented positive integer. *)
Lemma tnum_positive_bits : forall p, (Pos.size_nat p <= Pos.to_nat p)%nat.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.size_nat];
    rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
Qed.

(** A nonnegative integer has no more bits than its value. *)
Lemma tnum_nonnegative_bits : forall z, 0 <= z -> (Z.size_nat z <= Z.to_nat z)%nat.
Proof.
  intros [|p|p] Hnonnegative; cbn [Z.size_nat Z.to_nat]; try lia.
  apply tnum_positive_bits.
Qed.

(** Negation preserves the magnitude bit count. *)
Lemma tnum_opp_bits : forall z, Z.size_nat (- z) = Z.size_nat z.
Proof. intros []; reflexivity. Qed.

(** A power of two needs its exponent and one additional stored bit. *)
Lemma tnum_pow2_bits : forall n, 0 <= n ->
  (Z.size_nat (2 ^ n) <= Z.to_nat n + 1)%nat.
Proof.
  intros n Hn. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as Hpositive.
  destruct (2 ^ n) as [|p|p] eqn:Hpower; cbn [Z.size_nat]; try lia.
  apply Zpower2_Psize. rewrite Nat2Z.inj_add, Z2Nat.id by exact Hn.
  rewrite <- Hpower. apply Z.pow_lt_mono_r; lia.
Qed.

(** An all-ones mask is a normalized word of the requested width. *)
Lemma tnum_ones_word : forall w, is_word w (Z.ones (Zpos w)).
Proof.
  intro w. unfold is_word, modulus. rewrite Z.ones_equiv.
  pose proof (modulus_pos w). unfold modulus in *. lia.
Qed.

(** Making an all-ones mask performs linearly many bit operations. *)
Lemma tnum_ones_time : forall n, 0 <= n ->
  (Word.Z.T_ones n <= 16 * N.of_nat (Z.to_nat n + 1))%N.
Proof.
  intros n Hn.
  pose proof (Std.Z.T_shiftl_le 1 n) as Hshift.
  pose proof (Std.Z.T_pred_le (Z.shiftl 1 n)) as Hpred.
  pose proof (tnum_pow2_bits n Hn) as Hbits. rewrite <- Z.shiftl_1_l in Hbits.
  change (Std.Z.T_shiftl 1 n <= 6 * Z.abs_N n + 1)%N in Hshift.
  assert (Habs : Z.abs_N n = N.of_nat (Z.to_nat n)).
  { destruct n; cbn [Z.abs_N Z.to_nat]; try reflexivity; lia. }
  rewrite Habs in Hshift.
  time_unfold Word.Z.T_ones. rewrite Nat2N.inj_add. nia.
Qed.

(** Masked normalization is linear in width and raw integer bits. *)
Lemma tnum_wrap_time : forall w z,
  (T_tnum_wrap w z <= 32 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z.
  pose proof (tnum_ones_time (Zpos w) ltac:(lia)) as Hones.
  pose proof (tnum_word_bits w _ (tnum_ones_word w)) as Hbits.
  pose proof (Std.Z.T_land_le z (Z.ones (Zpos w))) as Hland.
  time_unfold T_tnum_wrap. time_cbn.
  change (Word.Z.T_ones (Zpos w) <= 16 * N.of_nat (Pos.to_nat w + 1))%N in Hones.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Every integer magnitude is smaller than the next power of two above its bits. *)
Lemma tnum_abs_bits_bound : forall z, Z.abs z < 2 ^ Z.of_nat (Z.size_nat z).
Proof.
  intros [|p|p]; cbn [Z.abs Z.size_nat]; try lia; apply Zpower2_Psize; lia.
Qed.

(** An absolute-value power bound gives a stored-bit bound. *)
Lemma tnum_bits_of_abs_bound : forall z n,
  Z.abs z < 2 ^ Z.of_nat n -> (Z.size_nat z <= n)%nat.
Proof.
  intros [|p|p] n Hbound; cbn [Z.abs Z.size_nat] in *; try lia;
    now apply Zpower2_Psize in Hbound.
Qed.

(** Addition needs at most the operand bits and one carry bit. *)
Lemma tnum_sum_bits : forall x y,
  (Z.size_nat (x + y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros x y. apply tnum_bits_of_abs_bound.
  pose proof (tnum_abs_bits_bound x) as Hx.
  pose proof (tnum_abs_bits_bound y) as Hy.
  pose proof (Z.abs_triangle x y) as Hsum.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (Z.size_nat x)) ltac:(lia) ltac:(lia)) as Hxp.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (Z.size_nat y)) ltac:(lia) ltac:(lia)) as Hyp.
  rewrite !Nat2Z.inj_add, !Z.pow_add_r, Z.pow_1_r by lia. nia.
Qed.

(** Subtraction has the same bit budget as addition. *)
Lemma tnum_difference_bits : forall x y,
  (Z.size_nat (x - y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros x y. unfold Z.sub. pose proof (tnum_sum_bits x (- y)).
  now rewrite tnum_opp_bits in H.
Qed.

(** Converting an unsigned integer preserves its magnitude bit count. *)
Lemma tnum_of_N_bits : forall n, Z.size_nat (Z.of_N n) = N.size_nat n.
Proof. intros []; reflexivity. Qed.

(** Incrementing an unsigned integer needs at most one new bit. *)
Lemma tnum_succ_pos_bits : forall n,
  (Pos.size_nat (N.succ_pos n) <= N.size_nat n + 1)%nat.
Proof.
  intros [|p]; cbn [N.succ_pos N.size_nat Pos.size_nat]; [lia|].
  apply Std.Z.size_nat_succ.
Qed.

(** Integer conjunction has a linear stored-bit bound, including negative masks. *)
Lemma tnum_land_bits : forall x y,
  (Z.size_nat (Z.land x y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros [|p|p] [|q|q]; cbn [Z.land Z.size_nat]; try lia; rewrite ?tnum_of_N_bits.
  - pose proof (Std.N.size_nat_land p q). lia.
  - pose proof (Std.N.size_nat_N_ldiff (N.pos p) (Pos.pred_N q)). cbn [N.size_nat] in H. lia.
  - pose proof (Std.N.size_nat_N_ldiff (N.pos q) (Pos.pred_N p)). cbn [N.size_nat] in H. lia.
  - pose proof (tnum_succ_pos_bits (N.lor (Pos.pred_N p) (Pos.pred_N q))).
    pose proof (Std.N.size_nat_N_lor (Pos.pred_N p) (Pos.pred_N q)).
    pose proof (Std.N.size_nat_pred_N p). pose proof (Std.N.size_nat_pred_N q). lia.
Qed.

(** Integer disjunction has a linear stored-bit bound, including negative masks. *)
Lemma tnum_lor_bits : forall x y,
  (Z.size_nat (Z.lor x y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros [|p|p] [|q|q]; cbn [Z.lor Z.size_nat]; try lia.
  - pose proof (Std.N.size_nat_lor p q). lia.
  - pose proof (tnum_succ_pos_bits (N.ldiff (Pos.pred_N q) (N.pos p))).
    pose proof (Std.N.size_nat_N_ldiff (Pos.pred_N q) (N.pos p)).
    pose proof (Std.N.size_nat_pred_N q). lia.
  - pose proof (tnum_succ_pos_bits (N.ldiff (Pos.pred_N p) (N.pos q))).
    pose proof (Std.N.size_nat_N_ldiff (Pos.pred_N p) (N.pos q)).
    pose proof (Std.N.size_nat_pred_N p). lia.
  - pose proof (tnum_succ_pos_bits (N.land (Pos.pred_N p) (Pos.pred_N q))).
    pose proof (Std.N.size_nat_N_land (Pos.pred_N p) (Pos.pred_N q)).
    pose proof (Std.N.size_nat_pred_N p). lia.
Qed.

(** Integer exclusive disjunction has a linear stored-bit bound. *)
Lemma tnum_lxor_bits : forall x y,
  (Z.size_nat (Z.lxor x y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros [|p|p] [|q|q]; cbn [Z.lxor Z.size_nat]; try lia; rewrite ?tnum_of_N_bits.
  - pose proof (Std.N.size_nat_lxor p q). lia.
  - pose proof (tnum_succ_pos_bits (N.lxor (N.pos p) (Pos.pred_N q))).
    pose proof (Std.N.size_nat_N_lxor (N.pos p) (Pos.pred_N q)).
    pose proof (Std.N.size_nat_pred_N q). cbn [N.size_nat] in *. lia.
  - pose proof (tnum_succ_pos_bits (N.lxor (Pos.pred_N p) (N.pos q))).
    pose proof (Std.N.size_nat_N_lxor (Pos.pred_N p) (N.pos q)).
    pose proof (Std.N.size_nat_pred_N p). cbn [N.size_nat] in *. lia.
  - pose proof (Std.N.size_nat_N_lxor (Pos.pred_N p) (Pos.pred_N q)).
    pose proof (Std.N.size_nat_pred_N p). pose proof (Std.N.size_nat_pred_N q). lia.
Qed.

(** Integer complementation adds at most two magnitude bits. *)
Lemma tnum_lnot_bits : forall z, (Z.size_nat (Z.lnot z) <= Z.size_nat z + 2)%nat.
Proof.
  intro z. rewrite lnot_value.
  pose proof (tnum_difference_bits (- z) 1) as Hbits.
  rewrite tnum_opp_bits in Hbits. cbn [Z.size_nat Pos.size_nat] in Hbits. lia.
Qed.

(** Complementation has linear cost in its input magnitude bits. *)
Lemma tnum_lnot_time : forall z,
  (Z.T_lnot z <= 8 * N.of_nat (Z.size_nat z + 1))%N.
Proof.
  intro z. pose proof (Std.Z.T_pred_le (- z)) as Hpred.
  rewrite tnum_opp_bits in Hpred. time_unfold Z.T_lnot. time_cbn. time_pose.
  rewrite Nat2N.inj_add. nia.
Qed.

(** A masked integer occupies no more bits than its word width. *)
Lemma tnum_wrap_bits : forall w z,
  (Z.size_nat (tnum_wrap w z) <= Pos.to_nat w)%nat.
Proof.
  intros w z. apply tnum_word_bits. rewrite tnum_wrap_agrees. apply wrap_is_word.
Qed.

(** Masked conjunction occupies no more bits than its word width. *)
Lemma tnum_wand_bits : forall w x y,
  (Z.size_nat (tnum_wand w x y) <= Pos.to_nat w)%nat.
Proof.
  intros w x y. apply tnum_word_bits. rewrite tnum_wand_agrees. apply wand_is_word.
Qed.

(** Masked disjunction occupies no more bits than its word width. *)
Lemma tnum_wor_bits : forall w x y,
  (Z.size_nat (tnum_wor w x y) <= Pos.to_nat w)%nat.
Proof.
  intros w x y. apply tnum_word_bits. rewrite tnum_wor_agrees. apply wor_is_word.
Qed.

(** Masked complement occupies no more bits than its word width. *)
Lemma tnum_wnot_bits : forall w z,
  (Z.size_nat (tnum_wnot w z) <= Pos.to_nat w)%nat.
Proof.
  intros w z. apply tnum_word_bits. rewrite tnum_wnot_agrees. apply wnot_is_word.
Qed.

(** The minimum endpoint occupies no more bits than its width. *)
Lemma tnum_min_bits : forall w a, (Z.size_nat (tnum_min w a) <= Pos.to_nat w)%nat.
Proof. intros. apply tnum_word_bits, tnum_min_word. Qed.

(** The maximum endpoint occupies no more bits than its width. *)
Lemma tnum_max_bits : forall w a, (Z.size_nat (tnum_max w a) <= Pos.to_nat w)%nat.
Proof. intros. apply tnum_word_bits, tnum_max_word. Qed.

(** The uncertainty mask occupies no more bits than its width. *)
Lemma tnum_mask_bits : forall w a, (Z.size_nat (tnum_mask w a) <= Pos.to_nat w)%nat.
Proof. intros. apply tnum_word_bits, tnum_mask_word. Qed.

(** Reading the zero-mask field takes constant time. *)
Lemma tnum_zeros_time : forall a, (T_zeros a <= 1)%N.
Proof. intros [z o]. time_unfold T_zeros. time_cbn. lia. Qed.

(** Reading the one-mask field takes constant time. *)
Lemma tnum_ones_projection_time : forall a, (T_ones a <= 1)%N.
Proof. intros [z o]. time_unfold T_ones. time_cbn. lia. Qed.

TimeBound tnum_wrap_time tnum_lnot_time tnum_log2_time tnum_ones_time
  tnum_zeros_time tnum_ones_projection_time.

(** Masked conjunction reads its width and raw operands linearly. *)
Lemma tnum_wand_time : forall w x y,
  (T_tnum_wand w x y <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros w x y. pose proof (tnum_land_bits x y) as Hbits.
  time_unfold T_tnum_wand. time_cbn. time_pose.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_wand_time.

(** Masked disjunction reads its width and raw operands linearly. *)
Lemma tnum_wor_time : forall w x y,
  (T_tnum_wor w x y <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros w x y. pose proof (tnum_lor_bits x y) as Hbits.
  time_unfold T_tnum_wor. time_cbn. time_pose.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_wor_time.

(** Masked complementation reads the width and raw operand linearly. *)
Lemma tnum_wnot_time : forall w z,
  (T_tnum_wnot w z <= 128 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z. pose proof (tnum_lnot_bits z) as Hbits.
  time_unfold T_tnum_wnot. time_cbn. time_pose.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_wnot_time.

(** The minimum endpoint reads only the known-one mask. *)
Lemma tnum_min_time : forall w a,
  (T_tnum_min w a <= 40 * N.of_nat (Pos.to_nat w + Z.size_nat (ones a) + 1))%N.
Proof.
  intros w a. time_unfold T_tnum_min. time_cbn. time_pose.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_min_time.

(** The maximum endpoint reads only the known-zero mask. *)
Lemma tnum_max_time : forall w a,
  (T_tnum_max w a <= 144 * N.of_nat (Pos.to_nat w + Z.size_nat (zeros a) + 1))%N.
Proof.
  intros w a. time_unfold T_tnum_max. time_cbn. time_pose.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_max_time.

(** Building the uncertainty mask reads the two stored masks linearly. *)
Lemma tnum_mask_time : forall w a,
  (T_tnum_mask w a <= 512 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a. pose proof (tnum_wor_bits w (zeros a) (ones a)) as Hbits.
  time_unfold T_tnum_mask. time_cbn. time_pose. unfold tnum_bits.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_mask_time.

(** Testing subset inclusion reads both raw masks linearly. *)
Lemma tnum_subset_time : forall w x y,
  (T_tnum_subset w x y <=
    320 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros w x y. pose proof (tnum_wand_bits w x y) as Hbits.
  time_unfold T_tnum_subset. time_cbn. time_pose.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_subset_time.

(** Normalizing a payload reads its two raw masks linearly. *)
Lemma tnum_normalise_time : forall w a,
  (T_tnum_normalise w a <= 96 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a. time_unfold T_tnum_normalise. time_cbn. time_pose.
  unfold tnum_bits. rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_normalise_time.

(** Constructing a constant payload reads its width and literal bits linearly. *)
Lemma tnum_const_time : forall w z,
  (T_tnum_const w z <= 192 * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
Proof.
  intros w z. time_unfold T_tnum_const. time_cbn. time_pose.
  rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_const_time.

(** Joining payloads reads their stored masks linearly. *)
Lemma tnum_join_time : forall w a b,
  (T_tnum_join w a b <= 288 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b. time_unfold T_tnum_join. time_cbn. time_pose.
  unfold tnum_bits. rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_join_time.

(** Meeting payloads reads their stored masks linearly. *)
Lemma tnum_meet_time : forall w a b,
  (T_tnum_meet w a b <= 288 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b. time_unfold T_tnum_meet. time_cbn. time_pose.
  unfold tnum_bits. rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_meet_time.

(** Recognizing an empty payload reads its two masks linearly. *)
Lemma tnum_empty_time : forall w a,
  (T_tnum_empty w a <= 160 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a. pose proof (tnum_wand_bits w (zeros a) (ones a)) as Hbits.
  time_unfold T_tnum_empty. time_cbn. time_pose.
  unfold tnum_bits. rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_empty_time.

(** Point recognition reads the two masks and constructs its returned endpoint linearly. *)
Lemma tnum_constant_time : forall w a,
  (T_tnum_constant w a <= 384 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a. pose proof (tnum_wrap_bits w (zeros a)) as Hbits.
  time_unfold T_tnum_constant. time_cbn. time_pose.
  destruct (tnum_wrap w (zeros a) =? tnum_wnot w (ones a));
    unfold tnum_bits; rewrite !Nat2N.inj_add in *; nia.
Qed.
TimeBound tnum_constant_time.

(** Bitwise negation reads and normalizes the two masks linearly. *)
Lemma tnum_not_time : forall w a,
  (T_tnum_not w a <= 96 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a. time_unfold T_tnum_not. time_cbn. time_pose.
  unfold tnum_bits. rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_not_time.

(** Computing a power of two uses a constant-cost doubling callback. *)
Lemma tnum_pow2_time : forall n, 0 <= n ->
  (Word.Z.T_pow 2 n <= 8 * N.of_nat (Z.to_nat n + 1))%N.
Proof.
  intros [|p|p] Hn; [| |lia].
  - time_unfold Word.Z.T_pow. time_cbn. nia.
  - pose proof (Std.Pos.T_iter_le (Z.mul 2) (fun x => Std.Z.T_mul 2 x) (fun _ => True)
      3 1 p (fun _ _ => I) (fun x _ => Std.Z.T_mul_two_le x) I) as Hiter.
    time_unfold Word.Z.T_pow. time_unfold Word.Z.T_pow_pos. time_cbn.
    cbn [Z.to_nat]. rewrite Nat2N.inj_add.
    change (N.of_nat (Pos.to_nat p)) with (N.of_nat (N.to_nat (N.pos p))).
    rewrite N2Nat.id.
    nia.
Qed.
TimeBound tnum_pow2_time.

(** Constructing the word modulus performs linearly many doublings. *)
Lemma tnum_modulus_time : forall w,
  (T_modulus w <= 16 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (tnum_pow2_time (Zpos w) ltac:(lia)) as Hpow.
  time_unfold T_modulus. time_cbn.
  change (Word.Z.T_pow 2 (Zpos w) <= 8 * N.of_nat (Pos.to_nat w + 1))%N in Hpow.
  nia.
Qed.
TimeBound tnum_modulus_time.

(** The word modulus occupies the width and one leading bit. *)
Lemma tnum_modulus_bits : forall w, (Z.size_nat (modulus w) <= Pos.to_nat w + 1)%nat.
Proof. intro w. apply (tnum_pow2_bits (Zpos w) ltac:(lia)). Qed.

(** Constructing the contradictory payload is linear in the word width. *)
Lemma tnum_bot_time : forall w,
  (T_tnum_bot w <= 64 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intro w. pose proof (tnum_modulus_bits w) as Hbits.
  time_unfold T_tnum_bot. time_cbn. time_pose.
  change (Z.size_nat (Z.pow_pos 2 w) <= Pos.to_nat w + 1)%nat in Hbits.
  cbn [Z.size_nat Pos.size_nat] in *. rewrite !Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_bot_time.

(** Appending a one bit to a nonnegative quotient uses a constant-cost addition. *)
Lemma tnum_double_add_one_time : forall z, 0 <= z ->
  (Std.Z.T_add (2 * z) 1 <= 4)%N.
Proof.
  intros [|p|p] Hz; [| |lia].
  - time_unfold Std.Z.T_add. time_cbn. lia.
  - change (Std.Z.T_add (Zpos (xO p)) 1 <= 4)%N.
    time_unfold Std.Z.T_add. time_unfold Std.Pos.T_add. time_cbn. lia.
Qed.

(** Positive division charges divisor bits at each dividend bit. *)
Lemma tnum_positive_division_step_time : forall a b, 0 < b ->
  (Std.Z.T_pos_div_eucl a b <=
    64 * N.of_nat (Pos.size_nat a) * (N.of_nat (Z.size_nat b) + 1))%N.
Proof.
  intros a b Hb. induction a as [a IH|a IH|];
    time_unfold Std.Z.T_pos_div_eucl; cbn [Pos.size_nat].
  - destruct (Std.Z.pos_div_eucl_sizes a b Hb) as (Hq0 & Hr0 & Hq & Hr).
    destruct (Z.pos_div_eucl a b) as [q r]. cbn [fst snd] in *.
    pose proof (Std.Z.T_mul_two_le r). pose proof (Std.Z.T_mul_two_le q).
    pose proof (tnum_double_add_one_time r Hr0).
    pose proof (tnum_double_add_one_time q Hq0).
    pose proof (Std.Z.T_ltb_le (2 * r + 1) b).
    pose proof (Std.Z.T_sub_le (2 * r + 1) b).
    pose proof (Std.Z.size_nat_succ_double r Hr0).
    cbn [Z.size_nat Pos.size_nat] in *.
    destruct (2 * r + 1 <? b); rewrite ?Nat2N.inj_succ, !Nat2N.inj_add in *; nia.
  - destruct (Std.Z.pos_div_eucl_sizes a b Hb) as (Hq0 & Hr0 & Hq & Hr).
    destruct (Z.pos_div_eucl a b) as [q r]. cbn [fst snd] in *.
    pose proof (Std.Z.T_mul_two_le r). pose proof (Std.Z.T_mul_two_le q).
    pose proof (tnum_double_add_one_time q Hq0).
    pose proof (Std.Z.T_ltb_le (2 * r) b).
    pose proof (Std.Z.T_sub_le (2 * r) b).
    pose proof (Std.Z.size_nat_double r Hr0).
    cbn [Z.size_nat Pos.size_nat] in *.
    destruct (2 * r <? b); rewrite ?Nat2N.inj_succ, !Nat2N.inj_add in *; nia.
  - pose proof (Std.Z.T_leb_le 2 b). cbn [Z.size_nat Pos.size_nat] in *. nia.
Qed.

(** Signed division by a positive divisor adds only linear sign correction. *)
Lemma tnum_positive_division_time : forall z p,
  (Std.Z.T_div_eucl z (Zpos p) <=
    96 * (N.of_nat (Z.size_nat z) + 1) * (N.of_nat (Pos.size_nat p) + 1))%N.
Proof.
  intros [|a|a] p; time_unfold Std.Z.T_div_eucl; cbn [Z.size_nat].
  - nia.
  - pose proof (tnum_positive_division_step_time a (Zpos p) ltac:(lia)) as Hdiv.
    cbn [Z.size_nat] in Hdiv. nia.
  - pose proof (tnum_positive_division_step_time a (Zpos p) ltac:(lia)) as Hdiv.
    destruct (Std.Z.pos_div_eucl_sizes a (Zpos p) ltac:(lia)) as (Hq0 & Hr0 & Hq & Hr).
    destruct (Z.pos_div_eucl a (Zpos p)) as [q r]. cbn [fst snd] in *.
    pose proof (Std.Z.T_opp_le q). pose proof (Std.Z.T_opp_le (q + 1)).
    pose proof (Std.Z.T_add_le q 1). pose proof (Std.Z.T_sub_le (Zpos p) r).
    destruct r; cbn [Z.size_nat Pos.size_nat] in *;
      rewrite ?Nat2N.inj_add in *; nia.
Qed.
TimeBound tnum_positive_division_time.

(** Remainder modulo a positive width costs the product of operand bit lengths. *)
Lemma tnum_positive_modulo_time : forall z p,
  (Std.Z.T_modulo z (Zpos p) <=
    128 * (N.of_nat (Z.size_nat z) + 1) * (N.of_nat (Pos.size_nat p) + 1))%N.
Proof.
  intros z p. time_unfold Std.Z.T_modulo. time_cbn. time_pose. nia.
Qed.
TimeBound tnum_positive_modulo_time.

(** A remainder modulo a positive width uses at most the width's own magnitude bits. *)
Lemma tnum_positive_modulo_bits : forall z p,
  (Z.size_nat (z mod Zpos p) <= Pos.size_nat p)%nat.
Proof.
  intros z p. change (Z.size_nat (z mod Zpos p) <= Z.size_nat (Zpos p))%nat.
  apply Std.Z.size_nat_mono. pose proof (Z.mod_pos_bound z (Zpos p) ltac:(lia)). lia.
Qed.


(** A binary predecessor spends the zero-bit credit exposed by its borrow. *)
Lemma tnum_pred_N_credit : forall p,
  (Std.Pos.T_pred_N p + loopN_zero_bits (Pos.pred_N p) <=
    loopN_zero_bits (N.pos p) + 3)%N.
Proof.
  intros [p|p|]; time_unfold Std.Pos.T_pred_N;
    cbn [Pos.pred_N loopN_zero_bits loopN_zero_bits_pos];
    try pose proof (loopN_pred_double_credit p); lia.
Qed.

(** Testing a positive word pays index borrows with binary zero-bit credit. *)
Lemma tnum_testbit_credit : forall p n,
  (Word.Pos.T_testbit p n <=
    4 * N.of_nat (Pos.size_nat p) + loopN_zero_bits n + 1)%N.
Proof.
  intro p. induction p as [p IH|p IH|]; intros [|n];
    time_unfold Word.Pos.T_testbit; cbn [Pos.size_nat].
  all: try pose proof (IH (Pos.pred_N n)) as Htail.
  all: try pose proof (tnum_pred_N_credit n) as Hpred.
  all: rewrite ?Nat2N.inj_succ; nia.
Qed.

(** Positive bit lookup is linear in the value and index bit counts. *)
Lemma tnum_positive_testbit_time : forall p n,
  (Word.Pos.T_testbit p n <=
    8 * N.of_nat (Pos.size_nat p + N.size_nat n + 1))%N.
Proof.
  intros p n. pose proof (tnum_testbit_credit p n) as Htest.
  pose proof (loopN_zero_bits_le_size n) as Hcredit.
  rewrite ?Nat2N.inj_add. nia.
Qed.
TimeBound tnum_positive_testbit_time.

(** Unsigned bit lookup adds only constant dispatch cost. *)
Lemma tnum_unsigned_testbit_time : forall z n,
  (Word.N.T_testbit z n <=
    16 * N.of_nat (N.size_nat z + N.size_nat n + 1))%N.
Proof.
  intros [|p] n; time_unfold Word.N.T_testbit; time_cbn; time_pose;
    cbn [N.size_nat]; rewrite ?Nat2N.inj_add in *; nia.
Qed.
TimeBound tnum_unsigned_testbit_time.

(** Testing parity inspects only the outer integer and low positive bit. *)
Lemma tnum_odd_time : forall z, (Word.Z.T_odd z <= 2)%N.
Proof.
  intros [|[p|p|]|[p|p|]]; time_unfold Word.Z.T_odd; time_cbn; lia.
Qed.
TimeBound tnum_odd_time.

(** Integer bit lookup also charges the predecessor needed for a negative value. *)
Lemma tnum_testbit_time : forall z i,
  (Word.Z.T_testbit z i <=
    32 * N.of_nat (Z.size_nat z + Z.size_nat i + 1))%N.
Proof.
  intros [|p|p] [|i|i]; time_unfold Word.Z.T_testbit; time_cbn; time_pose;
    try pose proof (Std.N.size_nat_pred_N p);
    cbn [Z.size_nat N.size_nat Pos.size_nat] in *;
    rewrite ?Nat2N.inj_add in *; nia.
Qed.
TimeBound tnum_testbit_time.

(** Left shift by a nonnegative count uses constant-cost doubling steps. *)
Lemma tnum_shiftl_time : forall z k, 0 <= k ->
  (Std.Z.T_shiftl z k <= 8 * N.of_nat (Z.to_nat k + 1))%N.
Proof.
  intros z [|p|p] Hk; [| |lia].
  - time_unfold Std.Z.T_shiftl. time_cbn. nia.
  - pose proof (Std.Pos.T_iter_le (Z.mul 2) (fun x => Std.Z.T_mul 2 x) (fun _ => True)
      3 z p (fun _ _ => I) (fun x _ => Std.Z.T_mul_two_le x) I) as Hiter.
    time_unfold Std.Z.T_shiftl. time_cbn. cbn [Z.to_nat].
    rewrite Nat2N.inj_add.
    change (N.of_nat (Pos.to_nat p)) with (N.of_nat (N.to_nat (N.pos p))).
    rewrite N2Nat.id. nia.
Qed.
TimeBound tnum_shiftl_time.

(** Halving a nonnegative integer preserves nonnegativity. *)
Lemma tnum_div2_nonnegative : forall z, 0 <= z -> 0 <= Z.div2 z.
Proof.
  intros [|[p|p|]|p] Hz; cbn [Z.div2]; lia.
Qed.

(** Halving a nonnegative integer reads only its outer constructor. *)
Lemma tnum_div2_time : forall z, 0 <= z -> (Std.Z.T_div2 z <= 4)%N.
Proof.
  intros [|[p|p|]|p] Hz; try lia; time_unfold Std.Z.T_div2; time_cbn; time_pose; nia.
Qed.

(** Right shift of a nonnegative integer uses constant-cost halving steps. *)
Lemma tnum_shiftr_time : forall z k, 0 <= z -> 0 <= k ->
  (Std.Z.T_shiftr z k <= 8 * N.of_nat (Z.to_nat k + 1))%N.
Proof.
  intros z [|p|p] Hz Hk; [| |lia].
  - time_unfold Std.Z.T_shiftr. time_unfold Std.Z.T_shiftl. time_cbn. time_pose. nia.
  - pose proof (Std.Pos.T_iter_le Z.div2 (fun x => Std.Z.T_div2 x) (fun x => 0 <= x)
      4 z p tnum_div2_nonnegative tnum_div2_time Hz) as Hiter.
    time_unfold Std.Z.T_shiftr. time_unfold Std.Z.T_shiftl. time_cbn. time_pose.
    cbn [Z.to_nat]. rewrite Nat2N.inj_add.
    change (N.of_nat (Pos.to_nat p)) with (N.of_nat (N.to_nat (N.pos p))).
    rewrite N2Nat.id. nia.
Qed.
TimeBound tnum_shiftr_time.

(** A nonnegative left shift adds at most one stored bit per shift step. *)
Lemma tnum_shiftl_bits : forall z k, 0 <= k ->
  (Z.size_nat (Z.shiftl z k) <= Z.size_nat z + Z.to_nat k)%nat.
Proof.
  intros z k Hk. apply tnum_bits_of_abs_bound.
  pose proof (tnum_abs_bits_bound z) as Hz.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hpow.
  rewrite Z.shiftl_mul_pow2, Z.abs_mul, (Z.abs_eq (2 ^ k)) by lia.
  rewrite Nat2Z.inj_add, Z2Nat.id, Z.pow_add_r by lia. nia.
Qed.

(** A nonnegative right shift cannot increase the stored magnitude bits. *)
Lemma tnum_shiftr_bits : forall z k, 0 <= z -> 0 <= k ->
  (Z.size_nat (Z.shiftr z k) <= Z.size_nat z)%nat.
Proof.
  intros z k Hz Hk. apply Std.Z.size_nat_mono. rewrite Z.shiftr_div_pow2 by exact Hk.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hpow. split.
  - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; nia.
Qed.

(** Squared width bit lengths are bounded by a linear multiple of the width. *)
Lemma tnum_width_bits_square : forall w,
  ((Pos.size_nat w + 1) ^ 2 <= 8 * Pos.to_nat w)%nat.
Proof.
  induction w as [w IH|w IH|]; cbn [Pos.size_nat];
    rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1.
  all: try pose proof (tnum_positive_bits w) as Hbits.
  all: try pose proof (Pos2Nat.is_pos w) as Hpositive.
  all: cbn [Nat.pow] in *; nia.
Qed.


(** A fuel-dependent invariant bounds the generated loop clock by its live callback budget. *)
Lemma tnum_loopN_indexed_time : forall (St Out : Type) (step : St -> St + Out)
    (T_step : St -> N) (Inv : N -> St -> Prop) (B fuel : N) (s : St),
  (forall n state, Inv n state -> n <> 0%N -> (T_step state <= B)%N) ->
  (forall n state next, Inv n state -> n <> 0%N -> step state = inl next ->
    Inv (N.pred n) next) ->
  Inv fuel s ->
  (T_loopN step T_step fuel s <=
    (B + 8) * fuel + B + N.of_nat (N.size_nat fuel) + 4)%N.
Proof.
  intros St Out step T_step Inv B fuel s Hcost Hpreserve Hinitial.
  assert (Hbound : forall (fs : N * St) (Hacc : Acc loopN_lt fs),
    Inv (fst fs) (snd fs) ->
    (T_loop loopN_lt (loopN_step step)
      (fun fs => T_loopN_step step T_step fs) fs Hacc <=
      ((B + 8) * fst fs + loopN_zero_bits (fst fs)) + (B + 2) + 1)%N).
  { apply T_loop_le.
    - intros [n state] [n1 next] Hlt Hinv Hgo.
      destruct n as [|p]; [discriminate Hgo|].
      change (Inv (N.pos p) state) in Hinv.
      cbn [loopN_step] in Hgo.
      destruct (step state) as [state1|result] eqn:Hstep; [|discriminate Hgo].
      inversion Hgo; subst n1 next.
      split.
      + exact (Hpreserve (N.pos p) state state1 Hinv ltac:(discriminate) Hstep).
      + pose proof (Hcost (N.pos p) state Hinv ltac:(discriminate)) as Hcallback.
        pose proof (loopN_pred_credit (N.pos p)) as Hcredit.
        assert (Hfuel : (N.pred (N.pos p) + 1 = N.pos p)%N) by lia.
        time_unfold @T_loopN_step; cbn [fst snd]; rewrite Hstep.
        cbn [N.pred] in Hcredit, Hfuel |- *; nia.
    - intros [n state] result Hinv Hstop.
      destruct n as [|p].
      + time_unfold @T_loopN_step; cbn [fst snd]; lia.
      + change (Inv (N.pos p) state) in Hinv.
        cbn [loopN_step] in Hstop.
        destruct (step state) as [state1|result1] eqn:Hstep; [discriminate Hstop|].
        pose proof (Hcost (N.pos p) state Hinv ltac:(discriminate)) as Hcallback.
        time_unfold @T_loopN_step; cbn [fst snd]; rewrite Hstep; lia. }
  time_unfold @T_loopN.
  match goal with
  | |- context [T_loop _ _ _ _ ?Hacc] =>
    pose proof (Hbound (fuel, s) Hacc Hinitial) as Hloop
  end.
  pose proof (loopN_zero_bits_le_size fuel) as Hcredit.
  cbn [fst snd] in Hloop; nia.
Qed.


(** A carry flag occupies at most one stored integer bit. *)
Lemma tnum_b2z_bits : forall c, (Z.size_nat (Z.b2z c) <= 1)%nat.
Proof. intros []; cbn [Z.b2z Z.size_nat Pos.size_nat]; lia. Qed.

(** Converting the carry flag requires only a constructor test. *)
Lemma tnum_b2z_time : forall c, (Z.T_b2z c <= 1)%N.
Proof. intros []; time_unfold Z.T_b2z; time_cbn; reflexivity. Qed.
TimeBound tnum_b2z_time.

(** An endpoint sum with carry has linearly many stored bits. *)
Lemma tnum_carry_sum_bits : forall w x y c,
  is_word w x -> is_word w y ->
  (Z.size_nat (x + y + Z.b2z c) <= 2 * Pos.to_nat w + 3)%nat.
Proof.
  intros w x y c Hx Hy. pose proof (tnum_word_bits w x Hx).
  pose proof (tnum_word_bits w y Hy). pose proof (tnum_b2z_bits c).
  pose proof (tnum_sum_bits x y). pose proof (tnum_sum_bits (x + y) (Z.b2z c)). nia.
Qed.

(** The carry uncertainty computation produces only linearly many stored bits. *)
Lemma tnum_adc_uncertain_bits : forall w a b c,
  (Z.size_nat (tnum_adc_uncertain w a b c) <= 6 * Pos.to_nat w + 9)%nat.
Proof.
  intros w a b c.
  pose proof (tnum_carry_sum_bits w (tnum_min w a) (tnum_min w b) c
    (tnum_min_word w a) (tnum_min_word w b)).
  pose proof (tnum_carry_sum_bits w (tnum_max w a) (tnum_max w b) c
    (tnum_max_word w a) (tnum_max_word w b)).
  pose proof (tnum_mask_bits w a). pose proof (tnum_mask_bits w b).
  pose proof (tnum_lxor_bits
    (tnum_min w a + tnum_min w b + Z.b2z c)
    (tnum_max w a + tnum_max w b + Z.b2z c)).
  pose proof (tnum_lor_bits (tnum_mask w a) (tnum_mask w b)).
  pose proof (tnum_lor_bits
    (Z.lxor (tnum_min w a + tnum_min w b + Z.b2z c)
      (tnum_max w a + tnum_max w b + Z.b2z c))
    (Z.lor (tnum_mask w a) (tnum_mask w b))).
  unfold tnum_adc_uncertain. nia.
Qed.

(** Computing possible carries reads the masks and their bounded endpoints linearly. *)
Lemma tnum_adc_uncertain_time : forall w a b c,
  (T_tnum_adc_uncertain w a b c <=
    4096 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b c.
  pose proof (tnum_min_bits w a). pose proof (tnum_min_bits w b).
  pose proof (tnum_max_bits w a). pose proof (tnum_max_bits w b).
  pose proof (tnum_mask_bits w a). pose proof (tnum_mask_bits w b).
  pose proof (tnum_b2z_bits c).
  pose proof (tnum_sum_bits (tnum_min w a) (tnum_min w b)).
  pose proof (tnum_sum_bits (tnum_max w a) (tnum_max w b)).
  pose proof (tnum_carry_sum_bits w (tnum_min w a) (tnum_min w b) c
    (tnum_min_word w a) (tnum_min_word w b)).
  pose proof (tnum_carry_sum_bits w (tnum_max w a) (tnum_max w b) c
    (tnum_max_word w a) (tnum_max_word w b)).
  pose proof (tnum_lxor_bits
    (tnum_min w a + tnum_min w b + Z.b2z c)
    (tnum_max w a + tnum_max w b + Z.b2z c)).
  pose proof (tnum_lor_bits (tnum_mask w a) (tnum_mask w b)).
  time_unfold T_tnum_adc_uncertain. time_cbn. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_adc_uncertain_time.

(** Adding with a carry performs a bounded number of linear mask operations. *)
Lemma tnum_adc_time : forall w a b c,
  (T_tnum_adc w a b c <=
    8192 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b c.
  pose proof (tnum_min_bits w a). pose proof (tnum_min_bits w b).
  pose proof (tnum_b2z_bits c).
  pose proof (tnum_sum_bits (tnum_min w a) (tnum_min w b)).
  pose proof (tnum_carry_sum_bits w (tnum_min w a) (tnum_min w b) c
    (tnum_min_word w a) (tnum_min_word w b)).
  pose proof (tnum_adc_uncertain_bits w a b c).
  pose proof (tnum_lor_bits (tnum_min w a + tnum_min w b + Z.b2z c)
    (tnum_adc_uncertain w a b c)).
  pose proof (tnum_lnot_bits (tnum_adc_uncertain w a b c)).
  pose proof (tnum_lnot_bits (Z.lor
    (tnum_min w a + tnum_min w b + Z.b2z c) (tnum_adc_uncertain w a b c))).
  pose proof (tnum_land_bits (tnum_min w a + tnum_min w b + Z.b2z c)
    (Z.lnot (tnum_adc_uncertain w a b c))).
  time_unfold T_tnum_adc. time_cbn. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_adc_time.

(** Addition is linear in width and the stored input masks. *)
Lemma tnum_add_time : forall w a b,
  (T_tnum_add w a b <=
    16384 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b. time_unfold T_tnum_add. time_cbn. time_pose. nia.
Qed.
TimeBound tnum_add_time.

(** Subtraction first normalizes the complemented second operand. *)
Lemma tnum_sub_time : forall w a b,
  (T_tnum_sub w a b <=
    32768 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b. pose proof (tnum_not_bits w b).
  time_unfold T_tnum_sub. time_cbn. time_pose.
  rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_sub_time.

(** Negation constructs zero and performs one subtraction. *)
Lemma tnum_neg_time : forall w a,
  (T_tnum_neg w a <=
    131072 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w a. pose proof (tnum_const_bits w 0).
  time_unfold T_tnum_neg. time_cbn. time_pose.
  cbn [Z.size_nat] in *. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_neg_time.

(** Conjunction reads both stored masks linearly. *)
Lemma tnum_and_time : forall w a b,
  (T_tnum_and w a b <=
    288 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b. time_unfold T_tnum_and. time_cbn. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_and_time.

(** Disjunction reads both stored masks linearly. *)
Lemma tnum_or_time : forall w a b,
  (T_tnum_or w a b <=
    288 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b. time_unfold T_tnum_or. time_cbn. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_or_time.

(** Exclusive disjunction combines four bounded intermediate masks. *)
Lemma tnum_xor_time : forall w a b,
  (T_tnum_xor w a b <=
    2048 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
Proof.
  intros w a b.
  pose proof (tnum_wand_bits w (zeros a) (zeros b)).
  pose proof (tnum_wand_bits w (ones a) (ones b)).
  pose proof (tnum_wand_bits w (zeros a) (ones b)).
  pose proof (tnum_wand_bits w (ones a) (zeros b)).
  time_unfold T_tnum_xor. time_cbn. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_xor_time.

(** The nonrotation cutoff uses no more bits than the width itself. *)
Lemma tnum_shift_cutoff_size : forall w,
  0 <= tnum_shift_cutoff w /\
  (Z.to_nat (tnum_shift_cutoff w) <= Pos.size_nat w)%nat.
Proof.
  intro w; split; [exact (proj1 (tnum_shift_cutoff_bound w))|].
  unfold tnum_shift_cutoff, tnum_bitlen.
  destruct (Zpos w - 1 =? 0) eqn:Hzero; [cbn; lia|].
  apply Z.eqb_neq in Hzero.
  pose proof (tnum_abs_bits_bound (Zpos w)) as Hwidth.
  cbn [Z.abs Z.size_nat] in Hwidth.
  assert (Hpower : Zpos w - 1 < 2 ^ Z.of_nat (Pos.size_nat w)) by lia.
  apply Z.log2_lt_pow2 in Hpower; [|lia].
  pose proof (Z.log2_nonneg (Zpos w - 1)) as Hnonnegative.
  pose proof (Z2Nat.id (Z.succ (Z.log2 (Zpos w - 1))) ltac:(lia)) as Hcast.
  lia.
Qed.

(** Remainder modulo a nonnegative power of two fits exactly that many bits.
    The dividend need not be nonnegative because the divisor is positive. *)
Lemma tnum_power_modulo_bits : forall u k, 0 <= k ->
  (Z.size_nat (u mod 2 ^ k) <= Z.to_nat k)%nat.
Proof.
  intros u k Hk; apply tnum_bits_of_abs_bound.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hpower.
  pose proof (Z.mod_pos_bound u (2 ^ k) Hpower) as Hremainder.
  rewrite Z.abs_eq by lia.
  rewrite Z2Nat.id by exact Hk.
  exact (proj2 Hremainder).
Qed.

(** The low uncertainty mask used by nonrotation expansion has logarithmic width. *)
Lemma tnum_cutoff_modulo_bits : forall w u,
  (Z.size_nat (u mod 2 ^ tnum_shift_cutoff w) <= Pos.size_nat w)%nat.
Proof.
  intros w u; destruct (tnum_shift_cutoff_size w) as [Hnonnegative Hsize].
  eapply Nat.le_trans; [apply tnum_power_modulo_bits; exact Hnonnegative|exact Hsize].
Qed.



(** A nonnegative count no larger than the width occupies at most that width. *)
Lemma tnum_count_bits_width : forall w k, 0 <= k <= Zpos w ->
  (Z.size_nat k <= Pos.to_nat w)%nat /\ (Z.to_nat k <= Pos.to_nat w)%nat.
Proof.
  intros w k Hk. pose proof (tnum_nonnegative_bits k ltac:(lia)) as Hbits.
  assert (Hnat : (Z.to_nat k <= Pos.to_nat w)%nat).
  { change (Z.to_nat k <= Z.to_nat (Zpos w))%nat. apply Z2Nat.inj_le; lia. }
  lia.
Qed.

(** An all-ones mask uses no more bits than its requested length. *)
Lemma tnum_ones_bits : forall n, 0 <= n ->
  (Z.size_nat (Z.ones n) <= Z.to_nat n)%nat.
Proof.
  intros n Hn. apply tnum_bits_of_abs_bound.
  rewrite Z.ones_equiv, Z2Nat.id by exact Hn.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as Hpow.
  rewrite Z.abs_eq; lia.
Qed.

(** The left-shift helper clamps its live work to the word width. *)
Lemma tnum_shl_value_time : forall w k x, 0 <= k <= Zpos w ->
  (T_tnum_shl_value w k x <=
    256 * N.of_nat (Pos.to_nat w + Z.size_nat x + 1))%N.
Proof.
  intros w k x Hk.
  destruct (tnum_count_bits_width w k Hk) as [Hbits Hnat].
  pose proof (tnum_positive_bits w) as Hwidth.
  pose proof (tnum_shiftl_time x k ltac:(lia)) as Hshift.
  pose proof (tnum_shiftl_bits x k ltac:(lia)) as Hshiftbits.
  time_unfold T_tnum_shl_value. time_cbn. time_pose.
  destruct (Zpos w <=? k); cbn [Z.size_nat] in *;
    rewrite ?Nat2N.inj_add in *; nia.
Qed.
TimeBound tnum_shl_value_time.

(** The logical right-shift helper reads a normalized nonnegative word. *)
Lemma tnum_lshr_value_time : forall w k x, 0 <= k <= Zpos w ->
  (T_tnum_lshr_value w k x <=
    256 * N.of_nat (Pos.to_nat w + Z.size_nat x + 1))%N.
Proof.
  intros w k x Hk.
  destruct (tnum_count_bits_width w k Hk) as [Hbits Hnat].
  pose proof (tnum_positive_bits w) as Hwidth.
  pose proof (wrap_is_word w x) as Hword. rewrite <- tnum_wrap_agrees in Hword.
  pose proof (tnum_shiftr_time (tnum_wrap w x) k ltac:(destruct Hword; lia) ltac:(lia)) as Hshift.
  time_unfold T_tnum_lshr_value. time_cbn. time_pose.
  destruct (Zpos w <=? k); cbn [Z.size_nat] in *;
    rewrite ?Nat2N.inj_add in *; nia.
Qed.
TimeBound tnum_lshr_value_time.

(** The arithmetic right-shift helper constructs at most one word-sized sign mask. *)
Lemma tnum_ashr_value_time : forall w k x, 0 <= k <= Zpos w ->
  (T_tnum_ashr_value w k x <=
    2048 * N.of_nat (Pos.to_nat w + Z.size_nat x + 1))%N.
Proof.
  intros w k x Hk.
  set (j := Z.min k (Zpos w - 1)).
  assert (Hj : 0 <= j <= Zpos w - 1) by (unfold j; lia).
  destruct (tnum_count_bits_width w k Hk) as [Hkbits Hknat].
  destruct (tnum_count_bits_width w j ltac:(lia)) as [Hjbits Hjnat].
  destruct (tnum_count_bits_width w (Zpos w - 1) ltac:(lia)) as [Htopbits Htopnat].
  destruct (tnum_count_bits_width w (Zpos w - j) ltac:(lia)) as [Htailbits Htailnat].
  pose proof (tnum_positive_bits w) as Hwidth.
  pose proof (wrap_is_word w x) as Hword. rewrite <- tnum_wrap_agrees in Hword.
  pose proof (tnum_wrap_bits w x) as Hxbits.
  pose proof (tnum_shiftr_time (tnum_wrap w x) j ltac:(destruct Hword; lia) ltac:(lia)) as Hshift.
  pose proof (tnum_shiftr_bits (tnum_wrap w x) j ltac:(destruct Hword; lia) ltac:(lia)) as Hshiftbits.
  pose proof (tnum_ones_time (Zpos w - j) ltac:(lia)) as Hones.
  pose proof (tnum_ones_bits (Zpos w - j) ltac:(lia)) as Honesbits.
  pose proof (tnum_lnot_bits (Z.ones (Zpos w - j))) as Hnotbits.
  pose proof (tnum_wrap_bits w (Z.lnot (Z.ones (Zpos w - j)))) as Hmaskbits.
  pose proof (tnum_wrap_time w x) as Hwrap.
  pose proof (Std.Z.T_sub_le (Zpos w) 1) as Htopsub.
  pose proof (Std.Z.T_min_le k (Zpos w - 1)) as Hminimum.
  pose proof (tnum_testbit_time (tnum_wrap w x) (Zpos w - 1)) as Htest.
  pose proof (Std.Z.T_sub_le (Zpos w) j) as Htailsub.
  pose proof (tnum_lnot_time (Z.ones (Zpos w - j))) as Hnot.
  pose proof (tnum_wrap_time w (Z.lnot (Z.ones (Zpos w - j)))) as Hfill.
  pose proof (Std.Z.T_lor_le (Z.shiftr (tnum_wrap w x) j)
    (tnum_wrap w (Z.lnot (Z.ones (Zpos w - j))))) as Hor.
  time_unfold T_tnum_ashr_value. fold j. clearbody j.
  try change (match w with
    | xI p => Zpos (xO p)
    | xO p => Zpos (Pos.pred_double p)
    | xH => 0
    end) with (Zpos w - 1) in *.
  try change (match -j with
    | Z0 => Zpos w
    | Zpos p => Zpos (w + p)%positive
    | Zneg p => Z.pos_sub w p
    end) with (Zpos w - j) in *.
  destruct (Z.testbit (tnum_wrap w x) (Zpos w - 1)) eqn:Hsign;
    cbn beta iota zeta in *;
    change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in *;
    change (Z.size_nat 1) with 1%nat in *;
    rewrite ?Nat2N.inj_add in *; lia.
Qed.
TimeBound tnum_ashr_value_time.

(** Mapping endpoints charges the callback twice and linear mask work. *)
Lemma tnum_map_time : forall sw rw f Tf a,
  (forall x, is_word sw x -> is_word rw (f x)) ->
  (T_tnum_map sw rw f Tf a <=
    Tf (tnum_max sw a) + Tf (tnum_min sw a) +
    1024 * N.of_nat (Pos.to_nat sw + Pos.to_nat rw + tnum_bits a + 1))%N.
Proof.
  intros sw rw f Tf a Hf.
  pose proof (tnum_word_bits rw _ (Hf _ (tnum_max_word sw a))) as Hmax.
  pose proof (tnum_word_bits rw _ (Hf _ (tnum_min_word sw a))) as Hmin.
  time_unfold T_tnum_map. cbn beta iota zeta. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. lia.
Qed.

(** A bounded rotation uses one left shift and one nonnegative right shift. *)
Lemma tnum_rotl_value_time : forall w k x, 0 <= k <= Zpos w ->
  (T_tnum_rotl_value w k x <=
    512 * N.of_nat (Pos.to_nat w + Z.size_nat x + 1))%N.
Proof.
  intros w k x Hk.
  destruct (tnum_count_bits_width w k Hk) as [Hkbits Hknat].
  destruct (tnum_count_bits_width w (Zpos w - k) ltac:(lia)) as [Htailbits Htailnat].
  pose proof (tnum_positive_bits w) as Hwidth.
  pose proof (wrap_is_word w x) as Hword. rewrite <- tnum_wrap_agrees in Hword.
  pose proof (tnum_wrap_bits w x) as Hxbits.
  pose proof (tnum_shiftl_time (tnum_wrap w x) k ltac:(lia)) as Hleft.
  pose proof (tnum_shiftl_bits (tnum_wrap w x) k ltac:(lia)) as Hleftbits.
  pose proof (tnum_shiftr_time (tnum_wrap w x) (Zpos w - k)
    ltac:(destruct Hword; lia) ltac:(lia)) as Hright.
  pose proof (tnum_shiftr_bits (tnum_wrap w x) (Zpos w - k)
    ltac:(destruct Hword; lia) ltac:(lia)) as Hrightbits.
  pose proof (tnum_lor_bits (Z.shiftl (tnum_wrap w x) k)
    (Z.shiftr (tnum_wrap w x) (Zpos w - k))) as Horbits.
  time_unfold T_tnum_rotl_value. cbn beta iota zeta.
  try change (match -k with
    | Z0 => Zpos w
    | Zpos p => Zpos (w + p)%positive
    | Zneg p => Z.pos_sub w p
    end) with (Zpos w - k) in *.
  time_pose.
  change (Z.size_nat (Zpos w)) with (Pos.size_nat w) in *.
  rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound tnum_rotl_value_time.


(** Clamping a negative amount to zero never increases its stored bits. *)
Lemma tnum_max_zero_bits : forall k,
  (Z.size_nat (Z.max 0 k) <= Z.size_nat k)%nat.
Proof. intros [|p|p]; cbn [Z.max Z.compare Z.size_nat]; lia. Qed.

(** Scalar shifts charge an arbitrary amount only through its magnitude bits. *)
Lemma tnum_scalar_value_time : forall o w k x,
  (T_tnum_scalar_value o w k x <= 4096 * N.of_nat
    (Pos.to_nat w + Z.size_nat x + (Z.size_nat k + 1) * (Pos.size_nat w + 1)))%N.
Proof.
  intros o w k x.
  set (B := N.of_nat (Pos.to_nat w + Z.size_nat x +
    (Z.size_nat k + 1) * (Pos.size_nat w + 1))).
  assert (Hvalue : (N.of_nat (Pos.to_nat w + Z.size_nat x + 1) <= B)%N).
  { unfold B. rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add. nia. }
  assert (Hamount : (N.of_nat (Z.size_nat k) + 1 <= B)%N).
  { unfold B. rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add. nia. }
  assert (Hdivision :
    ((N.of_nat (Z.size_nat k) + 1) * (N.of_nat (Pos.size_nat w) + 1) <= B)%N).
  { unfold B. rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add. nia. }
  assert (HB : (1 <= B)%N) by lia.
  clearbody B.
  pose proof (tnum_wrap_time w x) as Hwrap.
  pose proof (tnum_max_zero_bits k) as Hmaxbits.
  pose proof (Std.Z.T_max_le 0 k) as Hmaximum.
  pose proof (Std.Z.T_min_le (Z.max 0 k) (Zpos w)) as Hminimum.
  change (Std.Z.T_max 0 k <= 4)%N in Hmaximum.
  assert (Hclamp : 0 <= Z.min (Z.max 0 k) (Zpos w) <= Zpos w) by lia.
  destruct o; time_unfold T_tnum_scalar_value; cbn beta iota zeta;
    try change (match k with
      | Z0 => 0
      | Zpos p => Zpos p
      | Zneg _ => 0
      end) with (Z.max 0 k) in *;
    try solve [clear Hclamp; lia].
  - pose proof (tnum_shl_value_time w (Z.min (Z.max 0 k) (Zpos w)) x Hclamp) as Hshift.
    clear Hclamp. lia.
  - pose proof (tnum_lshr_value_time w (Z.min (Z.max 0 k) (Zpos w)) x Hclamp) as Hshift.
    clear Hclamp. lia.
  - pose proof (tnum_ashr_value_time w (Z.min (Z.max 0 k) (Zpos w)) x Hclamp) as Hshift.
    clear Hclamp. lia.
  - pose proof (Z.mod_pos_bound k (Zpos w) ltac:(lia)) as Hrange.
    pose proof (tnum_rotl_value_time w (k mod Zpos w) x ltac:(lia)) as Hrotation.
    pose proof (tnum_positive_modulo_time k w) as Hmodulo.
    clear Hrange Hclamp Hmaxbits Hmaximum Hminimum. nia.
  - pose proof (Z.mod_pos_bound (-k) (Zpos w) ltac:(lia)) as Hrange.
    pose proof (tnum_rotl_value_time w ((-k) mod Zpos w) x ltac:(lia)) as Hrotation.
    pose proof (tnum_positive_modulo_time (-k) w) as Hmodulo.
    pose proof (Std.Z.T_opp_le k) as Hnegate.
    rewrite tnum_opp_bits in Hmodulo.
    clear Hrange Hclamp Hmaxbits Hmaximum Hminimum. nia.
Qed.
TimeBound tnum_scalar_value_time.


(** Scalar transfer maps two bounded endpoints. *)
Lemma tnum_scalar_time : forall o w k a,
  (T_tnum_scalar o w k a <= 32768 * N.of_nat
    (Pos.to_nat w + tnum_bits a + (Z.size_nat k + 1) * (Pos.size_nat w + 1)))%N.
Proof.
  intros o w k a.
  pose proof (tnum_map_time w w (tnum_scalar_value o w k)
    (fun x => T_tnum_scalar_value o w k x) a
    (fun x _ => tnum_scalar_word o w k x)) as Hmap.
  pose proof (tnum_scalar_value_time o w k (tnum_max w a)) as Hmax.
  pose proof (tnum_scalar_value_time o w k (tnum_min w a)) as Hmin.
  pose proof (tnum_max_bits w a). pose proof (tnum_min_bits w a).
  time_unfold T_tnum_scalar. cbn beta iota zeta.
  rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add in *. nia.
Qed.
TimeBound tnum_scalar_time.


(** Integer multiplication adds the stored magnitude bit counts. *)
Lemma tnum_product_bits : forall x y,
  (Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y)%nat.
Proof.
  exact WordTime.integer_mul_size.
Qed.

(** The original modular word wrapper has a quadratic bit-operation bound. *)
Lemma tnum_word_wrap_time : forall w z,
  (T_wrap w z <=
    256 * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
Proof.
  intros w z. eapply N.le_trans; [apply WordTime.word_wrap_time_bound|].
  apply N.mul_le_mono_r. lia.
Qed.
TimeBound tnum_word_wrap_time.

(** Word multiplication on bounded operands has quadratic cost in the width. *)
Lemma tnum_word_mul_time : forall w x y,
  is_word w x -> is_word w y ->
  (T_wmul w x y <= 4096 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
Proof.
  intros w x y Hx Hy.
  pose proof (WordTime.word_binary_width_bound T_wmul 128 w x y
    WordTime.word_mul_time_bound Hx Hy) as Htime.
  eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_r. lia.
Qed.
TimeBound tnum_word_mul_time.

(** Trailing-zero counting wraps a bounded word a constant number of times. *)
Lemma tnum_word_ctz_time : forall w x, is_word w x ->
  (T_wctz w x <= 8192 * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
Proof.
  intros w x Hx.
  pose proof (WordTime.word_unary_width_bound T_wctz 256 w x
    WordTime.word_ctz_time_bound Hx) as Htime.
  eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_r. lia.
Qed.
TimeBound tnum_word_ctz_time.

(** The trailing-zero abstraction pays for its raw mask once. *)
Lemma tnum_trailing_time : forall w a,
  (T_tnum_trailing w a <=
    16384 * N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a))%N.
Proof.
  intros w a.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1)
    (Pos.to_nat w + 1) ltac:(lia) ltac:(lia)) as Hlinear.
  pose proof (tnum_word_ctz_time w (tnum_wnot w (zeros a))
    ltac:(rewrite tnum_wnot_agrees; apply wnot_is_word)) as Hctz.
  time_unfold T_tnum_trailing. cbn beta iota zeta. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *.
  set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  clearbody budget. lia.
Qed.
TimeBound tnum_trailing_time.

(** The low-product approximation performs two trailing-zero counts. *)
Lemma tnum_mul_low_time : forall w a b,
  (T_tnum_mul_low w a b <=
    65536 * N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
Proof.
  intros w a b.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1)
    (Pos.to_nat w + 1) ltac:(lia) ltac:(lia)) as Hlinear.
  pose proof (tnum_ctz_range w (tnum_wnot w (zeros a))) as Ha.
  pose proof (tnum_ctz_range w (tnum_wnot w (zeros b))) as Hb.
  fold (tnum_trailing w a) in Ha. fold (tnum_trailing w b) in Hb.
  destruct (tnum_count_bits_width w (tnum_trailing w a) Ha) as [Habits Hanat].
  destruct (tnum_count_bits_width w (tnum_trailing w b) Hb) as [Hbbits Hbnat].
  pose proof (tnum_ones_time (tnum_trailing w a + tnum_trailing w b) ltac:(lia)) as Hones.
  pose proof (tnum_ones_bits (tnum_trailing w a + tnum_trailing w b) ltac:(lia)) as Honesbits.
  rewrite Z2Nat.inj_add in Hones, Honesbits by lia.
  time_unfold T_tnum_mul_low. cbn beta iota zeta. time_pose.
  rewrite ?Nat2N.inj_add in *.
  set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
  clearbody budget. lia.
Qed.
TimeBound tnum_mul_low_time.

(** Recognizing a constant returns a normalized endpoint. *)
Lemma tnum_constant_result_word : forall w a z,
  tnum_constant w a = Some z -> is_word w z.
Proof.
  intros w a z Hconstant. unfold tnum_constant in Hconstant.
  destruct (tnum_wrap w (zeros a) =? tnum_wnot w (ones a)); [|discriminate].
  injection Hconstant as <-. apply tnum_min_word.
Qed.

(** The constant-or-low multiplier pays raw mask sizes only in its initial checks. *)
Lemma tnum_mul_time : forall w a b,
  (T_tnum_mul w a b <=
    131072 * N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
Proof.
  intros w a b.
  pose proof (WordTime.time_square_floor (Pos.to_nat w + 1)
    (Pos.to_nat w + 1) ltac:(lia) ltac:(lia)) as Hlinear.
  time_unfold T_tnum_mul. cbn beta iota zeta.
  destruct (tnum_constant w a) as [x|] eqn:Ha,
    (tnum_constant w b) as [y|] eqn:Hb.
  - pose proof (tnum_word_mul_time w x y
      (tnum_constant_result_word w a x Ha) (tnum_constant_result_word w b y Hb)) as Hmul.
    assert (Hproduct : (Z.size_nat (wmul w x y) <= Pos.to_nat w)%nat).
    { apply tnum_word_bits. unfold wmul. apply wrap_is_word. }
    time_pose. rewrite ?Nat2N.inj_add in *.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
    clearbody budget. lia.
  - time_pose. rewrite ?Nat2N.inj_add in *.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
    clearbody budget. lia.
  - time_pose. rewrite ?Nat2N.inj_add in *.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
    clearbody budget. lia.
  - time_pose. rewrite ?Nat2N.inj_add in *.
    set (budget := N.of_nat ((Pos.to_nat w + 1) ^ 2)) in *.
    clearbody budget. lia.
Qed.
TimeBound tnum_mul_time.

(** The multiplication shift helper returns a normalized word. *)
Lemma tnum_shl_scalar_value_word : forall w k x,
  is_word w (tnum_shl_scalar_value w k x).
Proof.
  intros w k x. unfold tnum_shl_scalar_value, tnum_shl_value.
  destruct (Zpos w <=? Z.min k (Zpos w)).
  - unfold is_word. pose proof (modulus_pos w). lia.
  - rewrite tnum_wrap_agrees. apply wrap_is_word.
Qed.

(** Clamping a bounded multiplication index is linear in the word width. *)
Lemma tnum_shl_scalar_value_time : forall w k x, 0 <= k <= Zpos w ->
  (T_tnum_shl_scalar_value w k x <=
    512 * N.of_nat (Pos.to_nat w + Z.size_nat x + 1))%N.
Proof.
  intros w k x Hk. destruct (tnum_count_bits_width w k Hk) as [Hbits Hnat].
  pose proof (tnum_shl_value_time w (Z.min k (Zpos w)) x ltac:(lia)) as Hshift.
  time_unfold T_tnum_shl_scalar_value. cbn beta iota zeta. time_pose.
  rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound tnum_shl_scalar_value_time.

(** A multiplication shift maps two normalized endpoints. *)
Lemma tnum_shl_scalar_time : forall w k a, 0 <= k <= Zpos w ->
  (T_tnum_shl_scalar w k a <=
    8192 * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
Proof.
  intros w k a Hk.
  pose proof (tnum_map_time w w (tnum_shl_scalar_value w k)
    (fun x => T_tnum_shl_scalar_value w k x) a
    (fun x _ => tnum_shl_scalar_value_word w k x)) as Hmap.
  pose proof (tnum_shl_scalar_value_time w k (tnum_max w a) Hk) as Hmax.
  pose proof (tnum_shl_scalar_value_time w k (tnum_min w a) Hk) as Hmin.
  pose proof (tnum_max_bits w a). pose proof (tnum_min_bits w a).
  time_unfold T_tnum_shl_scalar. cbn beta iota zeta.
  rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound tnum_shl_scalar_time.

(** An uncertain payload stores only its complemented word mask. *)
Lemma tnum_uncertain_bits : forall w m,
  (tnum_bits (tnum_uncertain w m) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w m. unfold tnum_bits, tnum_uncertain. cbn [zeros ones Z.size_nat].
  pose proof (tnum_wnot_bits w m). lia.
Qed.

(** Constructing an uncertain payload reads one raw mask. *)
Lemma tnum_uncertain_time : forall w m,
  (T_tnum_uncertain w m <=
    256 * N.of_nat (Pos.to_nat w + Z.size_nat m + 1))%N.
Proof.
  intros w m. time_unfold T_tnum_uncertain. cbn beta iota zeta. time_pose. lia.
Qed.
TimeBound tnum_uncertain_time.

(** The accumulating multiplier checks two bounded right shifts before stopping. *)
Lemma tnum_mul_acc_done_time : forall w b i, 0 <= i <= Zpos w ->
  (T_tnum_mul_acc_done w b i <=
    1024 * N.of_nat (Pos.to_nat w + tnum_bits b + 1))%N.
Proof.
  intros w b i Hi. destruct (tnum_count_bits_width w i Hi) as [Hibits Hinat].
  pose proof (tnum_min_word w b) as Hminword.
  pose proof (tnum_mask_word w b) as Hmaskword.
  pose proof (tnum_min_bits w b) as Hminbits.
  pose proof (tnum_mask_bits w b) as Hmaskbits.
  pose proof (tnum_shiftr_time (tnum_min w b) i ltac:(destruct Hminword; lia) ltac:(lia)) as Hmintime.
  pose proof (tnum_shiftr_time (tnum_mask w b) i ltac:(destruct Hmaskword; lia) ltac:(lia)) as Hmasktime.
  pose proof (tnum_shiftr_bits (tnum_min w b) i ltac:(destruct Hminword; lia) ltac:(lia)) as Hminshiftbits.
  pose proof (tnum_shiftr_bits (tnum_mask w b) i ltac:(destruct Hmaskword; lia) ltac:(lia)) as Hmaskshiftbits.
  time_unfold T_tnum_mul_acc_done. cbn beta iota zeta. time_pose.
  unfold tnum_bits in *. rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound tnum_mul_acc_done_time.

(** One staged multiplication step reads the raw masks once. *)
Lemma tnum_mul_stage_step_time : forall w a b i r, 0 <= i <= Zpos w ->
  (T_tnum_mul_stage_step w a b (i, r) <= 131072 * N.of_nat
    (Pos.to_nat w + Z.size_nat i + tnum_bits a + tnum_bits b + tnum_bits r + 1))%N.
Proof.
  intros w a b i r Hi.
  pose proof (tnum_shl_scalar_time w i a Hi) as Hshift.
  pose proof (tnum_shl_scalar_bits w i a) as Hshiftbits.
  pose proof (tnum_add_bits w r (tnum_shl_scalar w i a)) as Haddbits.
  time_unfold T_tnum_mul_stage_step. cbn beta iota zeta. time_pose.
  destruct (Z.testbit (zeros b) i), (Z.testbit (ones b) i);
    unfold tnum_bits in *; rewrite ?Nat2N.inj_add in *; lia.
Qed.
TimeBound tnum_mul_stage_step_time.

(** One accumulating multiplication step forms only bounded intermediate masks. *)
Lemma tnum_mul_acc_step_time : forall w a b i r, 0 <= i <= Zpos w ->
  (T_tnum_mul_acc_step w a b (i, r) <= 131072 * N.of_nat
    (Pos.to_nat w + Z.size_nat i + tnum_bits a + tnum_bits b + tnum_bits r + 1))%N.
Proof.
  intros w a b i r Hi.
  pose proof (tnum_mul_acc_done_time w b i Hi) as Hdone.
  pose proof (tnum_mask_bits w a) as Hmaskbits.
  pose proof (tnum_min_bits w a) as Hminbits.
  pose proof (tnum_wor_bits w (tnum_min w a) (tnum_mask w a)) as Hworb.
  time_unfold T_tnum_mul_acc_step. cbn beta iota zeta.
  destruct (tnum_mul_acc_done w b i);
    [cbn beta iota zeta; time_pose; rewrite ?Nat2N.inj_add in *; lia|].
  destruct (Z.testbit (zeros b) i).
  { cbn beta iota zeta. time_pose. unfold tnum_bits in *.
    change (Z.size_nat 1) with 1%nat in *.
    rewrite ?Nat2N.inj_add in *. lia. }
  destruct (Z.testbit (ones b) i).
  - pose proof (tnum_uncertain_bits w (tnum_mask w a)) as Huncertain.
    pose proof (tnum_shl_scalar_bits w i (tnum_uncertain w (tnum_mask w a))) as Hshiftbits.
    pose proof (tnum_shl_scalar_time w i (tnum_uncertain w (tnum_mask w a)) Hi) as Hshift.
    cbn beta iota zeta. time_pose. unfold tnum_bits in *.
    change (Z.size_nat 1) with 1%nat in *.
    rewrite ?Nat2N.inj_add in *. lia.
  - pose proof (tnum_uncertain_bits w (tnum_wor w (tnum_min w a) (tnum_mask w a))) as Huncertain.
    pose proof (tnum_shl_scalar_bits w i (tnum_uncertain w (tnum_wor w (tnum_min w a) (tnum_mask w a)))) as Hshiftbits.
    pose proof (tnum_shl_scalar_time w i (tnum_uncertain w (tnum_wor w (tnum_min w a) (tnum_mask w a))) Hi) as Hshift.
    cbn beta iota zeta. time_pose. unfold tnum_bits in *.
    change (Z.size_nat 1) with 1%nat in *.
    rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound tnum_mul_acc_step_time.

Local Open Scope nat_scope.

Theorem tnum_unknown_from_equation : forall n i m,
  tnum_unknown_from n i m =
  length (filter (fun j => negb (Z.testbit m (Z.of_nat j))) (seq i n)).
Proof.
  intro n. induction n as [|n IH]; intros i m; cbn [tnum_unknown_from seq filter length].
  - reflexivity.
  - rewrite IH. destruct (Z.testbit m (Z.of_nat i)); reflexivity.
Qed.

Theorem tnum_rank_equation : forall w a,
  tnum_rank w a = tnum_unknown w (zeros a) + tnum_unknown w (ones a).
Proof.
  reflexivity.
Qed.

Lemma tnum_filter_count_monotone : forall (A : Type) (f g : A -> bool) xs,
  (forall x, In x xs -> f x = true -> g x = true) ->
  length (filter f xs) <= length (filter g xs).
Proof.
  intros A f g xs. induction xs as [|x xs IH]; intro Hsub; [reflexivity|].
  assert (Htail : length (filter f xs) <= length (filter g xs)).
  { apply IH. intros y Hy. apply Hsub. now right. }
  specialize (Hsub x (or_introl eq_refl)). cbn [filter].
  destruct (f x), (g x); cbn in *; try discriminate; lia.
Qed.

Lemma tnum_filter_count_equal : forall (A : Type) (f g : A -> bool) xs,
  (forall x, In x xs -> f x = true -> g x = true) ->
  length (filter f xs) = length (filter g xs) ->
  forall x, In x xs -> f x = g x.
Proof.
  intros A f g xs. induction xs as [|y xs IH]; intros Hsub Hcount x Hin.
  - contradiction.
  - assert (Htailsub : forall a, In a xs -> f a = true -> g a = true).
    { intros a Ha. apply Hsub. now right. }
    pose proof (tnum_filter_count_monotone A f g xs Htailsub) as Htail.
    pose proof (Hsub y (or_introl eq_refl)) as Hhead.
    cbn [filter] in Hcount.
    destruct (f y) eqn:Hf, (g y) eqn:Hg; cbn in Hcount; try discriminate; try lia.
    + destruct Hin as [->|Hin]; [now rewrite Hf, Hg|].
      apply IH; [exact Htailsub|lia|exact Hin].
    + destruct Hin as [->|Hin]; [now rewrite Hf, Hg|].
      apply IH; [exact Htailsub|exact Hcount|exact Hin].
Qed.

Lemma tnum_unknown_monotone : forall w a b,
  tnum_subset w b a = true -> tnum_unknown w a <= tnum_unknown w b.
Proof.
  intros w a b Hsub. rewrite tnum_subset_bits in Hsub.
  unfold tnum_unknown.
  apply tnum_filter_count_monotone. intros i Hi Hbit. apply in_seq in Hi.
  apply negb_true_iff in Hbit. apply negb_true_iff.
  destruct (Z.testbit b (Z.of_nat i)) eqn:Hb; [|reflexivity].
  specialize (Hsub (Z.of_nat i) ltac:(rewrite <- positive_nat_Z; lia) Hb). congruence.
Qed.

Lemma tnum_unknown_equal : forall w a b,
  tnum_subset w b a = true -> tnum_unknown w a = tnum_unknown w b ->
  tnum_subset w a b = true.
Proof.
  intros w a b Hsub Hcount. apply tnum_subset_bits. intros i Hi Hbit.
  assert (Himp : forall j, In j (seq 0 (Pos.to_nat w)) ->
    negb (Z.testbit a (Z.of_nat j)) = true ->
    negb (Z.testbit b (Z.of_nat j)) = true).
  { intros j Hj Hzero. apply in_seq in Hj. apply negb_true_iff in Hzero.
    apply negb_true_iff. rewrite tnum_subset_bits in Hsub.
    destruct (Z.testbit b (Z.of_nat j)) eqn:Hb; [|reflexivity].
    specialize (Hsub (Z.of_nat j) ltac:(rewrite <- positive_nat_Z; lia) Hb). congruence. }
  unfold tnum_unknown in Hcount.
  pose proof (tnum_filter_count_equal nat _ _ _ Himp Hcount (Z.to_nat i)
    ltac:(apply in_seq; cbn [Nat.add]; split; [lia|]; apply Nat2Z.inj_lt;
      rewrite Z2Nat.id, positive_nat_Z by lia; lia)) as Heq.
  cbn beta in Heq. rewrite Z2Nat.id in Heq by lia. rewrite Hbit in Heq.
  destruct (Z.testbit b i); cbn in Heq; congruence.
Qed.

Theorem tnum_rank_monotone : forall w a b,
  tnum_leb w a b = true -> tnum_rank w a <= tnum_rank w b.
Proof.
  intros w a b Hle.
  change (tnum_subset w (zeros b) (zeros a) &&
    tnum_subset w (ones b) (ones a) = true) in Hle.
  apply andb_true_iff in Hle as [Hz Ho].
  apply tnum_unknown_monotone in Hz, Ho. rewrite !tnum_rank_equation. lia.
Qed.

Theorem tnum_rank_equal : forall w a b,
  tnum_leb w a b = true -> tnum_rank w a = tnum_rank w b ->
  tnum_leb w b a = true.
Proof.
  intros w a b Hle Heq.
  change (tnum_subset w (zeros b) (zeros a) &&
    tnum_subset w (ones b) (ones a) = true) in Hle.
  apply andb_true_iff in Hle as [Hz Ho].
  pose proof (tnum_unknown_monotone w _ _ Hz) as Hzero.
  pose proof (tnum_unknown_monotone w _ _ Ho) as Hone.
  rewrite !tnum_rank_equation in Heq.
  change (tnum_subset w (zeros a) (zeros b) &&
    tnum_subset w (ones a) (ones b) = true).
  apply andb_true_iff. split; apply tnum_unknown_equal; try assumption; lia.
Qed.

Theorem tnum_rank_bounded : forall w a, tnum_rank w a <= 2 * Pos.to_nat w.
Proof.
  intros w a. rewrite tnum_rank_equation. unfold tnum_unknown.
 
  pose proof (filter_length_le (fun i => negb (Z.testbit (zeros a) (Z.of_nat i)))
    (seq 0 (Pos.to_nat w))) as Hz.
  pose proof (filter_length_le (fun i => negb (Z.testbit (ones a) (Z.of_nat i)))
    (seq 0 (Pos.to_nat w))) as Ho.
  rewrite length_seq in Hz, Ho. lia.
Qed.

Local Open Scope Z_scope.

Module KnownBits (L : WORD_LANGUAGE) (C : TNUM_CONFIG) <: KNOWN_BITS L C.
  Include KnownBitsCode L C.
  Include KNOWN_BITS_SPEC L C.
  Definition pgamma := tnum_gamma.
  Definition pwrank (_ : pwparam) (w : positive) (a : p) : nat := known_count w a.

  (** Mask inclusion is reflexive before bottom recognition. *)
  Local Lemma tnum_raw_refl : forall w a, tnum_leb w a a = true.
  Proof. intros w a. apply tnum_leb_bits. auto. Qed.

  (** The raw join contains its left mask. *)
  Local Lemma tnum_raw_join_left : forall w a b,
    tnum_leb w a (tnum_join w a b) = true.
  Proof.
    intros w a b. exact (proj1 (proj1 (tnum_join_leb w a b (tnum_join w a b))
      (tnum_raw_refl w (tnum_join w a b)))).
  Qed.

  (** The raw join contains its right mask. *)
  Local Lemma tnum_raw_join_right : forall w a b,
    tnum_leb w b (tnum_join w a b) = true.
  Proof.
    intros w a b. exact (proj2 (proj1 (tnum_join_leb w a b (tnum_join w a b))
      (tnum_raw_refl w (tnum_join w a b)))).
  Qed.

  (** A raw refinement of a contradictory mask is contradictory. *)
  Local Lemma tnum_raw_empty_below : forall w a b,
    tnum_leb w a b = true -> tnum_empty w b = true -> tnum_empty w a = true.
  Proof.
    intros w a b Hle Hb. destruct (tnum_empty w a) eqn:Ha; [reflexivity|].
    pose proof (proj1 (tnum_endpoints_sound w a Ha)) as Hamin.
    pose proof (tnum_gamma_monotone w a b _ Hle Hamin) as Hbmin.
    pose proof (tnum_empty_sound w b _ Hbmin). congruence.
  Qed.

  (** Raw inclusion can only remove positions with known facts. *)
  Local Lemma known_count_subset : forall w a b,
    tnum_leb w a b = true -> forall i, In i (seq 0 (Pos.to_nat w)) ->
    Z.testbit (Z.lor (zeros b) (ones b)) (Z.of_nat i) = true ->
    Z.testbit (Z.lor (zeros a) (ones a)) (Z.of_nat i) = true.
  Proof.
    intros w a b Hle i Hi Hbit. apply tnum_leb_bits in Hle as [Hz Ho].
    apply in_seq in Hi. rewrite Z.lor_spec in Hbit |- *.
    apply orb_true_iff in Hbit as [Hbit|Hbit]; apply orb_true_iff.
    - left. apply Hz; [rewrite <- positive_nat_Z; lia|exact Hbit].
    - right. apply Ho; [rewrite <- positive_nat_Z; lia|exact Hbit].
  Qed.

  (** Raw inclusion does not increase the count of known positions. *)
  Local Lemma known_count_mono : forall w a b, tnum_leb w a b = true ->
    (known_count w b <= known_count w a)%nat.
  Proof.
    intros w a b Hle. unfold known_count. apply tnum_filter_count_monotone.
    exact (known_count_subset w a b Hle).
  Qed.

  (** Equal known-position counts make consistent raw inclusion symmetric. *)
  Local Lemma known_count_equal : forall w a b,
    tnum_empty w a = false -> tnum_leb w a b = true ->
    known_count w a = known_count w b -> tnum_leb w b a = true.
  Proof.
    intros w a b Ha Hle Hcount.
    assert (Hsame : forall i, 0 <= i < Zpos w ->
      Z.testbit (Z.lor (zeros b) (ones b)) i =
      Z.testbit (Z.lor (zeros a) (ones a)) i).
    { intros i Hi.
      pose proof (tnum_filter_count_equal nat _ _ _ (known_count_subset w a b Hle)
        (eq_sym Hcount) (Z.to_nat i)
        ltac:(apply in_seq; cbn [Nat.add]; split; [lia|]; apply Nat2Z.inj_lt;
          rewrite Z2Nat.id, positive_nat_Z by lia; lia)) as Heq.
      cbn beta in Heq. now rewrite Z2Nat.id in Heq by lia. }
    assert (Hdisjoint : forall i, 0 <= i < Zpos w ->
      Z.testbit (zeros a) i && Z.testbit (ones a) i = false).
    { unfold tnum_empty in Ha. apply negb_false_iff, Z.eqb_eq in Ha.
      intros i Hi. apply (f_equal (fun z => Z.testbit z i)) in Ha.
      now rewrite tnum_wand_agrees, tnum_and_bit, Z.bits_0 in Ha by exact Hi. }
    apply tnum_leb_bits in Hle as [Hz Ho]. apply tnum_leb_bits.
    split; intros i Hi Hbit; specialize (Hsame i Hi); specialize (Hdisjoint i Hi);
      specialize (Hz i Hi); specialize (Ho i Hi); rewrite !Z.lor_spec in Hsame;
      destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i),
        (Z.testbit (zeros b) i), (Z.testbit (ones b) i);
      cbn in *; intuition discriminate.
  Qed.

  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof.
    intros w a. change (tnum_empty w a || tnum_leb w a a = true).
    rewrite tnum_raw_refl, orb_true_r. reflexivity.
  Qed.

  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof.
    intro w. change (tnum_empty w (tnum_bot w) = true).
    destruct (tnum_empty w (tnum_bot w)) eqn:Hbot; [reflexivity|].
    exfalso. apply (tnum_gamma_bot_empty w (tnum_min w (tnum_bot w))).
    exact (proj1 (tnum_endpoints_sound w (tnum_bot w) Hbot)).
  Qed.

  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof.
    intros w a b Ha. change (tnum_empty w a = true) in Ha.
    change (tnum_empty w a || tnum_leb w a b = true). now rewrite Ha.
  Qed.

  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof. intros w a. apply pis_bot_least, pis_bot_bot. Qed.

  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof.
    intros w a. change (tnum_empty w a || tnum_leb w a tnum_top = true).
    apply orb_true_iff. right. apply tnum_leb_bits.
    split; intros i Hi Hbit; cbn [tnum_top zeros ones] in Hbit;
      rewrite Z.bits_0 in Hbit; discriminate.
  Qed.

  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof.
    intros w a b. change (tnum_empty w a || tnum_leb w a (tnum_join w a b) = true).
    rewrite tnum_raw_join_left, orb_true_r. reflexivity.
  Qed.

  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof.
    intros w a b. change (tnum_empty w b || tnum_leb w b (tnum_join w a b) = true).
    rewrite tnum_raw_join_right, orb_true_r. reflexivity.
  Qed.

  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof.
    intros w a b. change (tnum_empty w (tnum_meet w a b) ||
      tnum_leb w (tnum_meet w a b) a = true).
    rewrite tnum_meet_lower_left, orb_true_r. reflexivity.
  Qed.

  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof.
    intros w a b. change (tnum_empty w (tnum_meet w a b) ||
      tnum_leb w (tnum_meet w a b) b = true).
    apply orb_true_iff. right. apply tnum_leb_bits.
    split; intros i Hi Hbit; cbn [tnum_meet zeros ones];
      rewrite tnum_wor_agrees, tnum_or_bit, Hbit, orb_true_r by exact Hi; reflexivity.
  Qed.

  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof.
    intros w a b z Hle Ha.
    change (tnum_empty w a || tnum_leb w a b = true) in Hle.
    rewrite (tnum_empty_sound w a z Ha) in Hle. cbn in Hle.
    exact (tnum_gamma_monotone w a b z Hle Ha).
  Qed.

  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof. exact tnum_gamma_bot_empty. Qed.

  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof. intros w z _. apply tnum_top_sound. Qed.

  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. exact tnum_meet_sound. Qed.

  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof.
    intros w a z Hempty Ha. pose proof (tnum_empty_sound w a z Ha).
    change (tnum_empty w a = true) in Hempty. congruence.
  Qed.

  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof.
    intros w a b Hle Hb.
    change (tnum_empty w a || tnum_leb w a b = true) in Hle.
    change (tnum_empty w a = true).
    destruct (tnum_empty w a) eqn:Ha; [reflexivity|].
    cbn in Hle. pose proof (tnum_raw_empty_below w a b Hle Hb). congruence.
  Qed.

  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof.
    intros w a b c Hab Hbc.
    change (tnum_empty w a || tnum_leb w a b = true) in Hab.
    change (tnum_empty w b || tnum_leb w b c = true) in Hbc.
    change (tnum_empty w a || tnum_leb w a c = true).
    destruct (tnum_empty w a) eqn:Ha; [reflexivity|].
    cbn in Hab |- *. destruct (tnum_empty w b) eqn:Hb.
    - pose proof (tnum_raw_empty_below w a b Hab Hb). congruence.
    - cbn in Hbc. apply tnum_leb_bits in Hab, Hbc. apply tnum_leb_bits.
      destruct Hab as [Haz Hao], Hbc as [Hbz Hbo]. split; eauto.
  Qed.

  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof. exact tnum_const_sound. Qed.

  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof.
    intros w a z v Hpoint Hz Ha. exact (tnum_constant_value w a z v Hz Ha Hpoint).
  Qed.

  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. intros w a b Hle. split; [exact Hle|apply pleb_refl]. Qed.

  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. intros q w a b Hle. unfold pwiden. now rewrite Hle. Qed.

  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof.
    intros q w a b. unfold pwiden. destruct (pleb w b a);
      [apply pleb_refl|apply pjoin_ub_l].
  Qed.

  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof.
    intros q w a b. unfold pwiden. destruct (pleb w b a) eqn:Hle;
      [exact Hle|apply pjoin_ub_r].
  Qed.

  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof.
    intros q w a b Ha Hunstable. unfold pwiden. rewrite Hunstable.
    change (known_count w (tnum_join w a b) < known_count w a)%nat.
    pose proof (tnum_raw_join_left w a b) as Hjoin.
    pose proof (known_count_mono w a (tnum_join w a b) Hjoin) as Hmono.
    destruct (Nat.lt_ge_cases (known_count w (tnum_join w a b)) (known_count w a))
      as [Hlt|Hge]; [exact Hlt|].
    assert (Hcount : known_count w a = known_count w (tnum_join w a b)) by lia.
    pose proof (known_count_equal w a (tnum_join w a b) Ha Hjoin Hcount) as Hreverse.
    apply tnum_join_leb in Hreverse as [_ Hba].
    assert (Hstable : pleb w b a = true).
    { change (tnum_empty w b || tnum_leb w b a = true).
      now rewrite Hba, orb_true_r. }
    congruence.
  Qed.

  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof.
    intros q w a b Ha. destruct (pleb w b a) eqn:Hstable.
    - rewrite (pwiden_stable q w a b Hstable). lia.
    - pose proof (pwrank_widen q w a b Ha Hstable). lia.
  Qed.

  Lemma F_pwiden : forall q w a b,
    pwiden q w a b = if pleb w b a then a else pjoin w a b.
  Proof. reflexivity. Qed.

  Lemma multiplier_selected : forall w a b, tnum_mul w a b = tnum_mul_with C.multiplier w a b.
  Proof. reflexivity. Qed.
  (** Payload concretization is the zero-mask and one-mask meaning. *)
  Lemma gamma_tnum : forall w a z, pgamma w a z <-> tnum_gamma w a z.
  Proof. intros; reflexivity. Qed.
  (** Bitwise negation retains each concrete result. *)
  Lemma tnum_not_sound : forall w a x z, L.is_word w x -> pgamma w a x ->
    L.eval_op Op.bvnot ((w, x) :: nil) = Some (w, z) -> pgamma w (tnum_not w a) z.
  Proof.
    intros w a x z Hx Ha Heval.
    change (eval_op bvnot [(w, x)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun1 bvnot w x UNot eq_refl) in Heval.
    injection Heval as <-. now apply tnum_not_sound.
  Qed.
  (** Arithmetic negation retains each concrete result. *)
  Lemma tnum_neg_sound : forall w a x z, L.is_word w x -> pgamma w a x ->
    L.eval_op Op.bvneg ((w, x) :: nil) = Some (w, z) -> pgamma w (tnum_neg w a) z.
  Proof.
    intros w a x z Hx Ha Heval.
    change (eval_op bvneg [(w, x)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun1 bvneg w x UNeg eq_refl) in Heval.
    injection Heval as <-. now apply tnum_neg_sound.
  Qed.
  (** Addition retains each concrete result. *)
  Lemma tnum_add_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvadd ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_add w a b) z.
  Proof.
    intros w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvadd [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvadd w x y BAdd eq_refl) in Heval.
    injection Heval as <-. now apply tnum_add_sound.
  Qed.
  (** Subtraction retains each concrete result. *)
  Lemma tnum_sub_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvsub ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_sub w a b) z.
  Proof.
    intros w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvsub [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvsub w x y BSub eq_refl) in Heval.
    injection Heval as <-. now apply tnum_sub_sound.
  Qed.
  (** Conjunction retains each concrete result. *)
  Lemma tnum_and_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvand ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_and w a b) z.
  Proof.
    intros w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvand [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvand w x y BAnd eq_refl) in Heval.
    injection Heval as <-. now apply tnum_and_sound.
  Qed.
  (** Disjunction retains each concrete result. *)
  Lemma tnum_or_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvor ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_or w a b) z.
  Proof.
    intros w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvor [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvor w x y BOr eq_refl) in Heval.
    injection Heval as <-. now apply tnum_or_sound.
  Qed.
  (** Exclusive disjunction retains each concrete result. *)
  Lemma tnum_xor_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvxor ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_xor w a b) z.
  Proof.
    intros w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvxor [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvxor w x y BXor eq_refl) in Heval.
    injection Heval as <-. now apply tnum_xor_sound.
  Qed.
  (** Every multiplier choice retains each concrete product. *)
  Lemma tnum_mul_with_sound : forall choice w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvmul ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_mul_with choice w a b) z.
  Proof.
    intros choice w a b x y z Hx Hy Ha Hb Heval.
    change (eval_op bvmul [(w, x); (w, y)] = Some (w, z)) in Heval.
    rewrite (eval_op_fun2 bvmul w x y BMul eq_refl) in Heval.
    injection Heval as <-. now apply tnum_mul_with_sound.
  Qed.
  (** An unknown shift or rotation retains each concrete result. *)
  Lemma tnum_variable_sound : forall o w a b x y z,
    In o (Op.bvshl :: Op.bvlshr :: Op.bvashr :: Op.bvrotl :: Op.bvrotr :: nil) ->
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op o ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_variable o w a b) z.
  Proof.
    intros o w a b x y z Ho Hx Hy Ha Hb Heval.
    assert (Hshift : tnum_shift_op o) by
      (unfold tnum_shift_op; cbn in Ho; intuition congruence).
    destruct (word_fun2 o) as [f|] eqn:Hf.
    - change (eval_op o [(w, x); (w, y)] = Some (w, z)) in Heval.
      rewrite (eval_op_fun2 o w x y f Hf) in Heval. injection Heval as <-.
      eapply tnum_variable_sound; eassumption.
    - destruct Hshift as [Hshift|[Hshift|[Hshift|[Hshift|Hshift]]]];
        subst o; discriminate.
  Qed.

End KnownBits.
Module KnownBitsT (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG) <: KNOWN_BITS_ALL L C.
  Include KnownBits L C.
  Definition tnum_scalar_value := tnum_scalar_value.
  Definition T_tnum_scalar_value := T_tnum_scalar_value.
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
  TimeFun tnum_normalise.
  TimeFun tnum_not.
  TimeFun tnum_neg.
  TimeFun tnum_add.
  TimeFun tnum_sub.
  TimeFun tnum_and.
  TimeFun tnum_or.
  TimeFun tnum_xor.
  TimeFun tnum_mul_with.
  TimeFun tnum_mul.
  TimeFun tnum_variable.

  Definition psize (w : positive) (a : p) : nat := Pos.to_nat w + tnum_bits a + 1.
  Definition pwsize (_ : pwparam) : nat := 0.

  (** Bottom-aware inclusion reads the two stored payloads linearly. *)
  Local Lemma pleb_time : forall w a b,
    (T_pleb w a b <=
      1024 * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  Proof.
    intros w a b. time_unfold T_pleb. time_cbn. time_pose.
    unfold tnum_bits in *. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Definition c_payload : N := 2 * 1024.
  Definition c_tnum : N := 1. (* STUB *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. time_unfold T_ptop. time_unfold T_tnum_top. time_cbn.
    unfold c_payload. cbn [Nat.pow]. rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *. nia.
  Qed.
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. time_unfold T_pbot. time_cbn. time_pose.
    unfold c_payload. cbn [Nat.pow]. rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *. nia.
  Qed.
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. pose proof (tnum_top_bits w) as Hbits.
    unfold c_payload, psize, ptop, pbot, pconst. cbn [Nat.pow].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *. nia.
  Qed.
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. pose proof (tnum_bot_bits w) as Hbits.
    unfold c_payload, psize, ptop, pbot, pconst. cbn [Nat.pow].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *. nia.
  Qed.
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z. pose proof (tnum_const_bits w z) as Hbits.
    unfold c_payload, psize, ptop, pbot, pconst. cbn [Nat.pow].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *. nia.
  Qed.
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <= c_payload *
      N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (tnum_join_bits_bound w a b) as Hbits.
    unfold c_payload, psize, pjoin, pmeet. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <= c_payload *
      N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (tnum_meet_bits w a b) as Hbits.
    unfold c_payload, psize, pjoin, pmeet. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <= c_payload *
      N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b. unfold pwiden. destruct (pleb w b a).
    - unfold c_payload, psize, pwsize. rewrite !Nat2N.inj_add. nia.
    - pose proof (tnum_join_bits_bound w a b) as Hbits.
      unfold c_payload, psize, pwsize, pjoin. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <= c_payload *
      N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. unfold pnarrow, c_payload. nia.
  Qed.
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <= c_payload *
      N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b. pose proof (pleb_time w b a) as Hle.
    time_unfold T_pwiden. time_unfold T_pjoin. time_cbn. time_pose.
    destruct (pleb w b a); unfold c_payload, psize, pwsize;
      rewrite !Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. time_unfold T_pnarrow. time_cbn. time_pose.
    unfold c_payload, psize. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (pleb_time w a b) as Htime.
    unfold c_payload, psize. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. time_unfold T_pjoin. time_cbn. time_pose.
    unfold c_payload, psize. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. time_unfold T_pmeet. time_cbn. time_pose.
    unfold c_payload, psize. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. time_unfold T_pis_bot. time_cbn. time_pose.
    unfold c_payload, psize. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof.
    intros w a. time_unfold T_ppoint. time_cbn. time_pose.
    unfold c_payload, psize. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_pconst_le : forall w z,
    (T_pconst w z <= c_payload *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z. time_unfold T_pconst. time_cbn. time_pose.
    unfold c_payload. cbn [Nat.pow]. rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *. nia.
  Qed.

  Lemma T_tnum_normalise_le : forall w a,
    (T_tnum_normalise w a <= c_tnum *
      N.of_nat ((Pos.to_nat w + tnum_bits a + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_not_le : forall w a,
    (T_tnum_not w a <= c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_neg_le : forall w a,
    (T_tnum_neg w a <= c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_add_le : forall w a b,
    (T_tnum_add w a b <= c_tnum *
      N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_sub_le : forall w a b,
    (T_tnum_sub w a b <= c_tnum *
      N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_and_le : forall w a b,
    (T_tnum_and w a b <= c_tnum *
      N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_or_le : forall w a b,
    (T_tnum_or w a b <= c_tnum *
      N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_xor_le : forall w a b,
    (T_tnum_xor w a b <= c_tnum *
      N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_mul_with_le : forall choice w a b,
    (T_tnum_mul_with choice w a b <= c_tnum *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_mul_le : forall w a b,
    (T_tnum_mul w a b <= c_tnum *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_variable_le : forall o w a b,
    (T_tnum_variable o w a b <= c_tnum *
      N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
  Proof. Admitted. (* STUB *)
  Lemma mul_bigO : bigO (fun _ => True)
    (fun x : positive * (tnum * tnum) => N.of_nat
      ((Pos.to_nat (fst x) + 1) ^ 2 + tnum_bits (fst (snd x)) +
        tnum_bits (snd (snd x))))
    (fun x => T_tnum_mul (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)

  Definition mul_step := tnum_mul_stage_step.
  TimeFun mul_step.
  Definition acc_step := tnum_mul_acc_step.
  TimeFun acc_step.
  Definition k_mul_step : N := 64 * 4096.
  Lemma F3_rank : forall q w a, pis_bot w a = false ->
    (pwrank q w a = known_count w a)%nat.
  Proof. reflexivity. Qed.
  Lemma F4_rank_bound : forall q w a, pis_bot w a = false ->
    (pwrank q w a <= Pos.to_nat w)%nat.
  Proof.
    intros q w a _. unfold pwrank, known_count.
    pose proof (filter_length_le
      (fun i => Z.testbit (Z.lor (zeros a) (ones a)) (Z.of_nat i))
      (seq 0 (Pos.to_nat w))) as Hbound.
    now rewrite length_seq in Hbound.
  Qed.
  (** Payload size includes width and stored mask bits. *)
  Lemma psize_bits : forall w a,
    psize w a = (Pos.to_nat w + tnum_bits a + 1)%nat.
  Proof. reflexivity. Qed.
  (** Unary transfer results store no more than two masks of the width. *)
  Lemma tnum_unary_bits : forall w a,
    (tnum_bits (tnum_not w a) <= 2 * Pos.to_nat w)%nat /\
    (tnum_bits (tnum_neg w a) <= 2 * Pos.to_nat w)%nat /\
    (tnum_bits (tnum_normalise w a) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a. repeat split;
      first [apply tnum_not_bits|apply tnum_neg_bits|apply tnum_normalise_bits].
  Qed.
  (** Binary transfer results store no more than two masks of the width. *)
  Lemma tnum_binary_bits : forall w a b,
    (tnum_bits (tnum_add w a b) <= 2 * Pos.to_nat w)%nat /\
    (tnum_bits (tnum_sub w a b) <= 2 * Pos.to_nat w)%nat /\
    (tnum_bits (tnum_and w a b) <= 2 * Pos.to_nat w)%nat /\
    (tnum_bits (tnum_or w a b) <= 2 * Pos.to_nat w)%nat /\
    (tnum_bits (tnum_xor w a b) <= 2 * Pos.to_nat w)%nat /\
    (tnum_bits (tnum_mul w a b) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a b. repeat split; first [apply tnum_add_bits|apply tnum_sub_bits|
      apply tnum_and_bits|apply tnum_or_bits|apply tnum_xor_bits|apply tnum_mul_with_bits].
  Qed.
  (** Configured stages and variable shifts keep masks within the width. *)
  Lemma tnum_stage_bits : forall choice o w a b,
    (tnum_bits (tnum_mul_with choice w a b) <= 2 * Pos.to_nat w)%nat /\
    (tnum_bits (tnum_variable o w a b) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros choice o w a b. split; [apply tnum_mul_with_bits|apply tnum_variable_bits].
  Qed.
  (** The bit mask agrees with modular word reduction. *)
  Lemma F0_tnum_wrap : forall w z, tnum_wrap w z = L.wrap w z.
  Proof. exact tnum_wrap_agrees. Qed.
  (** Masked scalar shifts agree with the word operations for a nonnegative amount. *)
  Lemma F0_scalar_value : forall o w k x, (0 <= k)%Z ->
    tnum_scalar_value o w k x =
      match o with
      | Op.bvshl => wshl w x (Z.min k (Zpos w))
      | Op.bvlshr => wlshr w x (Z.min k (Zpos w))
      | Op.bvashr => washr w x (Z.min k (Zpos w))
      | Op.bvrotl => wrotl w x (k mod Zpos w)
      | Op.bvrotr => wrotl w x ((- k) mod Zpos w)
      | _ => L.wrap w x
      end.
  Proof.
    exact tnum_scalar_value_agrees.
  Qed.
  (** One masked scalar shift reads the width, the amount and the raw value once. *)
  Lemma T0_scalar_value : forall o w k x,
    (T_tnum_scalar_value o w k x <= k_mul_step * N.of_nat (Pos.to_nat w + Z.size_nat x +
      (Z.size_nat k + 1) * (Pos.size_nat w + 1)))%N.
  Proof.
    intros o w k x. pose proof (tnum_scalar_value_time o w k x) as Htime.
    unfold T_tnum_scalar_value, k_mul_step. lia.
  Qed.
  Lemma F7_mul_step : forall w a b x y i r,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    (0 <= i < Zpos w)%Z -> pgamma w r (L.wrap w (x * (y mod 2 ^ i))) ->
    match mul_step w a b (i, r) with
    | inl (j, s) => j = (i + 1)%Z /\ pgamma w s (L.wrap w (x * (y mod 2 ^ j)))
    | inr s => pgamma w s (L.wrap w (x * y))
    end.
  Proof.
    intros w a b x y i r Hx Hy Ha Hb Hi Hr.
    pose proof (tnum_mul_step_sound w a b x y i r Hi Hx Ha Hb Hr) as Hstep.
    unfold mul_step. destruct (tnum_mul_stage_step w a b (i, r)) as [[j q]|q].
    - destruct Hstep as [Hj Hq]. split; [exact Hj|]. now rewrite Hj.
    - contradiction.
  Qed.
  (** A staged step keeps its output masks within the width. *)
  Lemma F8_mul_step_bits : forall w a b i r j s,
    (tnum_bits r <= 2 * Pos.to_nat w)%nat ->
    mul_step w a b (i, r) = inl (j, s) ->
    (tnum_bits s <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a b i r j q Hr Hstep.
    pose proof (tnum_mul_step_bits w a b (i, r) Hr) as Hbound.
    change (tnum_mul_stage_step w a b (i, r) = inl (j, q)) in Hstep.
    now rewrite Hstep in Hbound.
  Qed.
  (** An accumulating step keeps its output masks within the width. *)
  Lemma F9_acc_step_bits : forall w a b i r j s,
    (tnum_bits r <= 2 * Pos.to_nat w)%nat ->
    acc_step w a b (i, r) = inl (j, s) ->
    (tnum_bits s <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a b i r j q Hr Hstep.
    pose proof (tnum_acc_step_bits w a b (i, r) Hr) as Hbound.
    change (tnum_mul_acc_step w a b (i, r) = inl (j, q)) in Hstep.
    now rewrite Hstep in Hbound.
  Qed.
  (** Masking work is linear in the width and raw integer size. *)
  Lemma T0_tnum_wrap : forall w z,
    (T_tnum_wrap w z <= k_mul_step *
      N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
  Proof.
    intros w z. pose proof (tnum_wrap_time w z) as Htime.
    unfold k_mul_step. lia.
  Qed.
  (* Gamma, widening and multiplication laws now live in KNOWN_BITS_LAWS. *)
  (** One staged product step at an index within the width charges its index, accumulator
      and raw masks. *)
  Lemma T1_mul_step : forall w a b i r, (0 <= i <= Zpos w)%Z ->
    (T_mul_step w a b (i, r) <= k_mul_step *
      N.of_nat (Pos.to_nat w + Z.size_nat i + tnum_bits a + tnum_bits b +
        tnum_bits r + 1))%N.
  Proof.
    intros w a b i r Hi. pose proof (tnum_mul_stage_step_time w a b i r Hi) as Htime.
    time_unfold T_mul_step. cbn beta iota zeta. unfold k_mul_step.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.
  (** One accumulating step at an index within the width charges the width, its index and
      its accumulator. *)
  Lemma T2_acc_step : forall w a b i r, (0 <= i <= Zpos w)%Z ->
    (T_acc_step w a b (i, r) <= k_mul_step *
      N.of_nat (Pos.to_nat w + Z.size_nat i + tnum_bits a + tnum_bits b +
        tnum_bits r + 1))%N.
  Proof.
    intros w a b i r Hi. pose proof (tnum_mul_acc_step_time w a b i r Hi) as Htime.
    time_unfold T_acc_step. cbn beta iota zeta. unfold k_mul_step.
    rewrite ?Nat2N.inj_add in *. lia.
  Qed.
End KnownBitsT.
