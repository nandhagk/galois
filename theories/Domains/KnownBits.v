(** * Known-bit masks

    Known-bit masks describe zeros and ones that hold across every represented word.
    For example, an eight-bit mask can record that the low nibble is zero.
    Builds on: KnownBitsSig, WordSig and the bit-vector operations. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Loop.
From Galois.Bits Require Import Word Op Fun Testbit Arith.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import WordSig KnownBitsSig.
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

Definition tnum_shl_scalar_value (w : width) (k x : Z) : Z :=
  wshl w x (Z.min k (Zpos w)).
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
  | bvshl => wshl w x (Z.min k (Zpos w))
  | bvlshr => wlshr w x (Z.min k (Zpos w))
  | bvashr => washr w x (Z.min k (Zpos w))
  | bvrotl => wrotl w x (k mod Zpos w)
  | bvrotr => wrotl w x ((-k) mod Zpos w)
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
Module KnownBits (L : WORD_LANGUAGE) (C : TNUM_CONFIG) <: KNOWN_BITS L C.
  Include KnownBitsCode L C.
  Include KNOWN_BITS_SPEC L C.
  Definition pgamma := tnum_gamma.
  Definition pwrank (_ : pwparam) (w : positive) (a : p) : nat := known_count w a.
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted. (* STUB *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted. (* STUB *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted. (* STUB *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof. Admitted. (* STUB *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof. Admitted. (* STUB *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof. Admitted. (* STUB *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof. Admitted. (* STUB *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof. Admitted. (* STUB *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof. Admitted. (* STUB *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof. Admitted. (* STUB *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof. Admitted. (* STUB *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof. Admitted. (* STUB *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof. Admitted. (* STUB *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. Admitted. (* STUB *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof. Admitted. (* STUB *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof. Admitted. (* STUB *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof. Admitted. (* STUB *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof. Admitted. (* STUB *)
  Lemma F_pwiden : forall q w a b,
    pwiden q w a b = if pleb w b a then a else pjoin w a b.
  Proof. Admitted. (* STUB *)
  Lemma multiplier_selected : forall w a b, tnum_mul w a b = tnum_mul_with C.multiplier w a b.
  Proof. Admitted. (* STUB *)
  (** Payload concretization is the zero-mask and one-mask meaning. *)
  Lemma gamma_tnum : forall w a z, pgamma w a z <-> tnum_gamma w a z.
  Proof. intros; reflexivity. Qed.
  (** Bitwise negation retains each concrete result. *)
  Lemma tnum_not_sound : forall w a x z, L.is_word w x -> pgamma w a x ->
    L.eval_op Op.bvnot ((w, x) :: nil) = Some (w, z) -> pgamma w (tnum_not w a) z.
  Proof. Admitted. (* STUB *)
  (** Arithmetic negation retains each concrete result. *)
  Lemma tnum_neg_sound : forall w a x z, L.is_word w x -> pgamma w a x ->
    L.eval_op Op.bvneg ((w, x) :: nil) = Some (w, z) -> pgamma w (tnum_neg w a) z.
  Proof. Admitted. (* STUB *)
  (** Addition retains each concrete result. *)
  Lemma tnum_add_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvadd ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_add w a b) z.
  Proof. Admitted. (* STUB *)
  (** Subtraction retains each concrete result. *)
  Lemma tnum_sub_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvsub ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_sub w a b) z.
  Proof. Admitted. (* STUB *)
  (** Conjunction retains each concrete result. *)
  Lemma tnum_and_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvand ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_and w a b) z.
  Proof. Admitted. (* STUB *)
  (** Disjunction retains each concrete result. *)
  Lemma tnum_or_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvor ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_or w a b) z.
  Proof. Admitted. (* STUB *)
  (** Exclusive disjunction retains each concrete result. *)
  Lemma tnum_xor_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvxor ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_xor w a b) z.
  Proof. Admitted. (* STUB *)
  (** Every multiplier choice retains each concrete product. *)
  Lemma tnum_mul_with_sound : forall choice w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvmul ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_mul_with choice w a b) z.
  Proof. Admitted. (* STUB *)
  (** An unknown shift or rotation retains each concrete result. *)
  Lemma tnum_variable_sound : forall o w a b x y z,
    In o (Op.bvshl :: Op.bvlshr :: Op.bvashr :: Op.bvrotl :: Op.bvrotr :: nil) ->
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op o ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_variable o w a b) z.
  Proof. Admitted. (* STUB *)

End KnownBits.
Module KnownBitsT (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG).
  Include KnownBits L C.
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

  Definition c_payload : N := 1. (* STUB *)
  Definition c_tnum : N := 1. (* STUB *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <= c_payload *
      N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <= c_payload *
      N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <= c_payload *
      N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <= c_payload *
      N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <= c_payload *
      N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
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
  Lemma T_pconst_le : forall w z,
    (T_pconst w z <= c_payload *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)

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
      N.of_nat ((Pos.to_nat w + 1) *
        (Pos.to_nat w + tnum_bits a + tnum_bits b + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_mul_le : forall w a b,
    (T_tnum_mul w a b <= c_tnum * N.of_nat ((Pos.to_nat w + 1) *
      (Pos.to_nat w + tnum_bits a + tnum_bits b + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_tnum_variable_le : forall o w a b,
    (T_tnum_variable o w a b <= c_tnum * N.of_nat ((Pos.to_nat w + 1) *
      (Pos.to_nat w + tnum_bits a + tnum_bits b + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma mul_bigO : bigO (fun _ => True)
    (fun x : positive * (tnum * tnum) => N.of_nat ((Pos.to_nat (fst x) + 1) *
      (Pos.to_nat (fst x) + tnum_bits (fst (snd x)) + tnum_bits (snd (snd x)) + 1)))
    (fun x => T_tnum_mul (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)

  Definition mul_step := tnum_mul_stage_step.
  TimeFun mul_step.
  Definition k_mul_step : N := 1. (* STUB *)
  Lemma F1_gamma : forall w a z, pgamma w a z <-> tnum_gamma w a z.
  Proof. Admitted. (* STUB *)
  Lemma F2_widen : forall q w a b,
    pwiden q w a b = if pleb w b a then a else pjoin w a b.
  Proof. Admitted. (* STUB *)
  Lemma F3_rank : forall q w a, pis_bot w a = false ->
    (pwrank q w a = known_count w a)%nat.
  Proof. Admitted. (* STUB *)
  Lemma F4_rank_bound : forall q w a, pis_bot w a = false ->
    (pwrank q w a <= Pos.to_nat w)%nat.
  Proof. Admitted. (* STUB *)
  Lemma F5_size : forall w a, psize w a = (Pos.to_nat w + tnum_bits a + 1)%nat.
  Proof. Admitted. (* STUB *)
  Lemma F6_mul_sound : forall choice w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (tnum_mul_with choice w a b) (L.wrap w (x * y)).
  Proof. Admitted. (* STUB *)
  Lemma F7_mul_step : forall w a b x y i r,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    (0 <= i < Zpos w)%Z -> pgamma w r (L.wrap w (x * (y mod 2 ^ i))) ->
    match mul_step w a b (i, r) with
    | inl (j, s) => j = (i + 1)%Z /\ pgamma w s (L.wrap w (x * (y mod 2 ^ j)))
    | inr s => pgamma w s (L.wrap w (x * y))
    end.
  Proof. Admitted. (* STUB *)
  Lemma T1_mul_step : forall w a b i r,
    (T_mul_step w a b (i, r) <= k_mul_step *
      N.of_nat (Pos.to_nat w + Z.size_nat i + tnum_bits a + tnum_bits b +
        tnum_bits r + 1))%N.
  Proof. Admitted. (* STUB *)
End KnownBitsT.

(** Closed-form addition contains every concrete modular sum. *)
Theorem tnum_add_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w (tnum_add w a b) (wadd w x y).
Proof. Admitted. (* CONVERT: tnum_add_sound: The variable tnum_adc_sound was not found in the current environment. *)

Theorem tnum_const_sound : forall w z, tnum_gamma w (tnum_const w z) (wrap w z).
Proof. Admitted. (* CONVERT: tnum_const_sound: The variable tnum_gamma_bits was not found in the current environment. *)

Theorem tnum_meet_sound : forall w a b z,
  tnum_gamma w a z -> tnum_gamma w b z -> tnum_gamma w (tnum_meet w a b) z.
Proof. Admitted. (* CONVERT: tnum_meet_sound: The variable tnum_meet_gamma was not found in the current environment. *)

Theorem tnum_not_sound : forall w a z,
  tnum_gamma w a z -> tnum_gamma w (tnum_not w a) (wnot w z).
Proof. Admitted. (* CONVERT: tnum_not_sound: The variable tnum_gamma_bits was not found in the current environment. *)

Theorem tnum_and_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_and w a b) (wand w x y).
Proof. Admitted. (* CONVERT: tnum_and_sound: The variable tnum_gamma_bits was not found in the current environment. *)

Theorem tnum_or_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_or w a b) (wor w x y).
Proof. Admitted. (* CONVERT: tnum_or_sound: The variable tnum_gamma_bits was not found in the current environment. *)

Theorem tnum_xor_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_xor w a b) (wxor w x y).
Proof. Admitted. (* CONVERT: tnum_xor_sound: The variable tnum_gamma_bits was not found in the current environment. *)

Theorem tnum_sub_sound : forall w a b x y,
  is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_sub w a b) (wsub w x y).
Proof. Admitted. (* CONVERT: tnum_sub_sound: The variable tnum_adc_sound was not found in the current environment. *)

Theorem tnum_neg_sound : forall w a x,
  is_word w x -> tnum_gamma w a x -> tnum_gamma w (tnum_neg w a) (wneg w x).
Proof.
  intros w a x Hx Ha. rewrite wneg_value.
  replace (-x) with (0 - x) by ring. rewrite <- wsub_value.
  apply tnum_sub_sound; try assumption.
  pose proof (tnum_const_sound w 0) as Hzero. now rewrite wrap_0 in Hzero.
Qed.

Theorem tnum_mul_low_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_low w a b) (wmul w x y).
Proof. Admitted. (* CONVERT: tnum_mul_low_sound: The variable tnum_trailing_factor was not found in the current *)

Theorem tnum_mul_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul w a b) (wmul w x y).
Proof. Admitted. (* CONVERT: tnum_mul_sound: The variable tnum_constant_value was not found in the current *)

Theorem tnum_mul_stages_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_stages w a b) (wmul w x y).
Proof. Admitted. (* CONVERT: tnum_mul_stages_sound: The reference tnum_mul_stages_c was not found in the current *)

Theorem tnum_mul_acc_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_acc w a b) (wmul w x y).
Proof. Admitted. (* CONVERT: tnum_mul_acc_sound: The variable iterate_value was not found in the current environment. *)

Theorem tnum_mul_with_sound : forall choice w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_with choice w a b) (wmul w x y).
Proof. Admitted. (* CONVERT: tnum_mul_with_sound: The reference tnum_mul_with_c was not found in the current *)

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
Proof. Admitted. (* CONVERT: tnum_xor_bit: wxor has type width -> Z -> Z -> Z but binary_tag is expected. *)

Theorem tnum_subset_bits : forall w a b,
  tnum_subset w a b = true <->
  forall i, 0 <= i < Zpos w -> Z.testbit a i = true -> Z.testbit b i = true.
Proof. Admitted. (* CONVERT: tnum_subset_bits: Found no subterm matching *)

Theorem tnum_join_bits : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (zeros (tnum_join w a b)) i =
    (Z.testbit (zeros a) i && Z.testbit (zeros b) i) /\
  Z.testbit (ones (tnum_join w a b)) i =
    (Z.testbit (ones a) i && Z.testbit (ones b) i).
Proof. Admitted. (* CONVERT: tnum_join_bits: Unable to unify *)

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

Theorem tnum_top_sound : forall w z, tnum_gamma w tnum_top z.
Proof.
  intros w z. unfold tnum_gamma, tnum_top. cbn [zeros ones].
  rewrite wrap_0, Z.land_0_r, Z.land_0_l. auto.
Qed.

Theorem tnum_normalise_sound : forall w a z,
  tnum_gamma w (tnum_normalise w a) z <-> tnum_gamma w a z.
Proof. Admitted. (* CONVERT: tnum_normalise_sound: Found no subterm matching "wrap ?M1501 (wrap ?M1501 ?M1502)" *)

Theorem tnum_meet_gamma : forall w a b z,
  tnum_gamma w (tnum_meet w a b) z <-> tnum_gamma w a z /\ tnum_gamma w b z.
Proof. Admitted. (* CONVERT: tnum_meet_gamma: Found no subterm matching *)

Theorem tnum_join_sound : forall w a b z,
  tnum_gamma w a z \/ tnum_gamma w b z -> tnum_gamma w (tnum_join w a b) z.
Proof. Admitted. (* CONVERT: tnum_join_sound: The variable tnum_gamma_monotone was not found in the current *)

Theorem tnum_value_bounds : forall w a x, tnum_gamma w a x ->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (tnum_min w a) i = true -> Z.testbit x i = true) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit x i = true -> Z.testbit (tnum_max w a) i = true).
Proof. Admitted. (* CONVERT: tnum_value_bounds: Found no subterm matching "Z.testbit (wrap ?M1525 ?M1526) ?M1527" *)

Theorem tnum_known_bit : forall w a x i,
  tnum_gamma w a x -> 0 <= i < Zpos w -> Z.testbit (tnum_mask w a) i = false ->
  Z.testbit (tnum_min w a) i = Z.testbit x i /\
  Z.testbit (tnum_max w a) i = Z.testbit x i.
Proof. Admitted. (* CONVERT: tnum_known_bit: Found no subterm matching "Z.testbit (wnot ?M1521 ?M1522) ?M1523" *)

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
Proof. Admitted. (* CONVERT: tnum_unsigned_bounds:  (in proof tnum_unsigned_bounds): Attempt to save an incomplete proof *)

Theorem tnum_constant_value : forall w a x c,
  is_word w x -> tnum_gamma w a x -> tnum_constant w a = Some c -> x = c.
Proof. Admitted. (* CONVERT: tnum_constant_value: No primitive equality found. *)

Theorem tnum_empty_sound : forall w a x,
  tnum_gamma w a x -> tnum_empty w a = false.
Proof. Admitted. (* CONVERT: tnum_empty_sound: Found no subterm matching *)

Theorem tnum_endpoints_sound : forall w a,
  tnum_empty w a = false ->
  tnum_gamma w a (tnum_min w a) /\ tnum_gamma w a (tnum_max w a).
Proof. Admitted. (* CONVERT: tnum_endpoints_sound: Found no subterm matching *)

Theorem tnum_mask_bit : forall w a i, 0 <= i < Zpos w ->
  Z.testbit (tnum_mask w a) i =
    negb (Z.testbit (zeros a) i || Z.testbit (ones a) i).
Proof. Admitted. (* CONVERT: tnum_mask_bit: Found no subterm matching "Z.testbit (wnot ?M1501 ?M1502) ?M1503" *)

Theorem tnum_amount_disjoint : forall w a c,
  Z.land c (tnum_mask w a) = c -> Z.land (tnum_min w a) c = 0.
Proof. Admitted. (* CONVERT: tnum_amount_disjoint: Found no subterm matching "Z.testbit (wrap ?M1543 ?M1544) ?M1545" *)

Theorem tnum_decompose : forall w a x,
  is_word w x -> tnum_gamma w a x ->
  exists c, Z.land c (tnum_mask w a) = c /\ x = tnum_min w a + c.
Proof. Admitted. (* CONVERT: tnum_decompose: Found no subterm matching "Z.testbit (wrap ?M1600 ?M1601) ?M1602" *)

Theorem tnum_max_value_mask : forall w a,
  tnum_empty w a = false -> tnum_max w a = tnum_min w a + tnum_mask w a.
Proof. Admitted. (* CONVERT: tnum_max_value_mask: Found no subterm matching "Z.testbit (wnot ?M1549 ?M1550) ?M1551" *)

Theorem tnum_gamma_wrap : forall w a z,
  tnum_gamma w a (wrap w z) <-> tnum_gamma w a z.
Proof.
  intros w a z. rewrite !tnum_gamma_bits. split; intros [Hz Ho]; split;
    intros i Hi Hbit; specialize (Hz i Hi); specialize (Ho i Hi);
    rewrite ?tnum_wrap_bit in * by exact Hi; auto.
Qed.

Theorem tnum_adc_sound : forall w a b x y initial,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_adc w a b initial) (wrap w (x + y + Z.b2z initial)).
Proof. Admitted. (* CONVERT: tnum_adc_sound: The variable tnum_adc_known was not found in the current environment. *)

Theorem tnum_upper_sound : forall w h x,
  0 <= x <= h -> tnum_gamma w (tnum_upper w h) x.
Proof. Admitted. (* CONVERT: tnum_upper_sound: The variable tnum_bitlen_bound was not found in the current *)

Theorem tnum_udiv_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_udiv w a b) (wudiv w x y).
Proof. Admitted. (* CONVERT: tnum_udiv_sound: Unable to unify *)

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

Theorem tnum_ctz_range : forall w x, 0 <= wctz w x <= Zpos w.
Proof. Admitted. (* CONVERT: tnum_ctz_range: wctz has type width -> Z -> Z but unary_tag is expected. *)

Lemma tnum_trailing_clear : forall w a x i,
  tnum_gamma w a x -> 0 <= i < tnum_trailing w a -> Z.testbit x i = false.
Proof. Admitted. (* CONVERT: tnum_trailing_clear: Tactic failure: Cannot find witness. *)

Lemma tnum_trailing_factor : forall w a x,
  tnum_gamma w a x -> exists q, x = q * 2 ^ tnum_trailing w a.
Proof. Admitted. (* CONVERT: tnum_trailing_factor: Tactic failure: Cannot find witness. *)

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
  - unfold tnum_shl_scalar_value. rewrite Z.min_l by lia.
    rewrite <- (wmul_wshl w x i Hx Hi).
    rewrite wadd_value, wmul_value, <- wrap_add. f_equal. ring.
  - f_equal. ring.
Qed.

Theorem tnum_mul_stage_bound : forall w a b, 0 <= tnum_mul_stage_count w a b <= Zpos w.
Proof. Admitted. (* CONVERT: tnum_mul_stage_bound: The variable iterate_value was not found in the current environment. *)

Lemma tnum_uncertain_sound : forall w m x,
  Z.land x m = x -> tnum_gamma w (tnum_uncertain w m) x.
Proof. Admitted. (* CONVERT: tnum_uncertain_sound: Not convertible. *)

Lemma tnum_uncertain_zero : forall w m, tnum_gamma w (tnum_uncertain w m) 0.
Proof.
  intros w m. apply tnum_uncertain_sound. apply Z.land_0_l.
Qed.

Lemma tnum_uncertain_value : forall w a x,
  tnum_gamma w a x ->
  tnum_gamma w (tnum_uncertain w (wor w (tnum_min w a) (tnum_mask w a))) x.
Proof. Admitted. (* CONVERT: tnum_uncertain_value: Not convertible. *)

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
Proof. Admitted. (* CONVERT: tnum_mul_acc_done_sound: Found no subterm matching "Z.testbit (wrap ?M1559 ?M1560) ?M1561" *)

Theorem tnum_mul_both_gamma : forall w a b z,
  tnum_gamma w (tnum_mul_with MulBoth w a b) z <->
  tnum_gamma w (tnum_mul_with MulStages w a b) z /\
    tnum_gamma w (tnum_mul_with MulAcc w a b) z.
Proof. Admitted. (* CONVERT: tnum_mul_both_gamma: The reference tnum_mul_with_c was not found in the current *)

Theorem tnum_shl_scalar_sound : forall w k a x,
  0 <= k -> is_word w x -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shl_scalar w k a) (tnum_shl_scalar_value w k x).
Proof. Admitted. (* CONVERT: tnum_shl_scalar_sound: The variable tnum_map_sound was not found in the current environment. *)

Lemma tnum_scalar_word : forall o w k x,
  is_word w (tnum_scalar_value o w k x).
Proof. Admitted. (* CONVERT: tnum_scalar_word: No applicable tactic. *)

Theorem tnum_scalar_bits : forall o w k x i,
  0 <= k -> is_word w x -> 0 <= i < Zpos w ->
  Z.testbit (tnum_scalar_value o w k x) i =
    match tnum_source o w k i with
    | Some j => Z.testbit x j
    | None => false
    end.
Proof. Admitted. (* CONVERT: tnum_scalar_bits: Found no subterm matching *)

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

Theorem tnum_scalar_sound : forall o w k a x,
  0 <= k -> is_word w x -> tnum_gamma w a x ->
  tnum_gamma w (tnum_scalar o w k a) (tnum_scalar_value o w k x).
Proof. Admitted. (* CONVERT: tnum_scalar_sound: The variable tnum_map_sound was not found in the current environment. *)

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

Theorem tnum_concat_sound : forall w v a b x y,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  tnum_gamma (w + v)%positive (tnum_concat w v a b) (x * modulus v + y).
Proof. Admitted. (* CONVERT: tnum_concat_sound: Found no subterm matching "Z.testbit (wrap ?M1555 ?M1556) ?M1557" *)

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

Theorem tnum_expand_equation : forall o w p d r,
  tnum_expand o w p d r =
  match p with
  | xH => tnum_join w r (tnum_scalar o w d r)
  | xO q => tnum_expand o w q (tnum_stride o w d) r
  | xI q => tnum_expand o w q (tnum_stride o w d)
      (tnum_join w r (tnum_scalar o w d r))
  end.
Proof. Admitted. (* CONVERT: tnum_expand_equation: The reference tnum_expand_c was not found in the current environment. *)

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
Proof. Admitted. (* CONVERT: tnum_variable_raw_equation: The reference tnum_variable_raw_c was not found in the current *)

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
Proof. Admitted. (* CONVERT: tnum_srem_sound: wneg has type width -> Z -> Z but unary_tag is expected. *)

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

Lemma tnum_filter_count_equal : forall (A : Type) (f g : A -> bool) xs,
  (forall x, In x xs -> f x = true -> g x = true) ->
  length (filter f xs) = length (filter g xs) ->
  forall x, In x xs -> f x = g x.
Proof. Admitted. (* CONVERT: tnum_filter_count_equal: The variable tnum_filter_count_monotone was not found in the current *)
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

(** This legacy two-mask count is separate from the payload rank based on known_count. *)
Definition tnum_rank (w : width) (a : tnum) : nat :=
  (tnum_unknown w (zeros a) + tnum_unknown w (ones a))%nat.

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

Theorem tnum_meet_lower_left : forall w a b,
  tnum_leb w (tnum_meet w a b) a = true.
Proof. Admitted. (* CONVERT: tnum_meet_lower_left: Found no subterm matching *)

Lemma tnum_mul_residual_step : forall w a b x y i,
  0 <= i < Zpos w ->
  tnum_mul_residual w a b x y (i + 1) =
    tnum_mul_residual w a b x y i +
      (x * Z.b2z (Z.testbit y i) -
        tnum_min w a * Z.b2z (Z.testbit (ones b) i)) * 2 ^ i.
Proof. Admitted. (* CONVERT: tnum_mul_residual_step: Unable to unify *)

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
  unfold tnum_shl_scalar_value in Hsum. rewrite Z.min_l in Hsum by lia.
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
Proof. Admitted. (* CONVERT: tnum_mul_acc_next: Not convertible. *)

Theorem tnum_map_sound : forall sw rw f a x,
  tnum_bit_copy sw rw f -> is_word sw x -> tnum_gamma sw a x ->
  tnum_gamma rw (tnum_map sw rw f a) (f x).
Proof. Admitted. (* CONVERT: tnum_map_sound: Found no subterm matching "Z.testbit (wnot ?M1535 ?M1536) ?M1537" *)

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

Lemma tnum_scalar_copy : forall o w k, 0 <= k ->
  tnum_bit_copy w w (tnum_scalar_value o w k).
Proof.
  intros o w k Hk i Hi. destruct (tnum_source o w k i) as [j|] eqn:Hsource.
  - right. exists j. split; [eapply tnum_source_range; eassumption|].
    intros x Hx. now rewrite tnum_scalar_bits, Hsource by assumption.
  - left. intros x Hx. now rewrite tnum_scalar_bits, Hsource by assumption.
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
Proof. Admitted. (* CONVERT: tnum_join_leb: The variable leb_trans was not found in the current environment. *)

Lemma tnum_map_join : forall sw rw f a b,
  tnum_bit_copy sw rw f ->
  tnum_equiv rw (tnum_map sw rw f (tnum_join sw a b))
    (tnum_join rw (tnum_map sw rw f a) (tnum_map sw rw f b)).
Proof. Admitted. (* CONVERT: tnum_map_join: Found no subterm matching "Z.testbit (wnot ?M1538 ?M1539) ?M1540" *)

Lemma tnum_map_composition : forall sw mw rw f g a,
  tnum_bit_copy mw rw g -> (forall x, is_word sw x -> is_word mw (f x)) ->
  tnum_equiv rw (tnum_map mw rw g (tnum_map sw mw f a))
    (tnum_map sw rw (fun x => g (f x)) a).
Proof. Admitted. (* CONVERT: tnum_map_composition: Found no subterm matching "Z.testbit (wnot ?M1514 ?M1515) ?M1516" *)

Lemma tnum_scalar_composition : forall o w h k a,
  0 <= h -> 0 <= k ->
  tnum_equiv w (tnum_scalar o w k (tnum_scalar o w h a))
    (tnum_scalar o w (h + k) a).
Proof. Admitted. (* CONVERT: tnum_scalar_composition: No applicable tactic. *)

Lemma tnum_scalar_zero : forall o w a, tnum_equiv w (tnum_scalar o w 0 a) a.
Proof. Admitted. (* CONVERT: tnum_scalar_zero: Found no subterm matching "Z.testbit (wnot ?M1648 ?M1649) ?M1650" *)

Lemma tnum_choices_nonnegative : forall p c, tnum_choices p c -> 0 <= c.
Proof.
  intro p. induction p as [p IH|p IH|]; intros c Hchoice; cbn [tnum_choices] in Hchoice.
  - destruct Hchoice as [t [Ht [Hc|Hc]]]; subst c; specialize (IH t Ht); lia.
  - destruct Hchoice as [t [Ht ->]]. specialize (IH t Ht). lia.
  - destruct Hchoice as [Hc|Hc]; subst c; lia.
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
Proof. Admitted. (* CONVERT: tnum_expand_mask_join: Found no subterm matching "wrap ?M1502 (wrap ?M1502 ?M1503)" *)

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

Theorem tnum_variable_raw_amount_bound : forall o w a b k,
  is_word w k -> tnum_gamma w b k ->
  tnum_leb w (tnum_scalar o w k a) (tnum_variable_raw o w a b) = true.
Proof. Admitted. (* CONVERT: tnum_variable_raw_amount_bound: The variable leb_refl was not found in the current environment. *)

Lemma tnum_unknown_equal : forall w a b,
  tnum_subset w b a = true -> tnum_unknown w a = tnum_unknown w b ->
  tnum_subset w a b = true.
Proof. Admitted. (* CONVERT: tnum_unknown_equal: The variable tnum_unknown_from_equation was not found in the current *)

Theorem tnum_rank_equal : forall w a b,
  tnum_leb w a b = true -> tnum_rank w a = tnum_rank w b ->
  tnum_leb w b a = true.
Proof. Admitted. (* CONVERT: tnum_rank_equal: The variable tnum_unknown_monotone was not found in the current *)

Theorem tnum_shift_sound : forall o w a x k f,
  (o = bvshl \/ o = bvlshr \/ o = bvashr) ->
  word_fun2 o = Some f -> is_word w x -> is_word w k -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shift o w a k) (eval_binary_tag f w x k).
Proof. Admitted. (* CONVERT: tnum_shift_sound: Illegal application (Non-functional construction): *)

Theorem tnum_scalar_agrees : forall o w f k x,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w k -> is_word w x ->
  tnum_scalar_value o w k x = eval_binary_tag f w x k.
Proof. Admitted. (* CONVERT: tnum_scalar_agrees: eval_binary_tag has function type but binary_tag is expected. *)

Theorem tnum_variable_sound : forall o w f a b x k,
  tnum_shift_op o -> word_fun2 o = Some f ->
  is_word w x -> is_word w k -> tnum_gamma w a x -> tnum_gamma w b k ->
  tnum_gamma w (tnum_variable o w a b) (eval_binary_tag f w x k).
Proof. Admitted. (* CONVERT: tnum_variable_sound: The reference tnum_variable_c was not found in the current *)

Theorem tnum_compare_sound : forall o w f a b x y,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_compare o w a b) (if eval_comparison_tag f w x y then 1 else 0).
Proof. Admitted. (* CONVERT: tnum_compare_sound: Found no subterm matching "wrap w x" in the current goal. *)

Theorem tnum_count_sound : forall o w f x,
  (o = bvclz \/ o = bvctz \/ o = bvpopcnt) -> word_fun1 o = Some f ->
  tnum_gamma w (tnum_count w) (eval_unary_tag f w x).
Proof.
  intros o w f x [Ho|[Ho|Ho]] Hf; subst o; injection Hf as <-;
    apply tnum_upper_sound; first [apply wclz_range|apply tnum_ctz_range|apply wpopcnt_range].
Qed.

Local Open Scope nat_scope.

Theorem tnum_rank_equation : forall w a,
  tnum_rank w a = tnum_unknown w (zeros a) + tnum_unknown w (ones a).
Proof. Admitted. (* CONVERT: tnum_rank_equation: The reference tnum_rank_c was not found in the current environment. *)



Theorem tnum_rank_monotone : forall w a b,
  tnum_leb w a b = true -> tnum_rank w a <= tnum_rank w b.
Proof. Admitted. (* CONVERT: tnum_rank_monotone: The variable tnum_unknown_monotone was not found in the current *)

Theorem tnum_rank_bounded : forall w a, tnum_rank w a <= 2 * Pos.to_nat w.
Proof. Admitted. (* CONVERT: tnum_rank_bounded: The variable tnum_unknown_from_equation was not found in the current *)
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

Lemma tnum_unknown_monotone : forall w a b,
  tnum_subset w b a = true -> tnum_unknown w a <= tnum_unknown w b.
Proof. Admitted. (* CONVERT: tnum_unknown_monotone: The variable tnum_unknown_from_equation was not found in the current environment. *)



Fixpoint tnum_unknown_from (n i : nat) (m : Z) : nat :=
  match n with
  | O => O
  | S n => let rest := tnum_unknown_from n (S i) m in
    if Z.testbit m (Z.of_nat i) then rest else S rest
  end.

Local Open Scope Z_scope.

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
Proof. Admitted. (* CONVERT: tnum_mul_acc_runs_sound: The reference tnum_mul_acc_step_c was not found in the current *)

Theorem tnum_unknown_from_equation : forall n i m,
  tnum_unknown_from n i m =
  length (filter (fun j => negb (Z.testbit m (Z.of_nat j))) (seq i n)).
Proof. Admitted. (* CONVERT: tnum_unknown_from_equation: The reference tnum_unknown_from_c was not found in the current *)

(* The old bundled dictionary statements below used the removed lattice_laws and
   lub_laws records. Their inclusion, bottom and join obligations now appear in
   WORD_PAYLOAD_LAWS; the reviewed payload interface does not include leastness.
   The retained direct facts include tnum_leb_bits, tnum_gamma_monotone and
   tnum_meet_lower_left.
Theorem tnum_laws : forall w, lattice_laws (tnum_lattice w).
Theorem tnum_lub : forall w, lub_laws (tnum_lattice w).
*)
