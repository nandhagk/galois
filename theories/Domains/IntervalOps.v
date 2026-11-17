(** * Word interval operations

    Endpoint arithmetic retains finite ranges when they fit the word width.
    For example, adding [1, 4] to [2, 5] yields [3, 9] at width eight.
    Builds on: Interval and the fixed-width word operations. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word Fun Testbit Arith Op.
From Galois.Domains Require Import Interval IntervalSig ThresholdsSig ValueSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Datatypes.
  TimeFun Corelib.Init.Datatypes.xorb.
End Datatypes.
Module Bool.
  TimeFun Bool.eqb.
End Bool.

(** Left shifts use constant-cost doubling at each nonnegative shift step. *)
Lemma interval_shiftl_time : forall z k, 0 <= k ->
  (Std.Z.T_shiftl z k <= 8 * N.of_nat (Z.to_nat k + 1))%N.
Proof.
  intros z [|p|p] Hk; [| |lia].
  - time_unfold Std.Z.T_shiftl. time_cbn. nia.
  - pose proof (Std.Pos.T_iter_le (Z.mul 2) (fun x => Std.Z.T_mul 2 x) (fun _ => True)
      3 z p (fun _ _ => Logic.I) (fun x _ => Std.Z.T_mul_two_le x) Logic.I) as Hiter.
    time_unfold Std.Z.T_shiftl. time_cbn. cbn [Z.to_nat].
    rewrite Nat2N.inj_add.
    change (N.of_nat (Pos.to_nat p)) with (N.of_nat (N.to_nat (N.pos p))).
    rewrite N2Nat.id. nia.
Qed.

(** Halving preserves a nonnegative endpoint. *)
Lemma interval_div2_nonnegative : forall z, 0 <= z -> 0 <= Z.div2 z.
Proof.
  intros [|[p|p|]|p] Hz; cbn [Z.div2]; lia.
Qed.

(** Halving a nonnegative endpoint reads only the outer constructor. *)
Lemma interval_div2_time : forall z, 0 <= z -> (Std.Z.T_div2 z <= 4)%N.
Proof.
  intros [|[p|p|]|p] Hz; try lia; time_unfold Std.Z.T_div2; time_cbn; time_pose; nia.
Qed.

(** Logical right shifts use constant-cost halving at each nonnegative shift step. *)
Lemma interval_shiftr_time : forall z k, 0 <= z -> 0 <= k ->
  (Std.Z.T_shiftr z k <= 8 * N.of_nat (Z.to_nat k + 1))%N.
Proof.
  intros z [|p|p] Hz Hk; [| |lia].
  - time_unfold Std.Z.T_shiftr. time_unfold Std.Z.T_shiftl. time_cbn. time_pose. nia.
  - pose proof (Std.Pos.T_iter_le Z.div2 (fun x => Std.Z.T_div2 x) (fun x => 0 <= x)
      4 z p interval_div2_nonnegative interval_div2_time Hz) as Hiter.
    time_unfold Std.Z.T_shiftr. time_unfold Std.Z.T_shiftl. time_cbn. time_pose.
    cbn [Z.to_nat]. rewrite Nat2N.inj_add.
    change (N.of_nat (Pos.to_nat p)) with (N.of_nat (N.to_nat (N.pos p))).
    rewrite N2Nat.id. nia.
Qed.

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

Definition interval_neg_ref (w : width) (a : itv) : itv :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.eqb hi 0 then I (Fin 0) (Fin 0)
    else if Z.ltb 0 lo then interval_checked w (modulus w - hi) (modulus w - lo)
    else interval_top w
  | None => interval_top w
  end.

Definition interval_neg (w : width) (a : itv) : itv :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.eqb hi 0 then I (Fin 0) (Fin 0)
    else if Z.ltb 0 lo then
      let M := modulus w in interval_checked w (M - hi) (M - lo)
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

Definition interval_shl_ref (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (la * 2 ^ lb) (ha * 2 ^ hb) else interval_top w
  | _, _ => interval_top w
  end.

(** Negative upper counts keep the original zero-power endpoint on raw intervals. *)
Definition interval_shl (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (Z.shiftl la lb) (if Z.leb 0 hb then Z.shiftl ha hb else 0)
    else interval_top w
  | _, _ => interval_top w
  end.

Definition interval_lshr_ref (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (la / 2 ^ hb) (ha / 2 ^ lb) else interval_top w
  | _, _ => interval_top w
  end.

(** Negative upper counts keep the original division-by-zero endpoint on raw intervals. *)
Definition interval_lshr (w : width) (a b : itv) : itv :=
  match interval_finite_helper a, interval_finite_helper b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (if Z.leb 0 hb then Z.shiftr la hb else 0) (Z.shiftr ha lb)
    else interval_top w
  | _, _ => interval_top w
  end.

Definition interval_sign_ref (w : width) (a : itv) : option bool :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.ltb hi (half w) then Some false
    else if Z.leb (half w) lo then Some true else None
  | None => None
  end.

Definition interval_sign (w : width) (a : itv) : option bool :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    let h := half w in
    if Z.ltb hi h then Some false
    else if Z.leb h lo then Some true else None
  | None => None
  end.

Definition interval_signed_ref (w : width) (a : itv) : option (Z * Z) :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    if Z.ltb hi (half w) then Some (lo, hi)
    else if Z.leb (half w) lo then Some (lo - modulus w, hi - modulus w)
    else None
  | None => None
  end.

Definition interval_signed (w : width) (a : itv) : option (Z * Z) :=
  match interval_finite_helper a with
  | Some (lo, hi) =>
    let h := half w in
    if Z.ltb hi h then Some (lo, hi)
    else if Z.leb h lo then
      let M := modulus w in Some (lo - M, hi - M)
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
  (match Scalar.interval_singleton b with
   | Some c =>
     match interval_finite_helper a with
     | Some (lo, hi) =>
       if Z.eqb lo c then Scalar.interval_meet a (I (Fin (c + 1)) PosInf)
       else if Z.eqb hi c then Scalar.interval_meet a (I NegInf (Fin (c - 1)))
       else a
     | None => a
     end
   | None => a
   end,
   match Scalar.interval_singleton a with
   | Some c =>
     match interval_finite_helper b with
     | Some (lo, hi) =>
       if Z.eqb lo c then Scalar.interval_meet b (I (Fin (c + 1)) PosInf)
       else if Z.eqb hi c then Scalar.interval_meet b (I NegInf (Fin (c - 1)))
       else b
     | None => b
     end
   | None => b
   end).

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

Module IntervalOpsSound (T : THRESHOLDS) (Scalar : INTERVAL_SCALAR_OPS T).
  Include IntervalOpsCode T Scalar.
  Include Scalar.

  (** Sharing width-dependent constants preserves the original endpoint formulas. *)
  Lemma interval_neg_agrees : forall w a, interval_neg w a = interval_neg_ref w a.
  Proof.
    reflexivity.
  Qed.

  (** Sharing the signed midpoint preserves the sign test. *)
  Lemma interval_sign_agrees : forall w a, interval_sign w a = interval_sign_ref w a.
  Proof.
    reflexivity.
  Qed.

  (** Sharing width constants preserves conversion to signed endpoints. *)
  Lemma interval_signed_agrees : forall w a, interval_signed w a = interval_signed_ref w a.
  Proof.
    reflexivity.
  Qed.

  (** Bit shifts preserve the old product endpoints even for malformed raw intervals. *)
  Lemma interval_shl_agrees : forall w a b, interval_shl w a b = interval_shl_ref w a b.
  Proof.
    intros w a b. unfold interval_shl, interval_shl_ref.
    destruct (interval_finite_helper a) as [[la ha]|];
      destruct (interval_finite_helper b) as [[lb hb]|]; try reflexivity.
    destruct (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w)) eqn:Hguard;
      [|reflexivity].
    repeat rewrite andb_true_iff in Hguard. destruct Hguard as [[_ Hlb] _].
    apply Z.leb_le in Hlb. rewrite (Z.shiftl_mul_pow2 la lb) by exact Hlb.
    destruct (Z.leb 0 hb) eqn:Hhb.
    - apply Z.leb_le in Hhb. now rewrite Z.shiftl_mul_pow2 by exact Hhb.
    - apply Z.leb_gt in Hhb. rewrite (Z.pow_neg_r 2 hb) by exact Hhb.
      now rewrite Z.mul_0_r.
  Qed.

  (** Bit shifts preserve the old quotient endpoints even for malformed raw intervals. *)
  Lemma interval_lshr_agrees : forall w a b, interval_lshr w a b = interval_lshr_ref w a b.
  Proof.
    intros w a b. unfold interval_lshr, interval_lshr_ref.
    destruct (interval_finite_helper a) as [[la ha]|];
      destruct (interval_finite_helper b) as [[lb hb]|]; try reflexivity.
    destruct (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w)) eqn:Hguard;
      [|reflexivity].
    repeat rewrite andb_true_iff in Hguard. destruct Hguard as [[_ Hlb] _].
    apply Z.leb_le in Hlb. rewrite (Z.shiftr_div_pow2 ha lb) by exact Hlb.
    destruct (Z.leb 0 hb) eqn:Hhb.
    - apply Z.leb_le in Hhb. now rewrite Z.shiftr_div_pow2 by exact Hhb.
    - apply Z.leb_gt in Hhb. rewrite (Z.pow_neg_r 2 hb) by exact Hhb.
      now rewrite Z.div_0_r.
  Qed.

  (** * Word interval membership *)

  (** Word membership uses normalized integers and reflected endpoint comparisons. *)
  Definition interval_pgamma (w : positive) (a : itv) (z : Z) : Prop :=
    Word.is_word w z /\ match a with
    | IBot => False
    | I lo hi => bound_leb lo (Fin z) = true /\ bound_leb (Fin z) hi = true
    end.

  (** Reflected endpoint membership is the public interval meaning. *)
  Lemma interval_pgamma_spec : forall w a z, interval_pgamma w a z <->
    Word.is_word w z /\ match a with IBot => False | I lo hi => in_bnd lo hi z end.
  Proof.
    intros w [|[|lo|] [|hi|]] z; unfold interval_pgamma, in_bnd;
      cbn [bound_leb]; rewrite ?Z.leb_le; intuition congruence.
  Qed.

  (** Every bound is below itself. *)
  Theorem bound_leb_refl : forall a, bound_leb a a = true.
  Proof.
    intros [|z|]; cbn; try reflexivity.
    apply Z.leb_refl.
  Qed.

  (** Bound comparison is transitive. *)
  Theorem bound_leb_trans : forall a b c,
    bound_leb a b = true -> bound_leb b c = true -> bound_leb a c = true.
  Proof.
    intros [|x|] [|y|] [|z|]; cbn; try discriminate; try reflexivity.
    intros Hxy Hyz. apply Z.leb_le in Hxy. apply Z.leb_le in Hyz.
    apply Z.leb_le. lia.
  Qed.

  (** Any two bounds are comparable. *)
  Theorem bound_leb_total : forall a b, bound_leb a b = true \/ bound_leb b a = true.
  Proof.
    intros [|x|] [|y|]; cbn; try (now left); try (now right).
    destruct (Z.leb x y) eqn:Hxy; [now left|right].
    apply Z.leb_gt in Hxy. apply Z.leb_le. lia.
  Qed.

  (** The minimum is below its left input. *)
  Theorem bound_min_lower_l : forall a b, bound_leb (bound_min a b) a = true.
  Proof.
    intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
    - apply bound_leb_refl.
    - destruct (bound_leb_total a b) as [H|H]; congruence.
  Qed.

  (** The minimum is below its right input. *)
  Theorem bound_min_lower_r : forall a b, bound_leb (bound_min a b) b = true.
  Proof.
    intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
    - exact Hab.
    - apply bound_leb_refl.
  Qed.

  (** A common lower bound is below the minimum. *)
  Theorem bound_min_greatest : forall a b c,
    bound_leb c a = true -> bound_leb c b = true -> bound_leb c (bound_min a b) = true.
  Proof.
    intros a b c Ha Hb. unfold bound_min. destruct (bound_leb a b); assumption.
  Qed.

  (** The maximum is above its left input. *)
  Theorem bound_max_upper_l : forall a b, bound_leb a (bound_max a b) = true.
  Proof.
    intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
    - exact Hab.
    - apply bound_leb_refl.
  Qed.

  (** The maximum is above its right input. *)
  Theorem bound_max_upper_r : forall a b, bound_leb b (bound_max a b) = true.
  Proof.
    intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
    - apply bound_leb_refl.
    - destruct (bound_leb_total a b) as [H|H]; congruence.
  Qed.

  (** The maximum is below every common upper bound. *)
  Theorem bound_max_least : forall a b c,
    bound_leb a c = true -> bound_leb b c = true -> bound_leb (bound_max a b) c = true.
  Proof.
    intros a b c Ha Hb. unfold bound_max. destruct (bound_leb a b); assumption.
  Qed.

  (** Every normalized word belongs to its width-specific top. *)
  Theorem interval_top_sound : forall w z,
    is_word w z -> interval_pgamma w (interval_top w) z.
  Proof.
    intros w z Hword. split; [exact Hword|].
    unfold interval_top. cbn [bound_leb].
    destruct Hword as [Hlower Hupper]. split; apply Z.leb_le; lia.
  Qed.

  (** A constant contains its wrapped integer. *)
  Theorem interval_const_sound : forall w z,
    interval_pgamma w (interval_const w z) (wrap w z).
  Proof.
    intros w z. split; [apply wrap_is_word|].
    unfold interval_const. cbn [bound_leb]. now rewrite Z.leb_refl.
  Qed.

  (** Raw interval inclusion retains every represented word. *)
  Lemma interval_gamma_mono : forall w a b z,
    interval_leb a b = true -> interval_pgamma w a z -> interval_pgamma w b z.
  Proof.
    intros w [|la ha] [|lb hb] z Hle [Hw Hgamma]; try contradiction; try discriminate.
    cbn in Hle. apply andb_true_iff in Hle as [Hlower Hupper].
    destruct Hgamma as [Hlo Hhi]. split; [exact Hw|].
    split; eapply bound_leb_trans; eassumption.
  Qed.

  (** Joining retains either operand's concrete words. *)
  Theorem interval_join_sound : forall w a b z,
    interval_pgamma w a z \/ interval_pgamma w b z ->
    interval_pgamma w (interval_join a b) z.
  Proof.
    intros w a b z [Ha|Hb].
    - eapply interval_gamma_mono; [|exact Ha].
      destruct a as [|la ha], b as [|lb hb]; cbn; try reflexivity;
        try (now rewrite !bound_leb_refl).
      apply andb_true_iff. split; [apply bound_min_lower_l|apply bound_max_upper_l].
    - eapply interval_gamma_mono; [|exact Hb].
      destruct a as [|la ha], b as [|lb hb]; cbn; try reflexivity;
        try (now rewrite !bound_leb_refl).
      apply andb_true_iff. split; [apply bound_min_lower_r|apply bound_max_upper_r].
  Qed.

  (** Raw intersection retains common concrete words. *)
  Theorem interval_meet_sound : forall w a b z,
    interval_pgamma w a z -> interval_pgamma w b z ->
    interval_pgamma w (interval_meet a b) z.
  Proof.
    intros w [|la ha] [|lb hb] z [Hw Ha] [_ Hb]; try contradiction.
    destruct Ha as [Hla Hha], Hb as [Hlb Hhb].
    assert (Hlo : bound_leb (bound_max la lb) (Fin z) = true).
    { apply bound_max_least; assumption. }
    assert (Hhi : bound_leb (Fin z) (bound_min ha hb) = true).
    { apply bound_min_greatest; assumption. }
    assert (Hordered : bound_leb (bound_max la lb) (bound_min ha hb) = true).
    { eapply bound_leb_trans; eassumption. }
    assert (Hnonempty : bounds_nonempty (bound_max la lb) (bound_min ha hb) = true).
    { destruct (bound_max la lb), (bound_min ha hb); cbn in *;
        try discriminate; assumption. }
    unfold interval_meet. rewrite Hnonempty. split; [exact Hw|]. now split.
  Qed.

  (** Clipping retains every represented word at its original width. *)
  Theorem interval_clip_sound : forall w a z,
    interval_pgamma w a z -> interval_pgamma w (interval_clip w a) z.
  Proof.
    intros w a z Ha. apply interval_meet_sound; [exact Ha|].
    apply interval_top_sound. exact (proj1 Ha).
  Qed.

  (** Finite observations bound every represented word. *)
  Theorem interval_finite_sound : forall w a lo hi z,
    interval_pgamma w a z -> interval_finite_helper a = Some (lo, hi) -> lo <= z <= hi.
  Proof.
    intros w [|[|l|] [|h|]] lo hi z Hgamma Hfinite;
      cbn [interval_finite_helper] in Hfinite; try discriminate.
    inversion Hfinite; subst lo hi. destruct Hgamma as [_ [Hlo Hhi]].
    cbn [bound_leb] in Hlo, Hhi. apply Z.leb_le in Hlo, Hhi. lia.
  Qed.

  (** A singleton observation identifies every represented word. *)
  Theorem interval_singleton_sound : forall w a x c,
    interval_pgamma w a x -> interval_singleton a = Some c -> x = c.
  Proof.
    intros w a x c Ha Hsingle. unfold interval_singleton, interval_finite in Hsingle.
    destruct (interval_finite_helper a) as [[lo hi]|] eqn:Hfinite; [|discriminate].
    destruct (Z.eqb lo hi) eqn:Heq; [|discriminate].
    inversion Hsingle; subst c. apply Z.eqb_eq in Heq.
    pose proof (interval_finite_sound w a lo hi x Ha Hfinite). lia.
  Qed.

  (** A checked range contains every normalized word between its endpoints. *)
  Theorem interval_checked_sound w lo hi z :
    is_word w z -> lo <= z <= hi -> interval_pgamma w (interval_checked w lo hi) z.
  Proof.
    intros Hword Hz. unfold interval_checked.
    destruct (Z.leb 0 lo && Z.ltb hi (modulus w))%bool; [|now apply interval_top_sound].
    split; [exact Hword|]. cbn. split; apply Z.leb_le; lia.
  Qed.

  (** A checked range also contains the wrapped value of every integer between its endpoints. *)
  Theorem interval_checked_wrap_sound w lo hi z :
    lo <= z <= hi -> interval_pgamma w (interval_checked w lo hi) (wrap w z).
  Proof.
    intro Hbounds. unfold interval_checked.
    destruct (Z.leb 0 lo && Z.ltb hi (modulus w))%bool eqn:Hfit;
      [|apply interval_top_sound, wrap_is_word].
    apply andb_true_iff in Hfit as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    assert (Hword : is_word w z) by (split; lia).
    rewrite (wrap_id w z Hword). split; [exact Hword|].
    cbn. split; apply Z.leb_le; lia.
  Qed.

  (** Addition contains every modular sum of represented operands, at any operand widths. *)
  Theorem interval_add_sound w wa wb a b x y :
    interval_pgamma wa a x -> interval_pgamma wb b y ->
    interval_pgamma w (interval_add w a b) (wrap w (x + y)).
  Proof.
    intros Ha Hb. unfold interval_add.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wrap_is_word).
    pose proof (interval_finite_sound wa a la ha x Ha Hfa).
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb).
    apply interval_checked_wrap_sound. lia.
  Qed.

  (** Uniform single-wrap addition retains every modular sum. *)
  Theorem interval_add_modular_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_add_modular w a b) (wrap w (x + y)).
  Proof.
    intros Ha Hb. unfold interval_add_modular.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wrap_is_word).
    pose proof (interval_finite_sound w a la ha x Ha Hfa).
    pose proof (interval_finite_sound w b lb hb y Hb Hfb).
    destruct (Z.leb (modulus w) (la + lb) && Z.ltb (ha + hb) (2 * modulus w))%bool;
      [|now apply (interval_add_sound w w w)].
    replace (x + y) with ((x + y - modulus w) + 1 * modulus w) by ring.
    rewrite wrap_add_modulus. apply interval_checked_wrap_sound. lia.
  Qed.

  (** Subtraction contains every modular difference of represented operands. *)
  Theorem interval_sub_sound w wa wb a b x y :
    interval_pgamma wa a x -> interval_pgamma wb b y ->
    interval_pgamma w (interval_sub w a b) (wrap w (x - y)).
  Proof.
    intros Ha Hb. unfold interval_sub.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wrap_is_word).
    pose proof (interval_finite_sound wa a la ha x Ha Hfa).
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb).
    apply interval_checked_wrap_sound. lia.
  Qed.

  (** Nonnegative endpoint multiplication contains every modular product. *)
  Theorem interval_mul_sound w wa wb a b x y :
    interval_pgamma wa a x -> interval_pgamma wb b y ->
    interval_pgamma w (interval_mul w a b) (wrap w (x * y)).
  Proof.
    intros Ha Hb. unfold interval_mul.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wrap_is_word).
    pose proof (interval_finite_sound wa a la ha x Ha Hfa).
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb).
    destruct (Z.leb 0 la && Z.leb 0 lb)%bool eqn:Hnonneg;
      [|apply interval_top_sound, wrap_is_word].
    apply andb_true_iff in Hnonneg as [Hla Hlb].
    apply Z.leb_le in Hla. apply Z.leb_le in Hlb.
    apply interval_checked_wrap_sound. nia.
  Qed.

  (** Negation retains zero and the reversed strictly positive range. *)
  Theorem interval_neg_sound w a x :
    interval_pgamma w a x -> interval_pgamma w (interval_neg w a) (wrap w (- x)).
  Proof.
    intro Ha. unfold interval_neg.
    destruct (interval_finite_helper a) as [[lo hi]|] eqn:Hfinite;
      [|apply interval_top_sound, wrap_is_word].
    pose proof (interval_finite_sound w a lo hi x Ha Hfinite).
    destruct Ha as [Hword _].
    destruct (Z.eqb hi 0) eqn:Hzero.
    - apply Z.eqb_eq in Hzero. assert (x = 0) by (destruct Hword; lia).
      subst x. rewrite Z.opp_0, wrap_0. split; [apply zero_is_word|].
      cbn. split; reflexivity.
    - destruct (Z.ltb 0 lo); [|apply interval_top_sound, wrap_is_word].
      rewrite <- (wrap_add_modulus w (- x) 1).
      replace (- x + 1 * modulus w) with (modulus w - x) by ring.
      apply interval_checked_wrap_sound. lia.
  Qed.

  (** Concatenation contains every pair of represented operands in the lower operand radix. *)
  Theorem interval_concat_sound rw wa wb a b x y :
    interval_pgamma wa a x -> interval_pgamma wb b y ->
    interval_pgamma rw (interval_concat rw wb a b) (wrap rw (x * modulus wb + y)).
  Proof.
    intros Ha Hb. unfold interval_concat.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wrap_is_word).
    pose proof (interval_finite_sound wa a la ha x Ha Hfa).
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb).
    pose proof (modulus_pos wb).
    apply interval_checked_wrap_sound. nia.
  Qed.

  (** Rewrapping contains every represented input after reduction to the result width. *)
  Theorem interval_rewrap_sound rw w a x :
    interval_pgamma w a x -> interval_pgamma rw (interval_rewrap rw a) (wrap rw x).
  Proof.
    intro Ha. unfold interval_rewrap.
    destruct (interval_finite_helper a) as [[lo hi]|] eqn:Hfinite;
      [|apply interval_top_sound, wrap_is_word].
    pose proof (interval_finite_sound w a lo hi x Ha Hfinite).
    apply interval_checked_wrap_sound. assumption.
  Qed.

  (** Leading-zero counts lie in the closed range from zero to the width. *)
  Theorem interval_clz_sound w x : interval_pgamma w (interval_counts w) (wclz w x).
  Proof.
    pose proof (wclz_range w x) as Hrange.
    split; [apply wclz_is_word|]. cbn. split; apply Z.leb_le; lia.
  Qed.

  (** Population counts lie in the closed range from zero to the width. *)
  Theorem interval_popcnt_sound w x : interval_pgamma w (interval_counts w) (wpopcnt w x).
  Proof.
    pose proof (wpopcnt_range w x) as Hrange.
    split; [apply wpopcnt_is_word|]. cbn. split; apply Z.leb_le; lia.
  Qed.

  (** Trailing-zero counts lie in the closed range from zero to the width. *)
  Theorem interval_ctz_sound w x : interval_pgamma w (interval_counts w) (wctz w x).
  Proof.
    pose proof (wctz_is_word w x) as Hword.
    assert (Hupper : wctz w x <= Zpos w).
    { pose proof (word_fun1_normalised bvctz UCtz w x eq_refl) as Hnorm.
      cbn [eval_unary_tag] in Hnorm.
      destruct (Z.eq_dec (wrap w x) 0) as [Hzero|Hnonzero].
      - rewrite <- Hnorm, Hzero, wctz_zero. lia.
      - pose proof (proj1 (wctz_spec w (wrap w x) (wrap_is_word w x) Hnonzero)) as Hbit.
        rewrite Hnorm in Hbit.
        destruct (Z_le_gt_dec (Zpos w) (wctz w x)) as [Hhigh|Hlow]; [|lia].
        rewrite (word_bits_high w (wrap w x) (wctz w x) (wrap_is_word w x) Hhigh) in Hbit.
        discriminate. }
    split; [exact Hword|]. cbn. split; apply Z.leb_le; destruct Hword; lia.
  Qed.

  (** Unsigned division includes the all-ones result for a zero divisor. *)
  Theorem interval_udiv_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_udiv w a b) (wudiv w x y).
  Proof.
    intros Ha Hb. unfold interval_udiv.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wudiv_is_word).
    pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
    destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
    destruct (Z.leb 0 la && Z.ltb 0 lb)%bool eqn:Hvalid.
    - apply andb_true_iff in Hvalid as [Hla Hlb]. apply Z.leb_le in Hla.
      apply Z.ltb_lt in Hlb. apply interval_checked_sound; [apply wudiv_is_word|].
      rewrite (wudiv_spec w x y Hwordx Hwordy ltac:(lia)).
      split.
      + eapply (Z.le_trans _ (x / hb));
          [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
      + eapply (Z.le_trans _ (x / lb));
          [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
    - destruct (Z.leb 0 la && Z.eqb lb 0 && Z.ltb 0 hb)%bool eqn:Hcontains.
      + repeat rewrite andb_true_iff in Hcontains. destruct Hcontains as [[Hla Hlb] Hhb].
        apply Z.leb_le in Hla. apply Z.eqb_eq in Hlb. apply Z.ltb_lt in Hhb.
        apply interval_checked_sound; [apply wudiv_is_word|].
        destruct (Z.eqb y 0) eqn:Hzero.
        * apply Z.eqb_eq in Hzero. subst y. rewrite wudiv_zero.
          pose proof (Z.div_le_upper_bound la hb (modulus w - 1) Hhb
            ltac:(pose proof (modulus_pos w); destruct Hwordx; nia)). lia.
        * apply Z.eqb_neq in Hzero. rewrite (wudiv_spec w x y Hwordx Hwordy Hzero).
          assert (Hlower : la / hb <= x / y).
          { eapply (Z.le_trans _ (x / hb));
              [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; destruct Hwordy; lia]. }
          pose proof (wudiv_is_word w x y) as Hword.
          rewrite (wudiv_spec w x y Hwordx Hwordy Hzero) in Hword. destruct Hword. lia.
      + destruct (Z.eqb lb 0 && Z.eqb hb 0)%bool eqn:Hzero;
          [|apply interval_top_sound, wudiv_is_word].
        apply andb_true_iff in Hzero as [Hlb Hhb]. apply Z.eqb_eq in Hlb. apply Z.eqb_eq in Hhb.
        assert (y = 0) by lia. subst y. rewrite wudiv_zero.
        split; [apply ones_is_word|]. cbn. now rewrite Z.leb_refl.
  Qed.

  (** Remainders retain the exact common-quotient range when both endpoints have one quotient. *)
  Theorem interval_urem_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_urem w a b) (wurem w x y).
  Proof.
    intros Ha Hb. unfold interval_urem.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wurem_is_word).
    pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
    destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
    destruct (Z.leb 0 la && Z.ltb 0 lb && Z.eqb (la / hb) (ha / lb))%bool eqn:Hexact.
    - repeat rewrite andb_true_iff in Hexact. destruct Hexact as [[Hla Hlb] Hquot].
      apply Z.leb_le in Hla. apply Z.ltb_lt in Hlb. apply Z.eqb_eq in Hquot.
      assert (Hlower : la / hb <= x / y).
      { eapply (Z.le_trans _ (x / hb));
          [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia]. }
      assert (Hupper : x / y <= ha / lb).
      { eapply (Z.le_trans _ (x / lb));
          [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia]. }
      assert (Hq : x / y = la / hb) by lia.
      assert (Hqnonnegative : 0 <= la / hb) by (apply Z.div_pos; lia).
      apply interval_checked_sound; [apply wurem_is_word|].
      rewrite (wurem_spec w x y Hwordx Hwordy ltac:(lia)).
      pose proof (Z.div_mod x y ltac:(lia)) as Hdivision. rewrite Hq in Hdivision. nia.
    - apply interval_checked_sound; [apply wurem_is_word|].
      destruct (Z.ltb 0 lb) eqn:Hpositive.
      + apply Z.ltb_lt in Hpositive.
        rewrite (wurem_spec w x y Hwordx Hwordy ltac:(lia)).
        pose proof (Z.mod_pos_bound x y ltac:(lia)).
        pose proof (Z.mod_le x y (proj1 Hwordx) ltac:(lia)).
        split; [lia|apply Z.min_glb; lia].
      + destruct (Z.eq_dec y 0) as [->|Hnonzero].
        * rewrite wurem_zero, (wrap_id w x Hwordx). destruct Hwordx. lia.
        * rewrite (wurem_spec w x y Hwordx Hwordy Hnonzero).
          pose proof (Z.mod_pos_bound x y ltac:(destruct Hwordy; lia)).
          pose proof (Z.mod_le x y (proj1 Hwordx) ltac:(destruct Hwordy; lia)). lia.
  Qed.
  (** * Bitwise bounds *)

  (** Complementing a normalized word reverses its position in the unsigned range. *)
  Theorem interval_complement_word w x :
    is_word w x -> wnot w x = modulus w - 1 - x.
  Proof.
    intro Hword. rewrite wnot_lnot, (wrap_id w x Hword), lnot_value.
    rewrite <- (wrap_add_modulus w (- x - 1) 1).
    replace (- x - 1 + 1 * modulus w) with (modulus w - 1 - x) by ring.
    apply wrap_id. destruct Hword. split; lia.
  Qed.

  (** Complement contains every complemented represented word. *)
  Theorem interval_not_sound w a x :
    interval_pgamma w a x -> interval_pgamma w (interval_not w a) (wnot w x).
  Proof.
    intro Ha. unfold interval_not.
    destruct (interval_finite_helper a) as [[lo hi]|] eqn:Hfinite;
      [|apply interval_top_sound, wnot_is_word].
    pose proof (interval_finite_sound w a lo hi x Ha Hfinite).
    rewrite wnot_lnot, (wrap_id w x (proj1 Ha)), lnot_value.
    rewrite <- (wrap_add_modulus w (- x - 1) 1).
    replace (- x - 1 + 1 * modulus w) with (modulus w - 1 - x) by ring.
    apply interval_checked_wrap_sound. lia.
  Qed.

  Local Lemma wand_words w x y :
    is_word w x -> is_word w y -> wand w x y = Z.land x y.
  Proof.
    intros Hx Hy. apply (word_ext w); [apply wand_is_word| |].
    - apply word_of_bits. intros i Hi. rewrite Z.land_spec.
      rewrite (word_bits_high w x i Hx Hi). reflexivity.
    - intros i Hi. rewrite testbit_wand by assumption. symmetry. apply Z.land_spec.
  Qed.

  Local Lemma wor_words w x y :
    is_word w x -> is_word w y -> wor w x y = Z.lor x y.
  Proof.
    intros Hx Hy. apply (word_ext w); [apply wor_is_word| |].
    - apply word_of_bits. intros i Hi. rewrite Z.lor_spec.
      rewrite (word_bits_high w x i Hx Hi), (word_bits_high w y i Hy Hi). reflexivity.
    - intros i Hi. rewrite testbit_wor by assumption. symmetry. apply Z.lor_spec.
  Qed.

  Local Lemma wxor_words w x y :
    is_word w x -> is_word w y -> wxor w x y = Z.lxor x y.
  Proof.
    intros Hx Hy. apply (word_ext w); [apply wxor_is_word| |].
    - apply word_of_bits. intros i Hi. rewrite Z.lxor_spec.
      rewrite (word_bits_high w x i Hx Hi), (word_bits_high w y i Hy Hi). reflexivity.
    - intros i Hi. rewrite testbit_wxor by assumption. symmetry. apply Z.lxor_spec.
  Qed.

  (** Conjunction is bounded by either represented nonnegative operand. *)
  Theorem interval_and_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_and w a b) (wand w x y).
  Proof.
    intros Ha Hb. unfold interval_and.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wand_is_word).
    pose proof (interval_finite_sound w a la ha x Ha Hfa).
    pose proof (interval_finite_sound w b lb hb y Hb Hfb).
    destruct Ha as [Hwordx _], Hb as [Hwordy _].
    apply interval_checked_sound; [apply wand_is_word|].
    rewrite wand_words by assumption.
    pose proof (Z.sub_land_same_l x y) as Hx.
    pose proof (Z.sub_land_same_l y x) as Hy. rewrite Z.land_comm in Hy.
    assert (Hnonnegx : 0 <= Z.land x (Z.lnot y)).
    { apply Z.land_nonneg. left. exact (proj1 Hwordx). }
    assert (Hnonnegy : 0 <= Z.land y (Z.lnot x)).
    { apply Z.land_nonneg. left. exact (proj1 Hwordy). }
    assert (Hnonneg : 0 <= Z.land x y).
    { apply Z.land_nonneg. left. exact (proj1 Hwordx). }
    split; [exact Hnonneg|]. apply Z.min_glb; lia.
  Qed.

  Local Lemma interval_mask_covers x y hi :
    0 <= x <= hi -> 0 <= y <= hi ->
    0 <= Z.lor x y <= interval_mask hi /\ 0 <= Z.lxor x y <= interval_mask hi.
  Proof.
    intros Hx Hy. unfold interval_mask. destruct (Z.eqb hi 0) eqn:Hzero.
    - apply Z.eqb_eq in Hzero.
      assert (Hxzero : x = 0) by lia. assert (Hyzero : y = 0) by lia.
      subst x y. cbn. lia.
    - set (n := Z.log2 hi + 1).
      assert (Hn : 0 <= n) by (unfold n; pose proof (Z.log2_nonneg hi); lia).
      assert (Hmask : 0 <= Z.ones n).
      { rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). lia. }
      assert (Hlogx : Z.log2 x < n) by
        (unfold n; pose proof (Z.log2_le_mono x hi ltac:(lia)); lia).
      assert (Hlogy : Z.log2 y < n) by
        (unfold n; pose proof (Z.log2_le_mono y hi ltac:(lia)); lia).
      assert (Hor : Z.lor (Z.lor x y) (Z.ones n) = Z.ones n).
      { rewrite <- Z.lor_assoc, Z.lor_ones_low by lia. apply Z.lor_ones_low; lia. }
      assert (Hlor : 0 <= Z.lor x y) by (apply Z.lor_nonneg; lia).
      assert (Hmaskdiff : 0 <= Z.land (Z.ones n) (Z.lnot (Z.lor x y))).
      { apply Z.land_nonneg. now left. }
      pose proof (Z.sub_lor_l_same_l (Z.ones n) (Z.lor x y)) as Hdiff.
      rewrite Hor in Hdiff.
      assert (Hand : 0 <= Z.land x y) by (apply Z.land_nonneg; lia).
      pose proof (Z.sub_lor_land x y) as Hxor.
      assert (Hxor_nonneg : 0 <= Z.lxor x y) by (apply Z.lxor_nonneg; lia).
      lia.
  Qed.

  (** The enclosing mask contains both disjunction and exclusive disjunction results. *)
  Theorem interval_or_xor_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_or_xor w a b) (wor w x y) /\
    interval_pgamma w (interval_or_xor w a b) (wxor w x y).
  Proof.
    intros Ha Hb. unfold interval_or_xor.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (split; apply interval_top_sound; first [apply wor_is_word|apply wxor_is_word]).
    pose proof (interval_finite_sound w a la ha x Ha Hfa).
    pose proof (interval_finite_sound w b lb hb y Hb Hfb).
    destruct Ha as [Hwordx _], Hb as [Hwordy _].
    pose proof (proj1 Hwordx). pose proof (proj1 Hwordy).
    pose proof (interval_mask_covers x y (Z.max ha hb)
      ltac:(pose proof (Z.le_max_l ha hb); lia)
      ltac:(pose proof (Z.le_max_r ha hb); lia)) as [Hor Hxor].
    split; apply interval_checked_sound; try apply wor_is_word; try apply wxor_is_word.
    - now rewrite wor_words by assumption.
    - now rewrite wxor_words by assumption.
  Qed.

  (** * Comparisons and unsigned shifts *)

  (** A decision contains its Boolean result whenever each decided case is justified. *)
  Theorem interval_truth_sound : forall w decision value,
    (decision = Some true -> value = true) -> (decision = Some false -> value = false) ->
    interval_pgamma w (interval_truth decision) (if value then 1 else 0).
  Proof.
    intros w [[|]|] value Htrue Hfalse; destruct value; cbn in *;
      try (exfalso; specialize (Htrue eq_refl); discriminate);
      try (exfalso; specialize (Hfalse eq_refl); discriminate);
      split; try apply one_is_word; try apply zero_is_word; split; reflexivity.
  Qed.

  (** Boolean complement retains every complemented Boolean input. *)
  Theorem interval_bool_not_sound : forall w a (b : bool),
    interval_pgamma w a (if b then 1 else 0) ->
    interval_pgamma w (interval_bool_not a) (if negb b then 1 else 0).
  Proof.
    intros w a b Ha. unfold interval_bool_not.
    destruct (interval_finite_helper a) as [[lo hi]|] eqn:Hfinite;
      [|apply interval_truth_sound; discriminate].
    pose proof (interval_finite_sound w a lo hi (if b then 1 else 0) Ha Hfinite) as Hbounds.
    destruct (Z.eqb lo 0 && Z.eqb hi 0)%bool eqn:Hzero.
    - apply andb_true_iff in Hzero as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
      destruct b; cbn in Hbounds; [lia|].
      apply interval_truth_sound; [reflexivity|discriminate].
    - destruct (Z.eqb lo 1 && Z.eqb hi 1)%bool eqn:Hone.
      + apply andb_true_iff in Hone as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
        destruct b; cbn in Hbounds; [|lia].
        apply interval_truth_sound; [discriminate|reflexivity].
      + apply interval_truth_sound; discriminate.
  Qed.

  (** Strict comparison contains every comparison of represented unsigned integers. *)
  Theorem interval_ult_sound : forall wa wb a b x y w,
    interval_pgamma wa a x -> interval_pgamma wb b y ->
    interval_pgamma w (interval_ult a b) (if Z.ltb x y then 1 else 0).
  Proof.
    intros wa wb a b x y w Ha Hb. unfold interval_ult.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_truth_sound; discriminate).
    pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
    destruct (Z.ltb ha lb) eqn:Htrue.
    - apply Z.ltb_lt in Htrue. apply interval_truth_sound; [|discriminate].
      intros _. apply Z.ltb_lt. lia.
    - destruct (Z.leb hb la) eqn:Hfalse.
      + apply Z.leb_le in Hfalse. apply interval_truth_sound; [discriminate|].
        intros _. apply Z.ltb_ge. lia.
      + apply interval_truth_sound; discriminate.
  Qed.

  (** Non-strict comparison contains every comparison of represented unsigned integers. *)
  Theorem interval_ule_sound : forall wa wb a b x y w,
    interval_pgamma wa a x -> interval_pgamma wb b y ->
    interval_pgamma w (interval_ule a b) (if Z.leb x y then 1 else 0).
  Proof.
    intros wa wb a b x y w Ha Hb. unfold interval_ule.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_truth_sound; discriminate).
    pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
    destruct (Z.leb ha lb) eqn:Htrue.
    - apply Z.leb_le in Htrue. apply interval_truth_sound; [|discriminate].
      intros _. apply Z.leb_le. lia.
    - destruct (Z.ltb hb la) eqn:Hfalse.
      + apply Z.ltb_lt in Hfalse. apply interval_truth_sound; [discriminate|].
        intros _. apply Z.leb_gt. lia.
      + apply interval_truth_sound; discriminate.
  Qed.

  (** Equality contains every equality test of represented integers. *)
  Theorem interval_eq_sound : forall wa wb a b x y w,
    interval_pgamma wa a x -> interval_pgamma wb b y ->
    interval_pgamma w (interval_eq a b) (if Z.eqb x y then 1 else 0).
  Proof.
    intros wa wb a b x y w Ha Hb. unfold interval_eq.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_truth_sound; discriminate).
    pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
    destruct (Z.ltb ha lb || Z.ltb hb la)%bool eqn:Hdisjoint.
    - assert (Hneq : x <> y).
      { apply orb_true_iff in Hdisjoint as [Hdisjoint|Hdisjoint];
          apply Z.ltb_lt in Hdisjoint; lia. }
      apply interval_truth_sound; [discriminate|]. intros _. now apply Z.eqb_neq.
    - destruct (Z.eqb la ha && Z.eqb lb hb && Z.eqb la lb)%bool eqn:Hpoint.
      + repeat rewrite andb_true_iff in Hpoint. destruct Hpoint as [[Ha' Hb'] Hab].
        apply Z.eqb_eq in Ha'. apply Z.eqb_eq in Hb'. apply Z.eqb_eq in Hab.
        apply interval_truth_sound; [intros _; apply Z.eqb_eq; lia|discriminate].
      + apply interval_truth_sound; discriminate.
  Qed.

  (** Bounded left shifts contain every modular product by the corresponding power of two. *)
  Theorem interval_shl_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_shl w a b) (wshl w x y).
  Proof.
    intros Ha Hb. rewrite interval_shl_agrees. unfold interval_shl_ref.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wshl_is_word).
    pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
    destruct (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool eqn:Hrange;
      [|apply interval_top_sound, wshl_is_word].
    repeat rewrite andb_true_iff in Hrange. destruct Hrange as [[Hla Hlb] Hhb].
    apply Z.leb_le in Hla. apply Z.leb_le in Hlb. apply Z.ltb_lt in Hhb.
    assert (Hpowlo : 2 ^ lb <= 2 ^ y) by (apply Z.pow_le_mono_r; lia).
    assert (Hpowhi : 2 ^ y <= 2 ^ hb) by (apply Z.pow_le_mono_r; lia).
    assert (Hpowpos : 0 < 2 ^ lb) by (apply Z.pow_pos_nonneg; lia).
    rewrite wshl_value, (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)).
    assert (Hshift : (Zpos w <=? y) = false) by (apply Z.leb_gt; lia).
    rewrite Hshift. apply interval_checked_wrap_sound. nia.
  Qed.

  (** Bounded logical right shifts contain every represented quotient by a power of two. *)
  Theorem interval_lshr_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_lshr w a b) (wlshr w x y).
  Proof.
    intros Ha Hb. rewrite interval_lshr_agrees. unfold interval_lshr_ref.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      try (apply interval_top_sound, wlshr_is_word).
    pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
    destruct (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool eqn:Hrange;
      [|apply interval_top_sound, wlshr_is_word].
    repeat rewrite andb_true_iff in Hrange. destruct Hrange as [[Hla Hlb] Hhb].
    apply Z.leb_le in Hla. apply Z.leb_le in Hlb. apply Z.ltb_lt in Hhb.
    assert (Hpowlo : 2 ^ lb <= 2 ^ y) by (apply Z.pow_le_mono_r; lia).
    assert (Hpowhi : 2 ^ y <= 2 ^ hb) by (apply Z.pow_le_mono_r; lia).
    assert (Hpowpos : 0 < 2 ^ lb) by (apply Z.pow_pos_nonneg; lia).
    apply interval_checked_sound; [apply wlshr_is_word|].
    rewrite wlshr_value, (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)).
    assert (Hshift : (Zpos w <=? y) = false) by (apply Z.leb_gt; lia).
    rewrite Hshift. split.
    - eapply (Z.le_trans _ (x / 2 ^ hb));
        [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
    - eapply (Z.le_trans _ (x / 2 ^ lb));
        [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
  Qed.
  (** * Backward refinements *)

  (** Equality retains a common concrete word in both operands. *)
  Theorem interval_assume_equal_sound w a b z :
    interval_pgamma w a z -> interval_pgamma w b z ->
    interval_pgamma w (fst (interval_assume_equal a b)) z /\
    interval_pgamma w (snd (interval_assume_equal a b)) z.
  Proof.
    intros Ha Hb. split; apply interval_meet_sound; assumption.
  Qed.

  (** Strict unsigned refinement retains every pair satisfying the comparison. *)
  Theorem interval_assume_ult_sound wa wb a b x y :
    interval_pgamma wa a x -> interval_pgamma wb b y -> x < y ->
    interval_pgamma wa (fst (interval_assume_ult a b)) x /\
    interval_pgamma wb (snd (interval_assume_ult a b)) y.
  Proof.
    intros Ha Hb Hlt. unfold interval_assume_ult.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb; cbn; try tauto.
    pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
    split; apply interval_meet_sound; try assumption.
    - split; [exact (proj1 Ha)|]. cbn. split; [reflexivity|apply Z.leb_le; lia].
    - split; [exact (proj1 Hb)|]. cbn. split; [apply Z.leb_le; lia|reflexivity].
  Qed.

  (** Non-strict unsigned refinement retains every pair satisfying the comparison. *)
  Theorem interval_assume_ule_sound wa wb a b x y :
    interval_pgamma wa a x -> interval_pgamma wb b y -> x <= y ->
    interval_pgamma wa (fst (interval_assume_ule a b)) x /\
    interval_pgamma wb (snd (interval_assume_ule a b)) y.
  Proof.
    intros Ha Hb Hle. unfold interval_assume_ule.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb; cbn; try tauto.
    pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
    pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
    split; apply interval_meet_sound; try assumption.
    - split; [exact (proj1 Ha)|]. cbn. split; [reflexivity|apply Z.leb_le; lia].
    - split; [exact (proj1 Hb)|]. cbn. split; [apply Z.leb_le; lia|reflexivity].
  Qed.

  (** Nonwrapping addition refinement retains operands whose sum satisfies the result fact. *)
  Theorem interval_assume_add_sound w a b q x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w q (wrap w (x + y)) ->
    interval_pgamma w (fst (interval_assume_add w a b q)) x /\
    interval_pgamma w (snd (interval_assume_add w a b q)) y.
  Proof.
    intros Ha Hb Hq. unfold interval_assume_add.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      destruct (interval_finite_helper q) as [[lq hq]|] eqn:Hfq; cbn [fst snd]; try tauto.
    destruct (Z.ltb (ha + hb) (modulus w)) eqn:Hfit; cbn [fst snd]; [|tauto].
    apply Z.ltb_lt in Hfit.
    pose proof (interval_finite_sound w a la ha x Ha Hfa).
    pose proof (interval_finite_sound w b lb hb y Hb Hfb).
    pose proof (interval_finite_sound w q lq hq (wrap w (x + y)) Hq Hfq) as Hresult.
    assert (Hword : is_word w (x + y)) by
      (split; pose proof (proj1 (proj1 Ha)); pose proof (proj1 (proj1 Hb)); lia).
    rewrite (wrap_id w _ Hword) in Hresult.
    split; apply interval_meet_sound; try assumption.
    - split; [exact (proj1 Ha)|]. cbn. split; apply Z.leb_le; lia.
    - split; [exact (proj1 Hb)|]. cbn. split; apply Z.leb_le; lia.
  Qed.

  (** Nonwrapping subtraction refinement retains operands satisfying the result fact. *)
  Theorem interval_assume_sub_sound w a b q x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w q (wrap w (x - y)) ->
    interval_pgamma w (fst (interval_assume_sub a b q)) x /\
    interval_pgamma w (snd (interval_assume_sub a b q)) y.
  Proof.
    intros Ha Hb Hq. unfold interval_assume_sub.
    destruct (interval_finite_helper a) as [[la ha]|] eqn:Hfa;
      destruct (interval_finite_helper b) as [[lb hb]|] eqn:Hfb;
      destruct (interval_finite_helper q) as [[lq hq]|] eqn:Hfq; cbn [fst snd]; try tauto.
    destruct (Z.leb hb la) eqn:Hfit; cbn [fst snd]; [|tauto].
    apply Z.leb_le in Hfit.
    pose proof (interval_finite_sound w a la ha x Ha Hfa).
    pose proof (interval_finite_sound w b lb hb y Hb Hfb).
    pose proof (interval_finite_sound w q lq hq (wrap w (x - y)) Hq Hfq) as Hresult.
    assert (Hword : is_word w (x - y)) by
      (destruct (proj1 Ha) as [Hxl Hxh]; destruct (proj1 Hb) as [Hyl Hyh]; split; lia).
    rewrite (wrap_id w _ Hword) in Hresult.
    split; apply interval_meet_sound; try assumption.
    - split; [exact (proj1 Ha)|]. cbn. split; apply Z.leb_le; lia.
    - split; [exact (proj1 Hb)|]. cbn. split; apply Z.leb_le; lia.
  Qed.

  (** Resize refinement uses the result interval only when the operand range already fits. *)
  Theorem interval_assume_rewrap_sound rw w a q x :
    interval_pgamma w a x -> interval_pgamma rw q (wrap rw x) ->
    interval_pgamma w (interval_assume_rewrap rw a q) x.
  Proof.
    intros Ha Hq. unfold interval_assume_rewrap.
    destruct (interval_finite_helper a) as [[lo hi]|] eqn:Hfinite; [|exact Ha].
    destruct (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool eqn:Hfit; [|exact Ha].
    apply andb_true_iff in Hfit as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    pose proof (interval_finite_sound w a lo hi x Ha Hfinite).
    assert (Hword : is_word rw x) by (split; lia).
    rewrite (wrap_id rw x Hword) in Hq.
    apply interval_meet_sound; [exact Ha|]. split; [exact (proj1 Ha)|exact (proj2 Hq)].
  Qed.

  (** Endpoint exclusion retains every represented value different from the excluded integer. *)
  Theorem interval_exclude_sound w a x c :
    interval_pgamma w a x -> x <> c -> interval_pgamma w (interval_exclude a c) x.
  Proof.
    intros Ha Hneq. unfold interval_exclude.
    destruct (interval_finite_helper a) as [[lo hi]|] eqn:Hfinite; [|exact Ha].
    pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
    destruct (Z.eqb lo c) eqn:Hlo.
    - apply Z.eqb_eq in Hlo. apply interval_meet_sound; [exact Ha|].
      split; [exact (proj1 Ha)|]. cbn. split; [apply Z.leb_le; lia|reflexivity].
    - destruct (Z.eqb hi c) eqn:Hhi; [|exact Ha].
      apply Z.eqb_eq in Hhi. apply interval_meet_sound; [exact Ha|].
      split; [exact (proj1 Ha)|]. cbn. split; [reflexivity|apply Z.leb_le; lia].
  Qed.

  (** Disequality excludes each known singleton from the opposite operand. *)
  Theorem interval_assume_neq_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y -> x <> y ->
    interval_pgamma w (fst (interval_assume_neq a b)) x /\
    interval_pgamma w (snd (interval_assume_neq a b)) y.
  Proof.
    intros Ha Hb Hneq. unfold interval_assume_neq. split; cbn [fst snd].
    - destruct (interval_singleton b) as [c|] eqn:Hsingle; [|exact Ha].
      apply interval_exclude_sound; [exact Ha|].
      pose proof (interval_singleton_sound w b y c Hb Hsingle). congruence.
    - destruct (interval_singleton a) as [c|] eqn:Hsingle; [|exact Hb].
      apply interval_exclude_sound; [exact Hb|].
      pose proof (interval_singleton_sound w a x c Ha Hsingle). congruence.
  Qed.

  (** * Signed operations *)

  (** A successful sign observation agrees with every represented concrete sign bit. *)
  Theorem interval_sign_sound w a x sign :
    interval_pgamma w a x -> interval_sign w a = Some sign -> msb w x = sign.
  Proof.
    intros Ha Hsign. unfold interval_sign in Hsign.
    destruct (interval_finite_helper a) as [[lo hi]|] eqn:Hfinite; [|discriminate].
    pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
    rewrite msb_half, (wrap_id w x (proj1 Ha)).
    destruct (Z.ltb hi (half w)) eqn:Hlow.
    - apply Z.ltb_lt in Hlow. inversion Hsign; subst sign.
      assert (Htest : Z.ltb x (half w) = true) by (apply Z.ltb_lt; lia).
      now rewrite Htest.
    - destruct (Z.leb (half w) lo) eqn:Hhigh; [|discriminate].
      apply Z.leb_le in Hhigh. inversion Hsign; subst sign.
      assert (Htest : Z.ltb x (half w) = false) by (apply Z.ltb_ge; lia).
      now rewrite Htest.
  Qed.

  (** Signed endpoint conversion bounds the signed view of every represented word. *)
  Theorem interval_signed_sound w a z lo hi :
    interval_pgamma w a z -> interval_signed w a = Some (lo, hi) ->
    lo <= signed w z <= hi.
  Proof.
    intros Ha Hsigned. unfold interval_signed in Hsigned.
    destruct (interval_finite_helper a) as [[l h]|] eqn:Hfinite; [|discriminate].
    pose proof (interval_finite_sound w a l h z Ha Hfinite) as Hbounds.
    rewrite signed_value, (wrap_id w z (proj1 Ha)).
    destruct (Z.ltb h (half w)) eqn:Hlow.
    - apply Z.ltb_lt in Hlow. inversion Hsigned; subst lo hi.
      assert (Htest : Z.ltb z (half w) = true) by (apply Z.ltb_lt; lia).
      now rewrite Htest.
    - destruct (Z.leb (half w) l) eqn:Hhigh; [|discriminate].
      apply Z.leb_le in Hhigh. inversion Hsigned; subst lo hi.
      assert (Htest : Z.ltb z (half w) = false) by (apply Z.ltb_ge; lia).
      rewrite Htest. lia.
  Qed.

  (** Sign extension contains the modular signed view at every result width. *)
  Theorem interval_sext_sound rw w a x :
    interval_pgamma w a x ->
    interval_pgamma rw (interval_sext rw w a) (wrap rw (signed w x)).
  Proof.
    intro Ha. unfold interval_sext.
    destruct (interval_signed w a) as [[lo hi]|] eqn:Hsigned;
      [|apply interval_top_sound, wrap_is_word].
    pose proof (interval_signed_sound w a x lo hi Ha Hsigned) as Hbounds.
    destruct (Z.ltb hi 0).
    - rewrite <- (wrap_add_modulus rw (signed w x) 1).
      replace (signed w x + 1 * modulus rw) with (modulus rw + signed w x) by ring.
      apply interval_checked_wrap_sound. lia.
    - destruct (Z.leb 0 lo); [|apply interval_top_sound, wrap_is_word].
      apply interval_checked_wrap_sound. exact Hbounds.
  Qed.

  (** Signed comparisons contain every Boolean result of represented operands. *)
  Theorem interval_signed_compare_sound w a b x y rw strict :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma rw (interval_signed_compare w strict a b)
      (if (if strict then Z.ltb (signed w x) (signed w y)
           else Z.leb (signed w x) (signed w y)) then 1 else 0).
  Proof.
    intros Ha Hb. unfold interval_signed_compare.
    destruct (interval_signed w a) as [[la ha]|] eqn:Hfa;
      destruct (interval_signed w b) as [[lb hb]|] eqn:Hfb;
      try (destruct strict; apply interval_truth_sound; discriminate).
    pose proof (interval_signed_sound w a x la ha Ha Hfa) as Hax.
    pose proof (interval_signed_sound w b y lb hb Hb Hfb) as Hby.
    destruct strict.
    - destruct (Z.ltb ha lb) eqn:Htrue.
      + apply Z.ltb_lt in Htrue. apply interval_truth_sound; [|discriminate].
        intros _. apply Z.ltb_lt. lia.
      + destruct (Z.leb hb la) eqn:Hfalse.
        * apply Z.leb_le in Hfalse. apply interval_truth_sound; [discriminate|].
          intros _. apply Z.ltb_ge. lia.
        * apply interval_truth_sound; discriminate.
    - destruct (Z.leb ha lb) eqn:Htrue.
      + apply Z.leb_le in Htrue. apply interval_truth_sound; [|discriminate].
        intros _. apply Z.leb_le. lia.
      + destruct (Z.ltb hb la) eqn:Hfalse.
        * apply Z.ltb_lt in Hfalse. apply interval_truth_sound; [discriminate|].
          intros _. apply Z.leb_gt. lia.
        * apply interval_truth_sound; discriminate.
  Qed.

  Local Lemma interval_same_sign_order w x y :
    is_word w x -> is_word w y -> msb w x = msb w y ->
    (signed w x < signed w y <-> x < y) /\
    (signed w x <= signed w y <-> x <= y).
  Proof.
    intros Hx Hy Hsame. rewrite !msb_half, (wrap_id w x Hx), (wrap_id w y Hy) in Hsame.
    rewrite !signed_value, (wrap_id w x Hx), (wrap_id w y Hy).
    destruct (Z.ltb x (half w)), (Z.ltb y (half w)); cbn in *; try discriminate; lia.
  Qed.

  (** Common-sign refinement retains every pair satisfying the signed Boolean result. *)
  Theorem interval_assume_signed_sound w (strict result : bool) a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    (if strict then Z.ltb (signed w x) (signed w y)
     else Z.leb (signed w x) (signed w y)) = result ->
    interval_pgamma w (fst (interval_assume_signed w strict result a b)) x /\
    interval_pgamma w (snd (interval_assume_signed w strict result a b)) y.
  Proof.
    intros Ha Hb Hcmp. unfold interval_assume_signed.
    destruct (interval_sign w a) as [sa|] eqn:Hsa;
      destruct (interval_sign w b) as [sb|] eqn:Hsb; try (split; assumption).
    destruct (Bool.eqb sa sb) eqn:Hsame; [|split; assumption].
    pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
    pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
    assert (Hbits : msb w x = msb w y) by
      (rewrite Hx, Hy; destruct sa, sb; cbn in Hsame; congruence).
    pose proof (interval_same_sign_order w x y (proj1 Ha) (proj1 Hb) Hbits)
      as [Hlt Hle]. destruct strict, result; cbn in Hcmp.
    - apply Z.ltb_lt in Hcmp. apply Hlt in Hcmp. now apply interval_assume_ult_sound.
    - apply Z.ltb_ge in Hcmp. assert (Horder : y <= x) by lia.
      destruct (interval_assume_ule_sound w w b a y x Hb Ha Horder); split; assumption.
    - apply Z.leb_le in Hcmp. apply Hle in Hcmp. now apply interval_assume_ule_sound.
    - apply Z.leb_gt in Hcmp. assert (Horder : y < x) by lia.
      destruct (interval_assume_ult_sound w w b a y x Hb Ha Horder); split; assumption.
  Qed.

  (** Signed division contains the sign-adjusted quotient, including the zero-divisor branches. *)
  Theorem interval_sdiv_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_sdiv w a b) (wsdiv w x y).
  Proof.
    intros Ha Hb. unfold interval_sdiv.
    destruct (interval_sign w a) as [sa|] eqn:Hsa;
      destruct (interval_sign w b) as [sb|] eqn:Hsb;
      try (apply interval_top_sound, wsdiv_is_word).
    pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
    pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
    rewrite wsdiv_value, Hx, Hy.
    destruct sa, sb; cbn [xorb]; repeat rewrite wneg_value;
      try (apply interval_neg_sound; apply interval_udiv_sound;
        try apply interval_neg_sound; assumption);
      apply interval_udiv_sound; try apply interval_neg_sound; assumption.
  Qed.

  (** Signed remainder contains the unsigned magnitude remainder adjusted to the dividend sign. *)
  Theorem interval_srem_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_srem w a b) (wsrem w x y).
  Proof.
    intros Ha Hb. unfold interval_srem.
    destruct (interval_sign w a) as [sa|] eqn:Hsa;
      destruct (interval_sign w b) as [sb|] eqn:Hsb;
      try (apply interval_top_sound, wsrem_is_word).
    pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
    pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
    rewrite wsrem_value, Hx, Hy.
    destruct sa, sb; cbn [xorb]; repeat rewrite wneg_value;
      try (apply interval_neg_sound; apply interval_urem_sound;
        try apply interval_neg_sound; assumption);
      apply interval_urem_sound; try apply interval_neg_sound; assumption.
  Qed.

  Local Lemma interval_mod_choice_sound w u candidate r z :
    interval_pgamma w u r -> interval_pgamma w candidate z ->
    interval_pgamma w (interval_mod_choice u candidate) (if Z.eqb r 0 then r else z).
  Proof.
    intros Hu Hz. unfold interval_mod_choice.
    assert (Hjoin : interval_pgamma w
      (interval_join (I (Fin 0) (Fin 0)) candidate) (if Z.eqb r 0 then r else z)).
    { apply interval_join_sound.
      destruct (Z.eqb r 0) eqn:Hzeroeq; [left|now right].
      apply Z.eqb_eq in Hzeroeq. subst r.
      split; [apply zero_is_word|]. cbn. split; reflexivity. }
    destruct (interval_finite_helper u) as [[lo hi]|] eqn:Hfinite; [|exact Hjoin].
    pose proof (interval_finite_sound w u lo hi r Hu Hfinite) as Hbounds.
    destruct (Z.ltb 0 lo) eqn:Hpositive.
    - apply Z.ltb_lt in Hpositive.
      assert (Hnonzero : Z.eqb r 0 = false) by (apply Z.eqb_neq; lia).
      now rewrite Hnonzero.
    - destruct (Z.eqb hi 0) eqn:Hzero; [|exact Hjoin].
      apply Z.eqb_eq in Hzero. assert (r = 0) by (pose proof (proj1 (proj1 Hu)); lia).
      subst r. cbn. split; [apply zero_is_word|]. cbn. split; reflexivity.
  Qed.

  (** Signed modulus retains the magnitude remainder and its divisor-sign adjustment. *)
  Theorem interval_smod_base_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_smod_base w a b) (wsmod w x y).
  Proof.
    intros Ha Hb. unfold interval_smod_base.
    destruct (interval_sign w a) as [sa|] eqn:Hsa;
      destruct (interval_sign w b) as [sb|] eqn:Hsb;
      try (apply interval_top_sound, wsmod_is_word).
    pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
    pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
    rewrite wsmod_value, Hx, Hy.
    destruct sa, sb; cbn [xorb];
      rewrite ?(wrap_id w x (proj1 Ha)), ?(wrap_id w y (proj1 Hb));
      repeat rewrite wadd_value; repeat rewrite wneg_value.
    - apply interval_mod_choice_sound.
      + apply interval_urem_sound; apply interval_neg_sound; assumption.
      + apply interval_neg_sound. apply interval_urem_sound; apply interval_neg_sound; assumption.
    - apply interval_mod_choice_sound.
      + apply interval_urem_sound; [apply interval_neg_sound|]; assumption.
      + apply interval_add_modular_sound; [apply interval_neg_sound; apply interval_urem_sound;
          [apply interval_neg_sound|]|]; assumption.
    - apply interval_mod_choice_sound.
      + apply interval_urem_sound; [|apply interval_neg_sound]; assumption.
      + apply interval_add_modular_sound; [apply interval_urem_sound; [|apply interval_neg_sound]|];
          assumption.
    - apply interval_mod_choice_sound; apply interval_urem_sound; assumption.
  Qed.

  (** A positive divisor additionally bounds signed modulus between zero and its upper endpoint. *)
  Theorem interval_smod_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_smod w a b) (wsmod w x y).
  Proof.
    intros Ha Hb. unfold interval_smod.
    destruct (interval_sign w b) as [sign|] eqn:Hsign;
      [destruct sign|]; try now apply interval_smod_base_sound.
    destruct (interval_finite_helper b) as [[lo hi]|] eqn:Hfinite;
      [|now apply interval_smod_base_sound].
    destruct (Z.ltb 0 lo) eqn:Hpositive; [|now apply interval_smod_base_sound].
    apply Z.ltb_lt in Hpositive.
    pose proof (interval_finite_sound w b lo hi y Hb Hfinite) as Hy.
    pose proof (interval_sign_sound w b y false Hb Hsign) as Hmsb.
    assert (Hsignedy : signed w y = y).
    { rewrite (signed_nonnegative w y Hmsb). apply wrap_id. exact (proj1 Hb). }
    pose proof (proj1 (wsmod_sign w x y) ltac:(rewrite Hsignedy; lia)) as Hmod.
    assert (Hword : is_word w (wsmod w x y)) by apply wsmod_is_word.
    assert (Hsigned : signed w (wsmod w x y) = wsmod w x y).
    { rewrite signed_value, (wrap_id w _ Hword).
      destruct (Z.ltb (wsmod w x y) (half w)) eqn:Hhalf; [reflexivity|].
      rewrite signed_value, (wrap_id w _ Hword), Hhalf in Hmod.
      destruct Hword. lia. }
    apply interval_meet_sound; [now apply interval_smod_base_sound|].
    split; [exact Hword|]. cbn.
    rewrite Hsignedy, Hsigned in Hmod. split; apply Z.leb_le; lia.
  Qed.

  Local Lemma interval_div_complement x d :
    0 <= x -> 0 < d -> (-1 - x) / d = -1 - x / d.
  Proof.
    intros Hx Hd. apply Z.diveq. right. left.
    pose proof (Z.div_mod x d ltac:(lia)) as Hdivision.
    pose proof (Z.mod_pos_bound x d Hd) as Hremainder. nia.
  Qed.

  Local Lemma interval_ashr_negative w x y :
    is_word w x -> is_word w y -> msb w x = true ->
    washr w x y = wnot w (wlshr w (wnot w x) y).
  Proof.
    intros Hx Hy Hnegative.
    rewrite (interval_complement_word w (wlshr w (wnot w x) y)
      (wlshr_is_word w (wnot w x) y)).
    rewrite (interval_complement_word w x Hx), washr_value, wlshr_value.
    rewrite (wrap_id w y Hy).
    rewrite (wrap_id w (modulus w - 1 - x)) by
      (pose proof (modulus_pos w); destruct Hx; split; lia).
    destruct (Z.leb (Zpos w) y) eqn:Hlarge.
    - rewrite Hnegative. lia.
    - rewrite msb_half, (wrap_id w x Hx) in Hnegative.
      apply Bool.negb_true_iff in Hnegative. apply Z.ltb_ge in Hnegative.
      rewrite signed_value, (wrap_id w x Hx).
      assert (Hhalf : Z.ltb x (half w) = false) by (apply Z.ltb_ge; exact Hnegative).
      rewrite Hhalf. set (d := 2 ^ y).
      assert (Hd : 0 < d) by (unfold d; apply Z.pow_pos_nonneg; destruct Hy; lia).
      assert (Ht : 0 <= modulus w - 1 - x) by (destruct Hx; lia).
      replace (x - modulus w) with (-1 - (modulus w - 1 - x)) by ring.
      rewrite interval_div_complement by assumption.
      pose proof (Z.div_pos (modulus w - 1 - x) d Ht Hd) as Hqlo.
      pose proof (Z.div_le_upper_bound (modulus w - 1 - x) d (modulus w - 1)
        ltac:(lia) ltac:(pose proof (modulus_pos w); pose proof (proj1 Hx); nia)) as Hqhi.
      assert (Hout : is_word w (modulus w - 1 - (modulus w - 1 - x) / d))
        by (split; pose proof (modulus_pos w); lia).
      rewrite <- (wrap_add_modulus w (-1 - (modulus w - 1 - x) / d) 1).
      replace (-1 - (modulus w - 1 - x) / d + 1 * modulus w) with
        (modulus w - 1 - (modulus w - 1 - x) / d) by ring.
      now rewrite (wrap_id w _ Hout).
  Qed.

  Local Lemma interval_ashr_nonnegative w x y :
    is_word w x -> is_word w y -> msb w x = false -> washr w x y = wlshr w x y.
  Proof.
    intros Hx Hy Hsign. rewrite washr_value, wlshr_value.
    rewrite (wrap_id w x Hx), (wrap_id w y Hy).
    destruct (Z.leb (Zpos w) y) eqn:Hlarge; [now rewrite Hsign|].
    rewrite (signed_nonnegative w x Hsign), (wrap_id w x Hx). apply wrap_id.
    pose proof (wlshr_is_word w x y) as Hresult.
    rewrite wlshr_value, (wrap_id w x Hx), (wrap_id w y Hy), Hlarge in Hresult.
    exact Hresult.
  Qed.

  Local Lemma interval_ashr_small_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_ashr_small w a b) (washr w x y).
  Proof.
    intros Ha Hb. unfold interval_ashr_small.
    destruct (interval_sign w a) as [sign|] eqn:Hsign;
      [|apply interval_top_sound, washr_is_word].
    pose proof (interval_sign_sound w a x sign Ha Hsign) as Hmsb.
    destruct sign.
    - rewrite (interval_ashr_negative w x y (proj1 Ha) (proj1 Hb) Hmsb).
      apply interval_not_sound. apply interval_lshr_sound; [apply interval_not_sound|]; assumption.
    - rewrite (interval_ashr_nonnegative w x y (proj1 Ha) (proj1 Hb) Hmsb).
      now apply interval_lshr_sound.
  Qed.

  (** Arithmetic right shift also includes sign saturation when shift amounts reach the width. *)
  Theorem interval_ashr_sound w a b x y :
    interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (interval_ashr w a b) (washr w x y).
  Proof.
    intros Ha Hb. unfold interval_ashr.
    destruct (interval_sign w a) as [sign|] eqn:Hsign;
      [|now apply interval_ashr_small_sound].
    destruct (interval_finite_helper b) as [[lo hi]|] eqn:Hfinite;
      [|now apply interval_ashr_small_sound].
    pose proof (interval_finite_sound w b lo hi y Hb Hfinite) as Hbounds.
    pose proof (interval_sign_sound w a x sign Ha Hsign) as Hmsb.
    destruct (Z.ltb hi (Zpos w)) eqn:Hhi; [now apply interval_ashr_small_sound|].
    assert (Hsaturated : Zpos w <= y ->
      interval_pgamma w (I (Fin (if sign then modulus w - 1 else 0))
        (Fin (if sign then modulus w - 1 else 0))) (washr w x y)).
    { intro Hlarge. rewrite washr_value, (wrap_id w y (proj1 Hb)).
      rewrite (proj2 (Z.leb_le _ _) Hlarge), Hmsb. destruct sign.
      - split; [apply ones_is_word|]. cbn. split; apply Z.leb_refl.
      - split; [apply zero_is_word|]. cbn. split; reflexivity. }
    destruct (Z.leb (Zpos w) lo) eqn:Hlo.
    - apply Hsaturated. apply Z.leb_le in Hlo. lia.
    - apply interval_join_sound. destruct (Z.leb (Zpos w) y) eqn:Hy.
      + right. apply Hsaturated. now apply Z.leb_le.
      + left. apply interval_ashr_small_sound; [exact Ha|].
        split; [exact (proj1 Hb)|].
        change (Z.leb lo y = true /\ Z.leb y (Zpos w - 1) = true).
        apply Z.leb_gt in Hy. split; apply Z.leb_le; lia.
  Qed.
End IntervalOpsSound.

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
