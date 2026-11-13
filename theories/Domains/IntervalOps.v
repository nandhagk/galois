(** * Word interval operations

    Endpoint arithmetic retains finite ranges when they fit the word width.
    For example, adding [1, 4] to [2, 5] yields [3, 9] at width eight.
    Builds on: Interval and the fixed-width word operations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time Std.
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
    intros Ha Hb. unfold interval_shl.
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
    intros Ha Hb. unfold interval_lshr.
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
