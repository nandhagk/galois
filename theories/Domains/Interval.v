(** * Interval lattice operations

    Intervals use integer bounds and threshold widening.
    For example, meeting disjoint finite intervals returns bottom.
    Builds on: IntervalSig and ThresholdsSig. *)

From Stdlib Require Import ZArith Bool List Lia.
From Argent Require Import Time Std BigO.
From Galois.Domains Require Import ValueSig IntervalSig ThresholdsSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Nat.
  TimeFun Nat.max.
End Nat.

Module IntervalBaseCode (T : THRESHOLDS_OPS) <: INTERVAL_SCALAR_OPS T.
  Include INTERVAL_SCALAR_SPEC T.
End IntervalBaseCode.

Module IntervalBaseT (T : THRESHOLDS_T) <: INTERVAL_SCALAR_T T.
  Include IntervalBaseCode T.

  TimeFun bound_leb.
  TimeFun bound_min.
  TimeFun bound_max.
  TimeFun widen_lower.
  TimeFun widen_upper.
  TimeFun narrow_bound.
  TimeFun interval_leb.
  TimeFun interval_join.
  TimeFun interval_widen.
  TimeFun interval_narrow.
  TimeFun bounds_nonempty.
  TimeFun interval_meet.
  TimeFun interval_finite.
  TimeFun interval_singleton.
  TimeFun interval_is_bot.
  TimeFun interval_stable_widen.

  Definition c_scalar : N := 1%N. (* STUB *)

  (** Scalar inclusion charges the raw endpoint bits. *)
  Lemma T_interval_leb_le : forall a b,
    (T_interval_leb a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Scalar join charges the raw endpoint bits. *)
  Lemma T_interval_join_le : forall a b,
    (T_interval_join a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Scalar meet charges the raw endpoint bits. *)
  Lemma T_interval_meet_le : forall a b,
    (T_interval_meet a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Scalar narrowing reads the endpoint constructors. *)
  Lemma T_interval_narrow_le : forall a b, (T_interval_narrow a b <= c_scalar)%N.
  Proof. Admitted. (* STUB *)
  (** Scalar bottom recognition reads the interval constructor. *)
  Lemma T_interval_is_bot_le : forall a, (T_interval_is_bot a <= c_scalar)%N.
  Proof. Admitted. (* STUB *)
  (** Scalar point recognition compares both finite endpoints. *)
  Lemma T_interval_singleton_le : forall a,
    (T_interval_singleton a <= c_scalar * N.of_nat (interval_bits a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Scalar widening pays for inclusion and the threshold search paths. *)
  Lemma T_interval_stable_widen_le : forall ts a b,
    (T_interval_stable_widen ts a b <= c_scalar * N.of_nat
      (interval_bits a + interval_bits b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widening selects endpoints from its operands, thresholds and infinities. *)
  Lemma interval_stable_widen_bits : forall ts a b,
    (interval_bits (interval_stable_widen ts a b) <=
      interval_bits a + interval_bits b + T.tree_bits ts)%nat.
  Proof. Admitted. (* STUB *)
End IntervalBaseT.

Module IntervalCode (L : Z_LANGUAGE_OPS) (T : THRESHOLDS_OPS) <: INTERVAL_OPS L T.
  Include IntervalBaseCode T.
  Definition t := itv.
  Definition wparam := ttree.
  Definition bot := IBot.
  Definition top := I NegInf PosInf.
  Definition leb := interval_leb.
  Definition is_bot := interval_is_bot.
  Definition join := interval_join.
  Definition meet := interval_meet.
  Definition widen := interval_stable_widen.
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
  Definition code_bnd_bits b := match b with Fin z => Z.size_nat z | _ => 0%nat end.
  Definition code_itv_bits a :=
    match a with IBot => 0%nat | I lo hi => Nat.max (code_bnd_bits lo) (code_bnd_bits hi) end.
  Definition shl a b :=
    let k := Z.of_nat (code_itv_bits a + code_itv_bits b + 1) in
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I (Fin la) ha, I (Fin lb) hb =>
      if (Z.leb 0 la && Z.leb 0 lb)%bool then
        match ha, hb with
        | Fin ha, Fin hb =>
          if andb (Z.leb lb k) (Z.leb hb k) then
            I (Fin (Z.shiftl la lb)) (Fin (Z.shiftl ha hb))
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

Local Close Scope Z_scope.

Module Interval (L : Z_LANGUAGE) (T : THRESHOLDS) <: INTERVAL L T.
  Include IntervalCode L T.
  Include INTERVAL_SPEC L T.
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

  Definition wrank := interval_wrank.
  Definition gamma := in_itv.

  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intros [|l h]; cbn; [reflexivity|].
    now rewrite !bound_leb_refl.
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [|la ha] [|lb hb] [|lc hc]; cbn; try discriminate; try reflexivity.
    intros Hab Hbc. apply andb_true_iff in Hab as [Hlb Hhb].
    apply andb_true_iff in Hbc as [Hlc Hhc]. apply andb_true_iff. split;
      eapply bound_leb_trans; eassumption.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros [|l h]; reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_l|apply bound_max_upper_l].
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_r|apply bound_max_upper_r].
  Qed.

  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted.

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn; try reflexivity.
    destruct (bounds_nonempty (bound_max la lb) (bound_min ha hb)); cbn; [|reflexivity].
    apply andb_true_iff. split; [apply bound_max_upper_l|apply bound_min_lower_l].
  Qed.
  (** Meet is below its right operand. *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* CONVERT: interval_laws: The variable widen_lower_old was not found in the current environment. *)
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* CONVERT: interval_laws: The variable widen_lower_next was not found in the current *)
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hba. split.
    - revert a b Hba. intros [|la ha] [|lb hb]; cbn; try discriminate; try reflexivity;
      try (intros _; now rewrite !bound_leb_refl).
    intros Hle. apply andb_true_iff in Hle as [Hl Hh]. apply andb_true_iff. split.
    + unfold narrow_bound. destruct la; try assumption; apply bound_leb_refl.
    + unfold narrow_bound. destruct ha; try assumption; apply bound_leb_refl.
    - revert a b Hba. intros [|la ha] [|lb hb]; cbn; try discriminate; try reflexivity;
      try (intros _; now rewrite !bound_leb_refl).
    intros Hle. apply andb_true_iff in Hle as [Hl Hh]. apply andb_true_iff. split.
    + unfold narrow_bound. destruct la; try assumption; apply bound_leb_refl.
    + unfold narrow_bound. destruct ha; try assumption; apply bound_leb_refl.
  Qed.

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof. Admitted. (* CONVERT: interval_gamma_laws: Unable to unify "bound_leb ?a ?c = true" with *)
  (** Bottom describes no concrete value. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof.
    intros c H. exact H.
  Qed.
  (** Top describes every concrete value. *)
  Lemma gamma_top : forall c, gamma top c.
  Proof. Admitted.
  (** Meet retains values described by both operands. *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof. Admitted. (* CONVERT: interval_meet_sound: Not an inductive product. *)
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    intros [|lo hi] z Hempty Hgamma; try discriminate. exact Hgamma.
  Qed.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof. Admitted.
  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted. (* CONVERT: interval_forward_sound: The variable pforward_sound was not found in the current environment. *)
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted. (* CONVERT: interval_assume_sound: The variable passume_sound was not found in the current environment. *)
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof. Admitted.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted.
End Interval.

Module IntervalTimingHelpers (L : Z_LANGUAGE_T) (T : THRESHOLDS_T).
  Include Interval L T.
  TimeFun bound_leb.
  TimeFun bound_min.
  TimeFun bound_max.
  TimeFun widen_lower.
  TimeFun widen_upper.
  TimeFun narrow_bound.
  TimeFun interval_leb.
  TimeFun interval_join.
  TimeFun interval_widen.
  TimeFun interval_narrow.
  TimeFun bounds_nonempty.
  TimeFun interval_meet.
  TimeFun interval_finite.
  TimeFun interval_singleton.
  TimeFun interval_is_bot.
  TimeFun interval_stable_widen.
  TimeFun leb.
  TimeFun bot.
  TimeFun top.
  TimeFun is_bot.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun point.
  TimeFun abst.
  TimeFun add.
  TimeFun sub.
  TimeFun mul.
  TimeFun udiv.
  TimeFun urem.
  TimeFun bitand.
  TimeFun bitor.
  TimeFun code_bnd_bits.
  TimeFun code_itv_bits.
  TimeFun shl.
  TimeFun truth.
  TimeFun cmp.
  TimeFun add_back.
  TimeFun sub_back.
  TimeFun mul_preimage.
  TimeFun mul_back.
  TimeFun unsigned_back.
  TimeFun udiv_back.
  TimeFun urem_back.
  TimeFun ult_back.
  TimeFun signed_split.
  TimeFun strict_back.
  TimeFun forward.
  TimeFun backward.
  TimeFun guard.
End IntervalTimingHelpers.

Module IntervalT (L : Z_LANGUAGE_T) (T : THRESHOLDS_T) <: INTERVAL_ALL L T.
  Include IntervalTimingHelpers L T.

  Definition size := itv_bits.
  Definition wsize (ts : ttree) := (T.depth ts + 1) * (T.tree_bits ts + 1).
  Definition wunits (_ : t) : nat := 0.
  Definition operand_bits (xs : list t) := fold_right Nat.add 0 (map size xs).
  Definition work (o : L.op) (xs : list t) :=
    operand_bits xs + length xs + (operand_bits xs + 1) ^ 2 +
    match L.view o with ZConst z => Z.size_nat z | _ => 0 end.
  Definition gwork (_ : L.guard) (xs : list t) :=
    operand_bits xs + length xs + (operand_bits xs + 1) ^ 2.
  Definition c_val : N := 1%N. (* STUB *)
  Definition c_lat : N := c_val.
  Definition c_interval : N := 1%N. (* STUB *)
  Definition k_interval_arith : N := 1%N. (* STUB *)
  Definition k_interval_back : N := 1%N. (* STUB *)
  Definition k_interval_widen : N := 1%N. (* STUB *)
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  (** Inclusion testing costs at most the combined abstract sizes. *)
  Lemma T_leb_le : forall a b, (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Join costs at most the combined abstract sizes. *)
  Lemma T_join_le : forall a b, (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Meet costs at most the combined abstract sizes. *)
  Lemma T_meet_le : forall a b, (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Bottom testing costs at most the abstract size. *)
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widening charges both values and the widening parameters. *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Narrowing charges both abstract values. *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Forward transfer is bounded by operator work. *)
  Lemma T_forward_le : forall o xs, (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Backward transfer additionally charges the requested result. *)
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Guard transfer is bounded by guard work. *)
  Lemma T_guard_le : forall g xs, (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Forward results fit within the charged operator work. *)
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Meet results fit within the combined operand sizes. *)
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Join results fit within the combined operand sizes. *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widening results fit within the operand and parameter sizes. *)
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Backward results fit within the charged work and request size. *)
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Guard results fit within the charged guard work. *)
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Operator work accounts for every operand size. *)
  Lemma work_sizes : forall o xs, fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof. Admitted. (* STUB *)
  (** Guard work accounts for every operand size. *)
  Lemma gwork_sizes : forall g xs, fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof. Admitted. (* STUB *)
  (** Interval size records the largest endpoint bit size. *)
  Lemma size_bits : forall a, size a = itv_bits a.
  Proof. Admitted. (* STUB *)
  (** Point recognition charges both endpoint comparisons. *)
  Lemma T_point_le : forall a, (T_point a <= c_interval * N.of_nat ((size a + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** A singleton interval shares its integer argument. *)
  Lemma T_abst_le : forall z, (T_abst z <= c_interval)%N.
  Proof. Admitted. (* STUB *)
  (** Addition charges linear endpoint arithmetic. *)
  Lemma T_add_le : forall a b, (T_add a b <= c_interval * N.of_nat ((size a + size b +
    1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Subtraction charges linear endpoint arithmetic. *)
  Lemma T_sub_le : forall a b, (T_sub a b <= c_interval * N.of_nat ((size a + size b +
    1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Multiplication has the published quadratic endpoint bound. *)
  Lemma T_mul_le : forall a b, (T_mul a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Unsigned division has the published quadratic endpoint bound. *)
  Lemma T_udiv_le : forall a b, (T_udiv a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Unsigned remainder has the published quadratic endpoint bound. *)
  Lemma T_urem_le : forall a b, (T_urem a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Bitwise conjunction has the published quadratic endpoint bound. *)
  Lemma T_bitand_le : forall a b, (T_bitand a b <= c_interval * N.of_nat ((binary_work a
    b)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Bitwise disjunction has the published quadratic endpoint bound. *)
  Lemma T_bitor_le : forall a b, (T_bitor a b <= c_interval * N.of_nat ((binary_work a
    b)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Shift transfer has the published quadratic endpoint bound. *)
  Lemma T_shl_le : forall a b, (T_shl a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Comparison charges linear endpoint comparisons. *)
  Lemma T_cmp_le : forall c a b, (T_cmp c a b <= c_interval * N.of_nat ((size a + size b +
    1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward addition charges the result and both operands. *)
  Lemma T_add_back_le : forall r a b, (T_add_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward subtraction charges the result and both operands. *)
  Lemma T_sub_back_le : forall r a b, (T_sub_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward multiplication charges the result and both operands. *)
  Lemma T_mul_back_le : forall r a b, (T_mul_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward unsigned division charges the result and both operands. *)
  Lemma T_udiv_back_le : forall r a b, (T_udiv_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward unsigned remainder charges the result and both operands. *)
  Lemma T_urem_back_le : forall r a b, (T_urem_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward comparison charges the result and both operands. *)
  Lemma T_ult_back_le : forall r a b, (T_ult_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Signed splitting charges the width and endpoints. *)
  Lemma T_signed_split_le : forall w a, (T_signed_split w a <=
    c_interval * N.of_nat (((Pos.to_nat w + size a + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Threshold widening charges a search path and endpoint bit sizes. *)
  Lemma T_widen_thresholds_le : forall ts a b, (T_widen ts a b <=
    c_interval * N.of_nat
      ((size a + size b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Interval concretization is inclusive endpoint membership. *)
  Lemma F1_gamma : forall a z, gamma a z <-> in_itv a z.
  Proof. Admitted. (* STUB *)
  (** Widening uses the count of thresholds beyond each finite endpoint. *)
  Lemma F2_wrank : forall ts a, wrank ts a = interval_wrank ts a.
  Proof. Admitted. (* STUB *)
  (** Each endpoint contributes at most one plus the threshold count. *)
  Lemma F3_wrank_le : forall ts a, wrank ts a <= 2 * (length (T.vals ts) + 1).
  Proof. Admitted. (* STUB *)
  (** Raising a finite upper endpoint to its next threshold removes one rank unit. *)
  Lemma F4_count_gt : forall ts z u, In u (T.vals ts) ->
    (z < u)%Z -> count_gt ts u < count_gt ts z.
  Proof. Admitted. (* STUB *)
  (** Lowering a finite lower endpoint to its previous threshold removes one rank unit. *)
  Lemma F5_count_lt : forall ts z u, In u (T.vals ts) ->
    (u < z)%Z -> count_lt ts u < count_lt ts z.
  Proof. Admitted. (* STUB *)
  (** Widening parameter size pays for a threshold search path. *)
  Lemma F_wsize : forall ts, wsize ts = (T.depth ts + 1) * (T.tree_bits ts + 1).
  Proof. Admitted. (* STUB *)
  (** Shift transfer computes finite endpoints below the cutoff and a sound infinity above it. *)
  Lemma F_shl_cutoff : forall a b, shl a b = shift_cutoff a b.
  Proof. Admitted. (* STUB *)
  (** Viewed forward transfer dispatches to the proved interval primitives. *)
  Lemma F_forward_view : forall o xs, forward o xs =
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
  Proof. Admitted. (* STUB *)
  (** Viewed strict guards dispatch to unsigned comparison refinement. *)
  Lemma F_guard_lt : forall g a b, L.gview g = ZGuardUlt ->
    guard g (a :: b :: nil) =
      let result := ult_back (I (Fin 1) (Fin 1)) a b in
      fst result :: snd result :: nil.
  Proof. Admitted. (* STUB *)
  (** Cutoff shifting keeps the published quadratic endpoint bound. *)
  Lemma T3_shl : forall a b,
    (T_shl a b <= k_interval_arith * N.of_nat (binary_work a b))%N.
  Proof. Admitted. (* STUB *)
  (** Addition retains every sum of represented operands. *)
  Lemma F6_add_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (add a b) (x + y).
  Proof. Admitted. (* STUB *)
  (** Subtraction retains every difference of represented operands. *)
  Lemma F7_sub_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (sub a b) (x - y).
  Proof. Admitted. (* STUB *)
  (** Multiplication retains every product of represented operands. *)
  Lemma F8_mul_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (mul a b) (x * y).
  Proof. Admitted. (* STUB *)
  (** Unsigned division retains each defined quotient of nonnegative operands. *)
  Lemma F9_udiv_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= x)%Z -> (0 < y)%Z -> in_itv (udiv a b) (Z.div x y).
  Proof. Admitted. (* STUB *)
  (** Unsigned remainder retains each defined remainder of nonnegative operands. *)
  Lemma F10_urem_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= x)%Z -> (0 < y)%Z -> in_itv (urem a b) (Z.modulo x y).
  Proof. Admitted. (* STUB *)
  (** Bitwise conjunction retains every represented pair of operands. *)
  Lemma F11_and_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (bitand a b) (Z.land x y).
  Proof. Admitted. (* STUB *)
  (** Bitwise disjunction retains every represented pair of operands. *)
  Lemma F12_or_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (bitor a b) (Z.lor x y).
  Proof. Admitted. (* STUB *)
  (** Left shifting retains represented operands for every nonnegative shift. *)
  Lemma F13_shl_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= y)%Z -> in_itv (shl a b) (Z.shiftl x y).
  Proof. Admitted. (* STUB *)
  (** Unsigned comparison refinement descends in both operands. *)
  Lemma F22_ult_back_lower : forall r a b,
    leb (fst (ult_back r a b)) a = true /\ leb (snd (ult_back r a b)) b = true.
  Proof. Admitted. (* STUB *)
  (** Comparison contains the Boolean result as zero or one. *)
  Lemma F14_cmp_sound : forall c a b x y, in_itv a x -> in_itv b y ->
    in_itv (cmp c a b) (match Z.compare x y, c with Eq, Eq | Lt, Lt | Gt, Gt => 1 | _, _ => 0 end).
  Proof. Admitted. (* STUB *)
  (** Signed splitting retains the signed view of every normalized word. *)
  Lemma F15_signed_split_sound : forall w a x, in_itv a x ->
    (0 <= x < 2 ^ Zpos w)%Z ->
    exists b, In b (signed_split w a) /\
      in_itv b (if (x <? 2 ^ (Zpos w - 1))%Z then x else x - 2 ^ Zpos w).
  Proof. Admitted. (* STUB *)
  (** Backward addition retains operands consistent with its result. *)
  Lemma F16_add_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x + y) ->
    in_itv (fst (add_back r a b)) x /\ in_itv (snd (add_back r a b)) y.
  Proof. Admitted. (* STUB *)
  (** Backward subtraction retains operands consistent with its result. *)
  Lemma F17_sub_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x - y) ->
    in_itv (fst (sub_back r a b)) x /\ in_itv (snd (sub_back r a b)) y.
  Proof. Admitted. (* STUB *)
  (** Backward multiplication retains operands consistent with its result. *)
  Lemma F18_mul_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x * y) ->
    in_itv (fst (mul_back r a b)) x /\ in_itv (snd (mul_back r a b)) y.
  Proof. Admitted. (* STUB *)
  (** Backward division retains operands consistent with a defined unsigned quotient. *)
  Lemma F19_udiv_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 < y)%Z -> in_itv r (Z.div x y) ->
    in_itv (fst (udiv_back r a b)) x /\ in_itv (snd (udiv_back r a b)) y.
  Proof. Admitted. (* STUB *)
  (** Backward remainder retains operands consistent with a defined unsigned remainder. *)
  Lemma F20_urem_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 < y)%Z -> in_itv r (Z.modulo x y) ->
    in_itv (fst (urem_back r a b)) x /\ in_itv (snd (urem_back r a b)) y.
  Proof. Admitted. (* STUB *)
  (** Backward unsigned comparison retains operands with the specified Boolean result. *)
  Lemma F21_ult_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 <= y)%Z ->
    in_itv r (if (x <? y)%Z then 1 else 0) ->
    in_itv (fst (ult_back r a b)) x /\ in_itv (snd (ult_back r a b)) y.
  Proof. Admitted. (* STUB *)
  (** Endpoint arithmetic bounds multiplication before dispatch overhead. *)
  Lemma T1_mul : forall a b, (T_mul a b <= k_interval_arith * N.of_nat (binary_work a b))%N.
  Proof. Admitted. (* STUB *)
  (** Threshold searches bound widening before dispatch overhead. *)
  Lemma T2_widen : forall ts a b,
    (T_widen ts a b <= k_interval_widen * N.of_nat
      (size a + size b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Multiplication has the published quadratic endpoint bound. *)
  Lemma mul_bigO : (bigO (fun _ => True)
    (fun ab => N.of_nat ((binary_work (fst ab) (snd ab))%nat))
    (fun ab => T_mul (fst ab) (snd ab)))%N.
  Proof. Admitted. (* STUB *)
End IntervalT.
