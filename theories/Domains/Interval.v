(** * Interval lattice operations

    Intervals use integer bounds and threshold widening.
    For example, meeting disjoint finite intervals returns bottom.
    Builds on: IntervalSig and ThresholdsSig. *)

From Stdlib Require Import ZArith NArith Bool List Lia.
From Argent Require Import Time Tactics Std BigO.
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

  Local Open Scope nat_scope.

  Definition c_scalar : N := (32 * (T.c_thresholds + 1))%N.

  (** An infinite endpoint stores no integer bits. *)
  Definition scalar_bnd_bits (b : bnd) : nat :=
    match b with Fin z => Z.size_nat z | _ => 0 end.

  (** Each endpoint is bounded by the interval's maximum endpoint size. *)
  Lemma scalar_endpoint_bits : forall lo hi,
    scalar_bnd_bits lo <= interval_bits (I lo hi) /\
    scalar_bnd_bits hi <= interval_bits (I lo hi).
  Proof.
    intros lo hi. unfold interval_bits, scalar_bnd_bits.
    split; [apply Nat.le_max_l | apply Nat.le_max_r].
  Qed.

  (** Endpoint minimum selects one of its arguments. *)
  Lemma bound_min_bits : forall a b,
    scalar_bnd_bits (bound_min a b) <= scalar_bnd_bits a + scalar_bnd_bits b.
  Proof.
    intros a b; unfold bound_min; destruct (bound_leb a b); lia.
  Qed.

  (** Endpoint maximum selects one of its arguments. *)
  Lemma bound_max_bits : forall a b,
    scalar_bnd_bits (bound_max a b) <= scalar_bnd_bits a + scalar_bnd_bits b.
  Proof.
    intros a b; unfold bound_max; destruct (bound_leb a b); lia.
  Qed.

  (** Narrowing selects an old finite endpoint or the next endpoint. *)
  Lemma narrow_bound_bits : forall a b,
    scalar_bnd_bits (narrow_bound a b) <= scalar_bnd_bits a + scalar_bnd_bits b.
  Proof.
    intros [] b; cbn [narrow_bound scalar_bnd_bits]; lia.
  Qed.

  (** Joining selects endpoints already present in its operands. *)
  Lemma interval_join_bits : forall a b,
    interval_bits (interval_join a b) <= interval_bits a + interval_bits b.
  Proof.
    intros [|lo hi] [|lo' hi']; try (cbn [interval_join interval_bits]; lia).
    pose proof (scalar_endpoint_bits lo hi) as [Hlo Hhi].
    pose proof (scalar_endpoint_bits lo' hi') as [Hlo' Hhi'].
    change (Nat.max (scalar_bnd_bits (bound_min lo lo'))
      (scalar_bnd_bits (bound_max hi hi')) <=
      interval_bits (I lo hi) + interval_bits (I lo' hi')).
    pose proof (bound_min_bits lo lo'). pose proof (bound_max_bits hi hi').
    apply Nat.max_lub; lia.
  Qed.

  (** Meeting either returns bottom or selects existing endpoints. *)
  Lemma interval_meet_bits : forall a b,
    interval_bits (interval_meet a b) <= interval_bits a + interval_bits b.
  Proof.
    intros [|lo hi] [|lo' hi']; try (cbn [interval_meet interval_bits]; lia).
    pose proof (scalar_endpoint_bits lo hi) as [Hlo Hhi].
    pose proof (scalar_endpoint_bits lo' hi') as [Hlo' Hhi'].
    unfold interval_meet.
    destruct (bounds_nonempty (bound_max lo lo') (bound_min hi hi')).
    - change (Nat.max (scalar_bnd_bits (bound_max lo lo'))
        (scalar_bnd_bits (bound_min hi hi')) <=
        interval_bits (I lo hi) + interval_bits (I lo' hi')).
      pose proof (bound_max_bits lo lo'). pose proof (bound_min_bits hi hi').
      apply Nat.max_lub; lia.
    - cbn [interval_bits]; lia.
  Qed.

  (** Narrowing also selects endpoints already present in the operands. *)
  Lemma interval_narrow_bits : forall a b,
    interval_bits (interval_narrow a b) <= interval_bits a + interval_bits b.
  Proof.
    intros [|lo hi] [|lo' hi']; try (cbn [interval_narrow interval_bits]; lia).
    pose proof (scalar_endpoint_bits lo hi) as [Hlo Hhi].
    pose proof (scalar_endpoint_bits lo' hi') as [Hlo' Hhi'].
    change (Nat.max (scalar_bnd_bits (narrow_bound lo lo'))
      (scalar_bnd_bits (narrow_bound hi hi')) <=
      interval_bits (I lo hi) + interval_bits (I lo' hi')).
    pose proof (narrow_bound_bits lo lo'). pose proof (narrow_bound_bits hi hi').
    apply Nat.max_lub; lia.
  Qed.

  (** The tree size includes every stored threshold. *)
  Lemma threshold_value_bits : forall ts z,
    In z (T.vals ts) -> Z.size_nat z <= T.tree_bits ts.
  Proof.
    intros ts z. unfold T.tree_bits, T.zb, T.zbits.
    induction (T.vals ts) as [|x xs IH]; cbn; intros Hin; [contradiction |].
    destruct Hin as [<- | Hin]; [apply Nat.le_max_l |].
    eapply Nat.le_trans; [apply IH, Hin | apply Nat.le_max_r].
  Qed.

  (** A widened lower endpoint comes from the operands or the threshold tree. *)
  Lemma widen_lower_bits : forall ts a b,
    scalar_bnd_bits (widen_lower ts a b) <=
    scalar_bnd_bits a + scalar_bnd_bits b + T.tree_bits ts.
  Proof.
    intros ts a b. unfold widen_lower. destruct (bound_leb a b); [lia |].
    destruct b as [|z|]; cbn [scalar_bnd_bits]; try lia.
    destruct (T.below ts z) as [u|] eqn:Hbelow; cbn [scalar_bnd_bits]; try lia.
    apply T.below_sound in Hbelow as [Hin _].
    pose proof (threshold_value_bits ts u Hin); lia.
  Qed.

  (** A widened upper endpoint comes from the operands or the threshold tree. *)
  Lemma widen_upper_bits : forall ts a b,
    scalar_bnd_bits (widen_upper ts a b) <=
    scalar_bnd_bits a + scalar_bnd_bits b + T.tree_bits ts.
  Proof.
    intros ts a b. unfold widen_upper. destruct (bound_leb b a); [lia |].
    destruct b as [|z|]; cbn [scalar_bnd_bits]; try lia.
    destruct (T.above ts z) as [u|] eqn:Habove; cbn [scalar_bnd_bits]; try lia.
    apply T.above_sound in Habove as [Hin _].
    pose proof (threshold_value_bits ts u Hin); lia.
  Qed.

  (** The maximum endpoint size charges the threshold tree only once. *)
  Lemma interval_widen_bits : forall ts a b,
    interval_bits (interval_widen ts a b) <=
    interval_bits a + interval_bits b + T.tree_bits ts.
  Proof.
    intros ts [|lo hi] [|lo' hi']; try (cbn [interval_widen interval_bits]; lia).
    pose proof (scalar_endpoint_bits lo hi) as [Hlo Hhi].
    pose proof (scalar_endpoint_bits lo' hi') as [Hlo' Hhi'].
    change (Nat.max (scalar_bnd_bits (widen_lower ts lo lo'))
      (scalar_bnd_bits (widen_upper ts hi hi')) <=
      interval_bits (I lo hi) + interval_bits (I lo' hi') + T.tree_bits ts).
    pose proof (widen_lower_bits ts lo lo'). pose proof (widen_upper_bits ts hi hi').
    apply Nat.max_lub; lia.
  Qed.

  (** Endpoint comparison inspects at most the first finite endpoint's bits. *)
  Lemma T_bound_leb_bits : forall a b,
    (T_bound_leb a b <= N.of_nat (scalar_bnd_bits a) + 5)%N.
  Proof.
    intros [|x|] [|y|]; unfold T_bound_leb; time_cbn; try lia.
    pose proof (Std.Z.T_leb_le x y). cbn [scalar_bnd_bits]; lia.
  Qed.

  (** Choosing a minimum adds one constructor branch to endpoint comparison. *)
  Lemma T_bound_min_bits : forall a b,
    (T_bound_min a b <= N.of_nat (scalar_bnd_bits a) + 6)%N.
  Proof.
    intros a b; pose proof (T_bound_leb_bits a b); unfold T_bound_min; lia.
  Qed.

  (** Choosing a maximum adds one constructor branch to endpoint comparison. *)
  Lemma T_bound_max_bits : forall a b,
    (T_bound_max a b <= N.of_nat (scalar_bnd_bits a) + 6)%N.
  Proof.
    intros a b; pose proof (T_bound_leb_bits a b); unfold T_bound_max; lia.
  Qed.

  (** Testing nonemptiness performs at most one endpoint comparison. *)
  Lemma T_bounds_nonempty_bits : forall a b,
    (T_bounds_nonempty a b <= N.of_nat (scalar_bnd_bits a) + 6)%N.
  Proof.
    intros a b; pose proof (T_bound_leb_bits a b).
    destruct a, b; unfold T_bounds_nonempty; cbn beta iota zeta; lia.
  Qed.
  (** Inclusion compares two endpoint pairs and combines their answers. *)
  Lemma T_interval_leb_bits : forall a b,
    (T_interval_leb a b <= N.of_nat (interval_bits a + interval_bits b) + 12)%N.
  Proof.
    intros [|lo hi] [|lo' hi']; unfold T_interval_leb; cbn beta iota zeta; try lia.
    pose proof (T_bound_leb_bits lo' lo). pose proof (T_bound_leb_bits hi hi').
    pose proof (Std.Datatypes.T_andb_le (bound_leb lo' lo) (bound_leb hi hi')).
    pose proof (scalar_endpoint_bits lo hi) as [Hlo Hhi].
    pose proof (scalar_endpoint_bits lo' hi') as [Hlo' Hhi'].
    rewrite Nat2N.inj_add. lia.
  Qed.

  (** Scalar inclusion charges the raw endpoint bits. *)
  Lemma T_interval_leb_le : forall a b,
    (T_interval_leb a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  Proof.
    intros a b. pose proof (T_interval_leb_bits a b).
    unfold c_scalar. rewrite Nat2N.inj_add. nia.
  Qed.

  (** Scalar join charges the raw endpoint bits. *)
  Lemma T_interval_join_le : forall a b,
    (T_interval_join a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  Proof.
    intros [|lo hi] [|lo' hi']; unfold T_interval_join; cbn beta iota zeta;
      unfold c_scalar; rewrite !Nat2N.inj_add; try nia.
    pose proof (T_bound_min_bits lo lo'). pose proof (T_bound_max_bits hi hi').
    pose proof (scalar_endpoint_bits lo hi) as [Hlo Hhi].
    nia.
  Qed.

  (** Scalar meet charges the raw endpoint bits. *)
  Lemma T_interval_meet_le : forall a b,
    (T_interval_meet a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  Proof.
    intros [|lo hi] [|lo' hi']; unfold T_interval_meet; cbn beta iota zeta;
      unfold c_scalar; rewrite !Nat2N.inj_add; try nia.
    pose proof (T_bound_max_bits lo lo'). pose proof (T_bound_min_bits hi hi').
    pose proof (T_bounds_nonempty_bits (bound_max lo lo') (bound_min hi hi')).
    pose proof (bound_max_bits lo lo').
    pose proof (scalar_endpoint_bits lo hi) as [Hlo Hhi].
    pose proof (scalar_endpoint_bits lo' hi') as [Hlo' Hhi'].
    nia.
  Qed.

  (** Scalar narrowing reads the endpoint constructors. *)
  Lemma T_interval_narrow_le : forall a b, (T_interval_narrow a b <= c_scalar)%N.
  Proof.
    intros [|lo hi] [|lo' hi']; unfold T_interval_narrow, T_narrow_bound;
      cbn beta iota zeta; unfold c_scalar; nia.
  Qed.

  (** Scalar bottom recognition reads the interval constructor. *)
  Lemma T_interval_is_bot_le : forall a, (T_interval_is_bot a <= c_scalar)%N.
  Proof.
    intros a; unfold T_interval_is_bot, c_scalar; nia.
  Qed.

  (** Scalar point recognition compares both finite endpoints. *)
  Lemma T_interval_singleton_le : forall a,
    (T_interval_singleton a <= c_scalar * N.of_nat (interval_bits a + 1))%N.
  Proof.
    intros [|[|lo|] [|hi|]];
      unfold T_interval_singleton, T_interval_finite, T_interval_finite_helper,
        interval_finite, interval_finite_helper;
      cbn beta iota zeta; unfold c_scalar; rewrite Nat2N.inj_add; try nia.
    pose proof (Std.Z.T_eqb_le lo hi).
    pose proof (scalar_endpoint_bits (Fin lo) (Fin hi)) as [Hlo Hhi].
    cbn [scalar_bnd_bits] in Hlo. nia.
  Qed.

  (** Lower widening charges one comparison and at most one threshold search. *)
  Lemma T_widen_lower_bits : forall ts a b,
    (T_widen_lower ts a b <= N.of_nat (scalar_bnd_bits a) + 6 +
      T.c_thresholds * N.of_nat ((T.depth ts + 1) * (T.tree_bits ts + 1)))%N.
  Proof.
    intros ts a b. pose proof (T_bound_leb_bits a b).
    unfold T_widen_lower. destruct (bound_leb a b); [nia |].
    destruct b as [|z|]; cbn beta iota zeta; try nia.
    pose proof (T.T_below_le ts z). rewrite Nat2N.inj_mul. nia.
  Qed.

  (** Upper widening uses the next endpoint as its comparison's first argument. *)
  Lemma T_widen_upper_bits : forall ts a b,
    (T_widen_upper ts a b <= N.of_nat (scalar_bnd_bits b) + 6 +
      T.c_thresholds * N.of_nat ((T.depth ts + 1) * (T.tree_bits ts + 1)))%N.
  Proof.
    intros ts a b. pose proof (T_bound_leb_bits b a).
    unfold T_widen_upper. destruct (bound_leb b a); [nia |].
    destruct b as [|z|]; cbn beta iota zeta; try nia.
    pose proof (T.T_above_le ts z). rewrite Nat2N.inj_mul. nia.
  Qed.

  (** A scalar widening searches for at most two endpoints. *)
  Lemma T_interval_widen_bits : forall ts a b,
    (T_interval_widen ts a b <= N.of_nat (interval_bits a + interval_bits b) + 13 +
      2 * T.c_thresholds * N.of_nat ((T.depth ts + 1) * (T.tree_bits ts + 1)))%N.
  Proof.
    intros ts [|lo hi] [|lo' hi']; unfold T_interval_widen; cbn beta iota zeta; try nia.
    pose proof (T_widen_lower_bits ts lo lo'). pose proof (T_widen_upper_bits ts hi hi').
    pose proof (scalar_endpoint_bits lo hi) as [Hlo Hhi].
    pose proof (scalar_endpoint_bits lo' hi') as [Hlo' Hhi'].
    rewrite Nat2N.inj_add. nia.
  Qed.

  (** Scalar widening pays for inclusion and the threshold search paths. *)
  Lemma T_interval_stable_widen_le : forall ts a b,
    (T_interval_stable_widen ts a b <= c_scalar * N.of_nat
      (interval_bits a + interval_bits b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1))%N.
  Proof.
    intros ts a b. pose proof (T_interval_leb_bits b a).
    pose proof (T_interval_widen_bits ts a b).
    unfold T_interval_stable_widen, c_scalar.
    rewrite !Nat2N.inj_add in *.
    destruct (interval_leb b a); nia.
  Qed.

  (** Widening selects endpoints from its operands, thresholds and infinities. *)
  Lemma interval_stable_widen_bits : forall ts a b,
    (interval_bits (interval_stable_widen ts a b) <=
      interval_bits a + interval_bits b + T.tree_bits ts)%nat.
  Proof.
    intros ts a b. unfold interval_stable_widen.
    destruct (interval_leb b a); [lia | apply interval_widen_bits].
  Qed.

  Local Close Scope nat_scope.
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
          if andb (Z.leb lb hb) (Z.leb hb k) then
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
  Proof.
    reflexivity.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [|lo hi] b Hbot; [reflexivity|discriminate].
  Qed.
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
  Proof.
    intros [|lo [|hi|]]; reflexivity.
  Qed.

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn; try reflexivity.
    destruct (bounds_nonempty (bound_max la lb) (bound_min ha hb)); cbn; [|reflexivity].
    apply andb_true_iff. split; [apply bound_max_upper_l|apply bound_min_lower_l].
  Qed.
  (** Meet is below its right operand. *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn; try reflexivity.
    destruct (bounds_nonempty (bound_max la lb) (bound_min ha hb)); cbn; [|reflexivity].
    apply andb_true_iff. split; [apply bound_max_upper_r|apply bound_min_lower_r].
  Qed.

  (** The widened lower endpoint covers the candidate endpoint. *)
  Lemma widen_lower_next : forall ts old next,
    bound_leb (widen_lower ts old next) next = true.
  Proof.
    intros ts old next. unfold widen_lower.
    destruct (bound_leb old next) eqn:Hle; [exact Hle|].
    destruct next as [|z|]; cbn; try reflexivity.
    destruct (T.below ts z) as [u|] eqn:Hbelow; cbn; [|reflexivity].
    apply Z.leb_le. exact (proj2 (T.below_sound ts z u Hbelow)).
  Qed.

  (** The widened lower endpoint covers the previous endpoint. *)
  Lemma widen_lower_old : forall ts old next,
    bound_leb (widen_lower ts old next) old = true.
  Proof.
    intros ts old next. destruct (bound_leb old next) eqn:Hle.
    - unfold widen_lower. rewrite Hle. apply bound_leb_refl.
    - eapply bound_leb_trans with (b := next); [apply widen_lower_next|].
      destruct (bound_leb_total old next) as [Horder|Horder]; congruence.
  Qed.

  (** The widened upper endpoint covers the candidate endpoint. *)
  Lemma widen_upper_next : forall ts old next,
    bound_leb next (widen_upper ts old next) = true.
  Proof.
    intros ts old next. unfold widen_upper.
    destruct (bound_leb next old) eqn:Hle; [exact Hle|].
    destruct next as [|z|]; cbn; try reflexivity.
    destruct (T.above ts z) as [u|] eqn:Habove; cbn; [|reflexivity].
    apply Z.leb_le. exact (proj2 (T.above_sound ts z u Habove)).
  Qed.

  (** The widened upper endpoint covers the previous endpoint. *)
  Lemma widen_upper_old : forall ts old next,
    bound_leb old (widen_upper ts old next) = true.
  Proof.
    intros ts old next. destruct (bound_leb next old) eqn:Hle.
    - unfold widen_upper. rewrite Hle. apply bound_leb_refl.
    - eapply bound_leb_trans with (b := next); [|apply widen_upper_next].
      destruct (bound_leb_total old next) as [Horder|Horder]; congruence.
  Qed.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold widen, interval_stable_widen.
    destruct (interval_leb b a); [apply leb_refl|].
    destruct a as [|la ha], b as [|lb hb]; cbn; try reflexivity;
      try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply widen_lower_old|apply widen_upper_old].
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold widen, interval_stable_widen.
    destruct (interval_leb b a) eqn:Hstable; [exact Hstable|].
    destruct a as [|la ha], b as [|lb hb]; cbn; try reflexivity;
      try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply widen_lower_next|apply widen_upper_next].
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p a b Hstable. unfold leb in Hstable.
    unfold widen, interval_stable_widen. now rewrite Hstable.
  Qed.

  Definition lower_count (ts : list Z) (z : Z) : nat :=
    length (filter (fun u => Z.ltb u z) ts).

  Definition upper_count (ts : list Z) (z : Z) : nat :=
    length (filter (fun u => Z.ltb z u) ts).

  Definition lower_rank (ts : list Z) (b : bnd) : nat :=
    match b with
    | NegInf => 0
    | Fin z => S (lower_count ts z)
    | PosInf => S (length ts)
    end.

  Definition upper_rank (ts : list Z) (b : bnd) : nat :=
    match b with
    | NegInf => S (length ts)
    | Fin z => S (upper_count ts z)
    | PosInf => 0
    end.

  (** Counting thresholds below a value never exceeds the list length. *)
  Lemma lower_count_bounded : forall ts z, lower_count ts z <= length ts.
  Proof.
    intros ts z. unfold lower_count. induction ts as [|u us IH]; cbn; [lia|].
    destruct (Z.ltb u z); cbn; lia.
  Qed.

  (** Counting thresholds above a value never exceeds the list length. *)
  Lemma upper_count_bounded : forall ts z, upper_count ts z <= length ts.
  Proof.
    intros ts z. unfold upper_count. induction ts as [|u us IH]; cbn; [lia|].
    destruct (Z.ltb z u); cbn; lia.
  Qed.

  (** Increasing the query can only add thresholds below it. *)
  Lemma lower_count_monotone : forall ts x y, (x <= y)%Z ->
    lower_count ts x <= lower_count ts y.
  Proof.
    intros ts x y Hxy. unfold lower_count.
    induction ts as [|u us IH]; cbn; [lia|].
    destruct (Z.ltb u x) eqn:Hux, (Z.ltb u y) eqn:Huy; cbn; lia.
  Qed.

  (** Increasing the query can only remove thresholds above it. *)
  Lemma upper_count_monotone : forall ts x y, (x <= y)%Z ->
    upper_count ts y <= upper_count ts x.
  Proof.
    intros ts x y Hxy. unfold upper_count.
    induction ts as [|u us IH]; cbn; [lia|].
    destruct (Z.ltb y u) eqn:Hyu, (Z.ltb x u) eqn:Hxu; cbn; lia.
  Qed.

  (** A listed threshold strictly below the old endpoint consumes a rank unit. *)
  Lemma lower_count_strict : forall ts x y, In x ts -> (x < y)%Z ->
    lower_count ts x < lower_count ts y.
  Proof.
    intros ts x y Hin Hxy. unfold lower_count.
    induction ts as [|u us IH]; cbn in *; [contradiction|].
    destruct Hin as [Heq|Hin].
    - subst u. rewrite Z.ltb_irrefl.
      assert (Hlt : Z.ltb x y = true) by (apply Z.ltb_lt; exact Hxy).
      rewrite Hlt. cbn.
      pose proof (lower_count_monotone us x y ltac:(lia)) as Hmono.
      unfold lower_count in Hmono. lia.
    - specialize (IH Hin).
      destruct (Z.ltb u x) eqn:Hux, (Z.ltb u y) eqn:Huy; cbn in *; lia.
  Qed.

  (** A listed threshold strictly above the old endpoint consumes a rank unit. *)
  Lemma upper_count_strict : forall ts x y, In y ts -> (x < y)%Z ->
    upper_count ts y < upper_count ts x.
  Proof.
    intros ts x y Hin Hxy. unfold upper_count.
    induction ts as [|u us IH]; cbn in *; [contradiction|].
    destruct Hin as [Heq|Hin].
    - subst u. rewrite Z.ltb_irrefl.
      assert (Hlt : Z.ltb x y = true) by (apply Z.ltb_lt; exact Hxy).
      rewrite Hlt. cbn.
      pose proof (upper_count_monotone us x y ltac:(lia)) as Hmono.
      unfold upper_count in Hmono. lia.
    - specialize (IH Hin).
      destruct (Z.ltb y u) eqn:Hyu, (Z.ltb x u) eqn:Hxu; cbn in *; lia.
  Qed.

  (** A threshold does not count itself among strictly lower entries. *)
  Lemma lower_count_member_bound : forall ts x, In x ts -> lower_count ts x < length ts.
  Proof.
    intros ts x Hin. induction ts as [|u us IH]; cbn in Hin; [contradiction|].
    unfold lower_count in *. cbn. destruct Hin as [Heq|Hin].
    - subst u. rewrite Z.ltb_irrefl.
      pose proof (lower_count_bounded us x) as Hbound. unfold lower_count in Hbound. lia.
    - specialize (IH Hin). destruct (Z.ltb u x); cbn; lia.
  Qed.

  (** A threshold does not count itself among strictly higher entries. *)
  Lemma upper_count_member_bound : forall ts x, In x ts -> upper_count ts x < length ts.
  Proof.
    intros ts x Hin. induction ts as [|u us IH]; cbn in Hin; [contradiction|].
    unfold upper_count in *. cbn. destruct Hin as [Heq|Hin].
    - subst u. rewrite Z.ltb_irrefl.
      pose proof (upper_count_bounded us x) as Hbound. unfold upper_count in Hbound. lia.
    - specialize (IH Hin). destruct (Z.ltb x u); cbn; lia.
  Qed.

  (** Lower-endpoint rank respects the bound order. *)
  Lemma lower_rank_monotone : forall ts a b, bound_leb a b = true ->
    lower_rank ts a <= lower_rank ts b.
  Proof.
    intros ts [|x|] [|y|] Hle; cbn in *; try discriminate; try lia.
    - apply Z.leb_le in Hle. pose proof (lower_count_monotone ts x y Hle). lia.
    - pose proof (lower_count_bounded ts x). lia.
  Qed.

  (** Upper-endpoint rank reverses the bound order. *)
  Lemma upper_rank_monotone : forall ts a b, bound_leb a b = true ->
    upper_rank ts b <= upper_rank ts a.
  Proof.
    intros ts [|x|] [|y|] Hle; cbn in *; try discriminate; try lia.
    - pose proof (upper_count_bounded ts y). lia.
    - apply Z.leb_le in Hle. pose proof (upper_count_monotone ts x y Hle). lia.
  Qed.

  (** Moving a lower endpoint outward strictly decreases its rank. *)
  Lemma widen_lower_progress : forall ts old next,
    bound_leb old next = false ->
    lower_rank (T.vals ts) (widen_lower ts old next) < lower_rank (T.vals ts) old.
  Proof.
    intros ts [|x|] [|y|] Hmove; cbn in Hmove; try discriminate;
      unfold widen_lower; cbn [bound_leb]; try rewrite Hmove;
      cbn [lower_rank]; try lia.
    - destruct (T.below ts y) as [u|] eqn:Hbelow; cbn [lower_rank]; [|lia].
      destruct (T.below_sound ts y u Hbelow) as [Hin Hu].
      apply Z.leb_gt in Hmove.
      pose proof (lower_count_strict (T.vals ts) u x Hin ltac:(lia)). lia.
    - destruct (T.below ts y) as [u|] eqn:Hbelow; cbn [lower_rank]; [|lia].
      destruct (T.below_sound ts y u Hbelow) as [Hin Hu].
      pose proof (lower_count_member_bound (T.vals ts) u Hin). lia.
  Qed.

  (** Moving an upper endpoint outward strictly decreases its rank. *)
  Lemma widen_upper_progress : forall ts old next,
    bound_leb next old = false ->
    upper_rank (T.vals ts) (widen_upper ts old next) < upper_rank (T.vals ts) old.
  Proof.
    intros ts [|x|] [|y|] Hmove; cbn in Hmove; try discriminate;
      unfold widen_upper; cbn [bound_leb]; try rewrite Hmove;
      cbn [upper_rank]; try lia.
    - destruct (T.above ts y) as [u|] eqn:Habove; cbn [upper_rank]; [|lia].
      destruct (T.above_sound ts y u Habove) as [Hin Hu].
      pose proof (upper_count_member_bound (T.vals ts) u Hin). lia.
    - destruct (T.above ts y) as [u|] eqn:Habove; cbn [upper_rank]; [|lia].
      destruct (T.above_sound ts y u Habove) as [Hin Hu].
      apply Z.leb_gt in Hmove.
      pose proof (upper_count_strict (T.vals ts) x u Hin ltac:(lia)). lia.
  Qed.

  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p [|la ha] [|lb hb] Hbot Hmove; try discriminate.
    unfold leb in Hmove. unfold widen, interval_stable_widen. rewrite Hmove.
    change (upper_rank (T.vals p) (widen_upper p ha hb) +
      lower_rank (T.vals p) (widen_lower p la lb) <
      upper_rank (T.vals p) ha + lower_rank (T.vals p) la).
    cbn [interval_leb] in Hmove. apply andb_false_iff in Hmove as [Hlower|Hupper].
    - pose proof (widen_lower_progress p la lb Hlower) as Hstrict.
      pose proof (upper_rank_monotone (T.vals p) _ _ (widen_upper_old p ha hb)) as Hstable.
      lia.
    - pose proof (lower_rank_monotone (T.vals p) _ _ (widen_lower_old p la lb)) as Hstable.
      pose proof (widen_upper_progress p ha hb Hupper) as Hstrict. lia.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot. destruct (leb b a) eqn:Hstable.
    - rewrite (widen_stable p a b Hstable). lia.
    - pose proof (wrank_widen p a b Hbot Hstable). lia.
  Qed.
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

  (** Endpoint membership agrees with the reflected order on finite bounds. *)
  Lemma in_bnd_order : forall lo hi z,
    in_bnd lo hi z <->
      bound_leb lo (Fin z) = true /\ bound_leb (Fin z) hi = true.
  Proof.
    intros [|lo|] [|hi|] z; unfold in_bnd; cbn [bound_leb]; rewrite ?Z.leb_le;
      intuition congruence.
  Qed.

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof.
    intros [|la ha] [|lb hb] z Hle Ha;
      cbn [leb interval_leb gamma in_itv] in *; try contradiction; try discriminate.
    apply andb_true_iff in Hle as [Hlower Hupper].
    apply in_bnd_order in Ha as [Hlo Hhi]. apply in_bnd_order. split;
      eapply bound_leb_trans; eassumption.
  Qed.
  (** Bottom describes no concrete value. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof.
    intros c H. exact H.
  Qed.
  (** Top describes every concrete value. *)
  Lemma gamma_top : forall c, gamma top c.
  Proof.
    intro c. split; trivial.
  Qed.
  (** Meet retains values described by both operands. *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof.
    intros [|la ha] [|lb hb] z Ha Hb;
      cbn [gamma in_itv] in Ha, Hb; try contradiction.
    apply in_bnd_order in Ha as [Hla Hha].
    apply in_bnd_order in Hb as [Hlb Hhb].
    assert (Hlo : bound_leb (bound_max la lb) (Fin z) = true).
    { apply bound_max_least; assumption. }
    assert (Hhi : bound_leb (Fin z) (bound_min ha hb) = true).
    { apply bound_min_greatest; assumption. }
    assert (Hordered : bound_leb (bound_max la lb) (bound_min ha hb) = true).
    { eapply bound_leb_trans; eassumption. }
    assert (Hnonempty : bounds_nonempty (bound_max la lb) (bound_min ha hb) = true).
    { destruct (bound_max la lb), (bound_min ha hb); cbn in *;
        try discriminate; assumption. }
    unfold meet, interval_meet. rewrite Hnonempty.
    apply in_bnd_order. split; assumption.
  Qed.
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    intros [|lo hi] z Hempty Hgamma; try discriminate. exact Hgamma.
  Qed.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn; intros; congruence.
  Qed.

  (** A singleton interval contains its defining integer. *)
  Lemma abst_sound : forall z, gamma (abst z) z.
  Proof.
    intro z. change (z <= z <= z)%Z. lia.
  Qed.

  (** Addition retains every sum of represented operands. *)
  Lemma add_sound : forall a b x y,
    gamma a x -> gamma b y -> gamma (add a b) (x + y).
  Proof.
    intros [|la ha] [|lb hb] x y Hx Hy; try contradiction.
    change (in_bnd la ha x) in Hx. change (in_bnd lb hb y) in Hy.
    destruct Hx as [Hla Hha], Hy as [Hlb Hhb]. unfold add, gamma, in_itv, in_bnd.
    split.
    - destruct la, lb; cbn in *; intuition lia.
    - destruct ha, hb; cbn in *; intuition lia.
  Qed.

  (** Subtraction retains every difference of represented operands. *)
  Lemma sub_sound : forall a b x y,
    gamma a x -> gamma b y -> gamma (sub a b) (x - y).
  Proof.
    intros [|la ha] [|lb hb] x y Hx Hy; try contradiction.
    change (in_bnd la ha x) in Hx. change (in_bnd lb hb y) in Hy.
    destruct Hx as [Hla Hha], Hy as [Hlb Hhb]. unfold sub, gamma, in_itv, in_bnd.
    split.
    - destruct la, hb; cbn in *; intuition lia.
    - destruct ha, lb; cbn in *; intuition lia.
  Qed.

  (** Multiplication by a fixed integer is bounded by the endpoint products. *)
  Lemma mul_endpoint_bounds : forall k lo hi v, (lo <= v <= hi)%Z ->
    (Z.min (k * lo) (k * hi) <= k * v <= Z.max (k * lo) (k * hi))%Z.
  Proof.
    intros k lo hi v Hv. destruct (Z_le_gt_dec 0 k) as [Hpos|Hneg].
    - rewrite Z.min_l, Z.max_r by nia. nia.
    - rewrite Z.min_r, Z.max_l by nia. nia.
  Qed.

  (** The four corner products bound every product from two finite ranges. *)
  Lemma mul_rectangle_bounds : forall la ha lb hb x y,
    (la <= x <= ha)%Z -> (lb <= y <= hb)%Z ->
    (Z.min (Z.min (la * lb) (la * hb)) (Z.min (ha * lb) (ha * hb)) <= x * y <=
      Z.max (Z.max (la * lb) (la * hb)) (Z.max (ha * lb) (ha * hb)))%Z.
  Proof.
    intros la ha lb hb x y Hx Hy.
    pose proof (mul_endpoint_bounds la lb hb y Hy) as [Hla Hha].
    pose proof (mul_endpoint_bounds ha lb hb y Hy) as [Hlb Hhb].
    assert (Hmid : (Z.min (la * y) (ha * y) <= x * y <= Z.max (la * y) (ha * y))%Z).
    { rewrite (Z.mul_comm la y), (Z.mul_comm ha y), (Z.mul_comm x y).
      apply mul_endpoint_bounds. exact Hx. }
    destruct Hmid as [Hlower Hupper]. split.
    - eapply Z.le_trans; [|exact Hlower]. apply Z.min_glb.
      + eapply Z.le_trans; [apply Z.le_min_l|exact Hla].
      + eapply Z.le_trans; [apply Z.le_min_r|exact Hlb].
    - eapply Z.le_trans; [exact Hupper|]. apply Z.max_lub.
      + eapply Z.le_trans; [exact Hha|apply Z.le_max_l].
      + eapply Z.le_trans; [exact Hhb|apply Z.le_max_r].
  Qed.

  (** Multiplication retains every product of represented operands. *)
  Lemma mul_sound : forall a b x y,
    gamma a x -> gamma b y -> gamma (mul a b) (x * y).
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]] x y Hx Hy;
      try contradiction; try apply gamma_top.
    change (la <= x <= ha)%Z in Hx. change (lb <= y <= hb)%Z in Hy.
    change (Z.min (Z.min (la * lb) (la * hb)) (Z.min (ha * lb) (ha * hb)) <= x * y <=
      Z.max (Z.max (la * lb) (la * hb)) (Z.max (ha * lb) (ha * hb)))%Z.
    now apply mul_rectangle_bounds.
  Qed.

  (** Point recognition identifies every integer represented by the interval. *)
  Lemma point_sound : forall a x c, gamma a x -> point a = Some c -> x = c.
  Proof.
    intros [|[|lo|] [|hi|]] x c Hx Hpoint; cbn in Hpoint; try discriminate.
    destruct (Z.eqb lo hi) eqn:Heq; [|discriminate].
    injection Hpoint as Hc. subst c. apply Z.eqb_eq in Heq.
    change (lo <= x <= hi)%Z in Hx. lia.
  Qed.

  (** Backward addition retains both operands of a represented sum. *)
  Lemma add_back_sound : forall r a b x y,
    gamma a x -> gamma b y -> gamma r (x + y) ->
    gamma (fst (add_back r a b)) x /\ gamma (snd (add_back r a b)) y.
  Proof.
    intros r a b x y Ha Hb Hr. split; apply gamma_meet; try assumption.
    - replace x with ((x + y) - y)%Z by lia. now apply sub_sound.
    - replace y with ((x + y) - x)%Z by lia. now apply sub_sound.
  Qed.

  (** Backward subtraction retains both operands of a represented difference. *)
  Lemma sub_back_sound : forall r a b x y,
    gamma a x -> gamma b y -> gamma r (x - y) ->
    gamma (fst (sub_back r a b)) x /\ gamma (snd (sub_back r a b)) y.
  Proof.
    intros r a b x y Ha Hb Hr. split; apply gamma_meet; try assumption.
    - replace x with ((x - y) + y)%Z by lia. now apply add_sound.
    - replace y with (x - (x - y))%Z by lia. now apply sub_sound.
  Qed.

  (** Multiplication preimages retain an operand of a represented product. *)
  Lemma mul_preimage_sound : forall r b x y,
    gamma b y -> gamma r (x * y) -> gamma (mul_preimage r b) x.
  Proof.
    intros r b x y Hb Hr. unfold mul_preimage.
    destruct (point b) as [z|] eqn:Hpoint; [|apply gamma_top].
    pose proof (point_sound b y z Hb Hpoint) as Hy. subst y.
    destruct (Z.eqb z 1) eqn:Hone.
    - apply Z.eqb_eq in Hone. subst z. now rewrite Z.mul_1_r in Hr.
    - destruct (Z.eqb z (-1)) eqn:Hneg; [|apply gamma_top].
      apply Z.eqb_eq in Hneg. subst z.
      replace x with (0 - x * (-1))%Z by ring.
      apply sub_sound; [apply abst_sound|exact Hr].
  Qed.

  (** Backward multiplication retains both operands of a represented product. *)
  Lemma mul_back_sound : forall r a b x y,
    gamma a x -> gamma b y -> gamma r (x * y) ->
    gamma (fst (mul_back r a b)) x /\ gamma (snd (mul_back r a b)) y.
  Proof.
    intros r a b x y Ha Hb Hr. split; apply gamma_meet; try assumption.
    - eapply mul_preimage_sound; eassumption.
    - eapply mul_preimage_sound; [exact Ha|]. now rewrite Z.mul_comm.
  Qed.

  (** Defined unsigned division and remainder retain nonnegative inputs and positive divisors. *)
  Lemma unsigned_back_sound : forall a b x y,
    gamma a x -> gamma b y -> (0 <= x)%Z -> (0 < y)%Z ->
    gamma (fst (unsigned_back a b)) x /\ gamma (snd (unsigned_back a b)) y.
  Proof.
    intros a b x y Ha Hb Hx Hy. split; apply gamma_meet; try assumption.
    - change ((0 <= x)%Z /\ True). tauto.
    - change ((1 <= y)%Z /\ True). split; [lia|trivial].
  Qed.
  Local Open Scope Z_scope.

  (** An all-ones mask above both nonnegative operands contains their disjunction. *)
  Lemma raw_lor_mask : forall x y hi,
    0 <= x <= hi -> 0 <= y <= hi ->
    0 <= Z.lor x y <= Z.ones (Z.log2 hi + 1).
  Proof.
    intros x y hi Hx Hy.
    set (n := Z.log2 hi + 1).
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
    rewrite Hor in Hdiff. lia.
  Qed.

  (** Raw disjunction contains every represented integer result. *)
  Lemma raw_bitor_sound : forall a b x y,
    gamma a x -> gamma b y -> gamma (bitor a b) (Z.lor x y).
  Proof.
    intros [|la ha] [|lb hb] x y Ha Hb;
      cbn [gamma in_itv] in Ha, Hb; try contradiction.
    destruct la as [|la|], ha as [|ha|], lb as [|lb|], hb as [|hb|];
      cbn [bitor]; try apply gamma_top.
    destruct ((0 <=? la) && (0 <=? lb))%bool eqn:Hnonneg;
      [|apply gamma_top].
    apply andb_true_iff in Hnonneg as [Hla Hlb].
    apply Z.leb_le in Hla. apply Z.leb_le in Hlb.
    unfold in_bnd in Ha, Hb; cbn in Ha, Hb. cbn [gamma in_itv]; unfold in_bnd; cbn.
    apply raw_lor_mask; pose proof (Z.le_max_l ha hb); pose proof (Z.le_max_r ha hb); lia.
  Qed.

  (** A nonnegative shift cannot decrease a nonnegative integer. *)
  Lemma raw_shiftl_grows : forall x y,
    0 <= x -> 0 <= y -> x <= Z.shiftl x y.
  Proof.
    intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by exact Hy.
    pose proof (Z.pow_pos_nonneg 2 y ltac:(lia) Hy). nia.
  Qed.

  (** Nonnegative endpoint shifts bound every enclosed pair. *)
  Lemma raw_shiftl_bounds : forall la ha lb hb x y,
    0 <= la -> 0 <= lb -> la <= x <= ha -> lb <= y <= hb ->
    Z.shiftl la lb <= Z.shiftl x y <= Z.shiftl ha hb.
  Proof.
    intros la ha lb hb x y Hla Hlb Hx Hy.
    rewrite !Z.shiftl_mul_pow2 by lia.
    assert (Hpowlo : 2 ^ lb <= 2 ^ y) by (apply Z.pow_le_mono_r; lia).
    assert (Hpowhi : 2 ^ y <= 2 ^ hb) by (apply Z.pow_le_mono_r; lia).
    assert (Hpowpos : 0 < 2 ^ lb) by (apply Z.pow_pos_nonneg; lia).
    nia.
  Qed.

  (** The shift cutoff preserves soundness when the upper endpoint is discarded. *)
  Lemma raw_shl_sound : forall a b x y,
    gamma a x -> gamma b y -> 0 <= y -> gamma (shl a b) (Z.shiftl x y).
  Proof.
    intros [|la ha] [|lb hb] x y Ha Hb Hy;
      cbn [gamma in_itv] in Ha, Hb; try contradiction.
    destruct la as [|la|], lb as [|lb|]; cbn [shl]; try apply gamma_top.
    destruct ((0 <=? la) && (0 <=? lb))%bool eqn:Hnonneg;
      [|apply gamma_top].
    apply andb_true_iff in Hnonneg as [Hla Hlb].
    apply Z.leb_le in Hla. apply Z.leb_le in Hlb.
    unfold in_bnd in Ha, Hb; cbn in Ha, Hb.
    assert (Hlower : la <= Z.shiftl x y).
    { eapply Z.le_trans; [exact (proj1 Ha)|apply raw_shiftl_grows; lia]. }
    destruct ha as [|ha|], hb as [|hb|]; cbn [gamma in_itv]; unfold in_bnd; cbn;
      try (split; [exact Hlower|constructor]).
    match goal with
    | |- context [if ?test then _ else _] => destruct test eqn:Hcutoff
    end;
      cbn [gamma in_itv]; unfold in_bnd; cbn.
    - apply raw_shiftl_bounds; assumption.
    - split; [exact Hlower|constructor].
  Qed.

  (** Raw conjunction is nonnegative and below both nonnegative operands. *)
  Lemma raw_land_bounds : forall x y,
    0 <= x -> 0 <= y -> 0 <= Z.land x y /\ Z.land x y <= x /\ Z.land x y <= y.
  Proof.
    intros x y Hx Hy.
    pose proof (Z.sub_land_same_l x y) as Hsubx.
    pose proof (Z.sub_land_same_l y x) as Hsuby. rewrite Z.land_comm in Hsuby.
    assert (Hdx : 0 <= Z.land x (Z.lnot y)) by (apply Z.land_nonneg; now left).
    assert (Hdy : 0 <= Z.land y (Z.lnot x)) by (apply Z.land_nonneg; now left).
    assert (Hxy : 0 <= Z.land x y) by (apply Z.land_nonneg; now left).
    lia.
  Qed.

  (** Raw conjunction contains every represented integer result. *)
  Lemma raw_bitand_sound : forall a b x y,
    gamma a x -> gamma b y -> gamma (bitand a b) (Z.land x y).
  Proof.
    intros [|la ha] [|lb hb] x y Ha Hb;
      cbn [gamma in_itv] in Ha, Hb; try contradiction.
    destruct la as [|la|], ha as [|ha|], lb as [|lb|], hb as [|hb|];
      cbn [bitand]; try apply gamma_top.
    destruct ((0 <=? la) && (0 <=? lb))%bool eqn:Hnonneg;
      [|apply gamma_top].
    apply andb_true_iff in Hnonneg as [Hla Hlb].
    apply Z.leb_le in Hla. apply Z.leb_le in Hlb.
    unfold in_bnd in Ha, Hb; cbn in Ha, Hb. cbn [gamma in_itv]; unfold in_bnd; cbn.
    pose proof (raw_land_bounds x y ltac:(lia) ltac:(lia)) as [Hxy [Hx Hy]].
    split; [exact Hxy|apply Z.min_glb; lia].
  Qed.

  (** Raw positive-divisor division is bounded by the opposite divisor endpoints. *)
  Lemma raw_udiv_sound : forall a b x y,
    gamma a x -> gamma b y -> gamma (udiv a b) (x / y).
  Proof.
    intros [|la ha] [|lb hb] x y Ha Hb;
      cbn [gamma in_itv] in Ha, Hb; try contradiction.
    destruct la as [|la|], ha as [|ha|], lb as [|lb|], hb as [|hb|];
      cbn [udiv]; try apply gamma_top.
    destruct ((0 <=? la) && (0 <? lb))%bool eqn:Hnonneg;
      [|apply gamma_top].
    apply andb_true_iff in Hnonneg as [Hla Hlb].
    apply Z.leb_le in Hla. apply Z.ltb_lt in Hlb.
    unfold in_bnd in Ha, Hb; cbn in Ha, Hb. cbn [gamma in_itv]; unfold in_bnd; cbn.
    split.
    - eapply Z.le_trans with (m := x / hb);
        [apply Z.div_le_mono; lia|apply Z.div_le_compat_l; lia].
    - eapply Z.le_trans with (m := x / lb);
        [apply Z.div_le_compat_l; lia|apply Z.div_le_mono; lia].
  Qed.

  (** Raw remainder lies below both the numerator and the divisor-minus-one bounds. *)
  Lemma raw_urem_sound : forall a b x y,
    gamma a x -> gamma b y -> gamma (urem a b) (x mod y).
  Proof.
    intros [|la ha] [|lb hb] x y Ha Hb;
      cbn [gamma in_itv] in Ha, Hb; try contradiction.
    destruct la as [|la|], ha as [|ha|], lb as [|lb|], hb as [|hb|];
      cbn [urem]; try apply gamma_top.
    destruct ((0 <=? la) && (0 <? lb))%bool eqn:Hnonneg;
      [|apply gamma_top].
    apply andb_true_iff in Hnonneg as [Hla Hlb].
    apply Z.leb_le in Hla. apply Z.ltb_lt in Hlb.
    unfold in_bnd in Ha, Hb; cbn in Ha, Hb. cbn [gamma in_itv]; unfold in_bnd; cbn.
    pose proof (Z.mod_pos_bound x y ltac:(lia)).
    pose proof (Z.mod_le x y ltac:(lia) ltac:(lia)).
    split; [lia|apply Z.min_glb; lia].
  Qed.

   (** Singleton comparison decisions and the Boolean fallback describe their result. *)
  Lemma raw_cmp_sound : forall c a b x y,
    gamma a x -> gamma b y ->
    gamma (cmp c a b)
      (if match Z.compare x y, c with
        | Eq, Eq | Lt, Lt | Gt, Gt => true | _, _ => false end then 1 else 0).
  Proof.
    intros c [|la ha] [|lb hb] x y Ha Hb; try contradiction.
    cbn [cmp].
    destruct (point (I la ha)) as [u|] eqn:Hu;
      destruct (point (I lb hb)) as [v|] eqn:Hv.
    - pose proof (point_sound _ _ _ Ha Hu) as Hx.
      pose proof (point_sound _ _ _ Hb Hv) as Hy. subst u v.
      unfold truth. destruct (Z.compare x y), c;
        cbn [abst gamma in_itv]; unfold in_bnd; cbn; lia.
    - destruct (Z.compare x y), c; cbn [gamma in_itv]; unfold in_bnd; cbn; lia.
    - destruct (Z.compare x y), c; cbn [gamma in_itv]; unfold in_bnd; cbn; lia.
    - destruct (Z.compare x y), c; cbn [gamma in_itv]; unfold in_bnd; cbn; lia.
  Qed.
  Local Close Scope Z_scope.

  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros o xs cs c Hxs Heval. unfold forward.
    destruct (L.view o) eqn:Hview; try apply gamma_top.
    all: rewrite (L.view_eval o cs ltac:(congruence)), Hview in Heval.
    all: destruct xs as [|a [|b [|extra xs]]]; try apply gamma_top.
    all: inversion Hxs as [|a' x tail values Ha Htail]; subst.
    all: try (cbn [zview_eval] in Heval; injection Heval as Hvalue;
      subst c; apply abst_sound).
    all: inversion Htail as [|b' y tail' values' Hb Hlast]; subst.
    all: inversion Hlast; subst.
    all: cbn [zview_eval] in Heval.
    all: try (match type of Heval with
      | (if ?test then Some _ else None) = Some _ =>
        destruct test eqn:Hdefined in Heval; try discriminate
      end).
    all: injection Heval as Hvalue; subst c.
    all: first [now apply add_sound | now apply sub_sound | now apply mul_sound |
      now apply raw_udiv_sound | now apply raw_urem_sound | now apply raw_bitand_sound |
      now apply raw_bitor_sound | now apply raw_cmp_sound |
      eapply raw_shl_sound; [exact Ha|exact Hb|now apply Z.leb_le in Hdefined]].
  Qed.
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hxs Heval Hr. unfold backward.
    destruct (L.view o) eqn:Hview; try exact Hxs.
    all: destruct xs as [|a [|b [|extra xs]]]; try exact Hxs.
    all: rewrite (L.view_eval o cs ltac:(congruence)), Hview in Heval.
    all: inversion Hxs as [|a' x tail values Ha Htail]; subst.
    all: inversion Htail as [|b' y tail' values' Hb Hlast]; subst.
    all: inversion Hlast; subst.
    all: cbn [zview_eval] in Heval.
    all: try (match type of Heval with
      | (if ?test then Some _ else None) = Some _ =>
        destruct test eqn:Hdefined in Heval; try discriminate
      end).
    all: injection Heval as Hvalue; subst c.
    all: try (apply andb_true_iff in Hdefined as [Hnonneg Hpositive];
      apply Z.leb_le in Hnonneg; apply Z.ltb_lt in Hpositive).
    all: first
      [destruct (add_back_sound r a b x y Ha Hb Hr) as [Hleft Hright] |
       destruct (sub_back_sound r a b x y Ha Hb Hr) as [Hleft Hright] |
       destruct (mul_back_sound r a b x y Ha Hb Hr) as [Hleft Hright] |
       destruct (unsigned_back_sound a b x y Ha Hb Hnonneg Hpositive) as [Hleft Hright]].
    all: constructor; [exact Hleft|constructor; [exact Hright|constructor]].
  Qed.
  Local Open Scope Z_scope.

  (** Strict comparison retains represented operands whose first value is smaller. *)
  Lemma strict_back_sound : forall a b x y,
    gamma a x -> gamma b y -> x < y ->
    gamma (fst (strict_back a b)) x /\ gamma (snd (strict_back a b)) y.
  Proof.
    intros [|la ha] [|lb hb] x y Ha Hb Hlt; try contradiction.
    cbn [strict_back fst snd]. split; apply gamma_meet; try assumption.
    - change (in_bnd lb hb y) in Hb. unfold in_bnd in Hb.
      cbn [gamma in_itv]. unfold in_bnd.
      destruct hb; cbn in *; intuition lia.
    - change (in_bnd la ha x) in Ha. unfold in_bnd in Ha.
      cbn [gamma in_itv]. unfold in_bnd.
      destruct la; cbn in *; intuition lia.
  Qed.

  (** Strict comparison returns a refinement of each original operand. *)
  Lemma strict_back_refines : forall a b,
    leb (fst (strict_back a b)) a = true /\
    leb (snd (strict_back a b)) b = true.
  Proof.
    intros [|la ha] [|lb hb]; cbn [strict_back fst snd]; split;
      first [apply bot_least | apply meet_lb_l].
  Qed.

  (** A represented comparison result preserves both operands of unsigned comparison. *)
  Lemma ult_back_sound : forall r a b x y,
    gamma a x -> gamma b y -> gamma r (if x <? y then 1 else 0) ->
    gamma (fst (ult_back r a b)) x /\ gamma (snd (ult_back r a b)) y.
  Proof.
    intros r a b x y Ha Hb Hr. unfold ult_back.
    destruct (point r) as [z|] eqn:Hpoint; [|split; assumption].
    destruct a as [|la ha], b as [|lb hb]; try contradiction.
    destruct la as [|la|], hb as [|hb|]; try (split; assumption).
    destruct (z =? 1) eqn:Hone; [|split; assumption].
    apply Z.eqb_eq in Hone. subst z.
    pose proof (point_sound r _ 1 Hr Hpoint) as Hresult.
    destruct (x <? y) eqn:Hlt; [|discriminate]. apply Z.ltb_lt in Hlt.
    cbn [fst snd]. split; apply gamma_meet; try assumption.
    - change (in_bnd lb (Fin hb) y) in Hb. unfold in_bnd in Hb. cbn in Hb.
      change (True /\ x <= hb - 1). intuition lia.
    - change (in_bnd (Fin la) ha x) in Ha. unfold in_bnd in Ha. cbn in Ha.
      change (la + 1 <= y /\ True). intuition lia.
  Qed.

  (** Unsigned comparison refinement stays below both original operands. *)
  Lemma ult_back_refines : forall r a b,
    leb (fst (ult_back r a b)) a = true /\
    leb (snd (ult_back r a b)) b = true.
  Proof.
    intros r a b. unfold ult_back.
    destruct (point r) as [z|]; [|split; apply leb_refl].
    destruct a as [|[|la|] ha], b as [|lb [|hb|]];
      try (split; apply leb_refl).
    destruct (z =? 1); cbn [fst snd]; split;
      first [apply meet_lb_l | apply leb_refl].
  Qed.

  (** Every operand list refines itself position by position. *)
  Lemma operands_refine_refl : forall xs,
    Forall2 (fun y x => leb y x = true) xs xs.
  Proof.
    induction xs as [|a xs IH]; constructor; [apply leb_refl | exact IH].
  Qed.

  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof.
    intros o r xs. unfold backward.
    destruct (L.view o); destruct xs as [|a [|b [|extra rest]]];
      try apply operands_refine_refl.
    all: cbn [add_back sub_back mul_back udiv_back urem_back unsigned_back fst snd];
      repeat constructor; apply meet_lb_l.
  Qed.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof.
    intros g xs cs Hxs Hholds.
    destruct (L.gview g) as [c| |] eqn:Hview;
      [| |unfold guard; rewrite Hview; exact Hxs].
    all: pose proof (proj1 (L.gview_holds g cs
      ltac:(rewrite Hview; discriminate)) Hholds) as Hguard.
    all: rewrite Hview in Hguard.
    all: destruct cs as [|x [|y [|extra rest]]]; try contradiction.
    all: inversion Hxs as [|a x' tail values Ha Htail]; subst.
    all: inversion Htail as [|b y' tail' values' Hb Hlast]; subst.
    all: inversion Hlast; subst.
    all: unfold guard; rewrite Hview.
    - change (Z.compare x y = c) in Hguard. destruct c.
      + apply Z.compare_eq_iff in Hguard. subst y.
        repeat constructor; apply gamma_meet; assumption.
      + apply Z.compare_lt_iff in Hguard.
        destruct (strict_back_sound a b x y Ha Hb Hguard) as [Hx Hy].
        constructor; [exact Hx|constructor; [exact Hy|constructor]].
      + apply Z.compare_gt_iff in Hguard.
        destruct (strict_back_sound b a y x Hb Ha Hguard) as [Hy Hx].
        constructor; [exact Hx|constructor; [exact Hy|constructor]].
    - change (0 <= x /\ 0 <= y /\ x < y) in Hguard.
      destruct Hguard as [Hnonnegx [Hnonnegy Hlt]].
      assert (Hresult : gamma (abst 1) (if x <? y then 1 else 0)).
      { assert (Hltb : (x <? y) = true) by (apply Z.ltb_lt; exact Hlt).
        rewrite Hltb. apply abst_sound. }
      destruct (ult_back_sound (abst 1) a b x y Ha Hb Hresult) as [Hx Hy].
      constructor; [exact Hx|constructor; [exact Hy|constructor]].
  Qed.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof.
    intros g xs. unfold guard.
    destruct (L.gview g) as [c| |]; [destruct c| |].
    all: destruct xs as [|a [|b [|extra rest]]]; try apply operands_refine_refl.
    - repeat constructor; apply meet_lb_l.
    - destruct (strict_back_refines a b) as [Ha Hb].
      constructor; [exact Ha|constructor; [exact Hb|constructor]].
    - destruct (strict_back_refines b a) as [Hb Ha].
      constructor; [exact Ha|constructor; [exact Hb|constructor]].
    - destruct (ult_back_refines (abst 1) a b) as [Ha Hb].
      constructor; [exact Ha|constructor; [exact Hb|constructor]].
  Qed.
  Local Close Scope Z_scope.
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
  Module ScalarTime := IntervalBaseT T.

  Definition size := itv_bits.
  Definition wsize (ts : ttree) := (T.depth ts + 1) * (T.tree_bits ts + 1).
  Definition wunits (_ : t) : nat := 0.
  Definition operand_bits (xs : list t) := fold_right Nat.add 0 (map size xs).
  Definition work (o : L.op) (xs : list t) :=
    operand_bits xs + length xs + (operand_bits xs + 1) ^ 2 +
    match L.view o with ZConst z => Z.size_nat z | _ => 0 end.
  Definition gwork (_ : L.guard) (xs : list t) :=
    operand_bits xs + length xs + (operand_bits xs + 1) ^ 2.
  Definition c_val : N := (65536 * (T.c_thresholds + L.c_view + 1))%N.
  Definition c_lat : N := c_val.
  Definition c_interval : N := (8192 * (T.c_thresholds + 1))%N.
  Definition k_interval_arith : N := 8192%N.
  Definition k_interval_back : N := 8192%N.
  Definition k_interval_widen : N := (64 * (T.c_thresholds + 1))%N.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat, c_val. nia.
  Qed.
  (** Inclusion testing costs at most the combined abstract sizes. *)
  Lemma T_leb_le : forall a b, (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (ScalarTime.T_interval_leb_le a b) as Htime.
    change (T_interval_leb a b <=
      ScalarTime.c_scalar * N.of_nat (size a + size b + 1))%N in Htime.
    unfold T_leb, c_val, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + size b + 1))%N) by lia. nia.
  Qed.
  (** Join costs at most the combined abstract sizes. *)
  Lemma T_join_le : forall a b, (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (ScalarTime.T_interval_join_le a b) as Htime.
    change (T_interval_join a b <=
      ScalarTime.c_scalar * N.of_nat (size a + size b + 1))%N in Htime.
    unfold T_join, c_val, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + size b + 1))%N) by lia. nia.
  Qed.
  (** Meet costs at most the combined abstract sizes. *)
  Lemma T_meet_le : forall a b, (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (ScalarTime.T_interval_meet_le a b) as Htime.
    change (T_interval_meet a b <=
      ScalarTime.c_scalar * N.of_nat (size a + size b + 1))%N in Htime.
    unfold T_meet, c_val, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + size b + 1))%N) by lia. nia.
  Qed.
  (** Bottom testing costs at most the abstract size. *)
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof.
    intros a. pose proof (ScalarTime.T_interval_is_bot_le a) as Htime.
    change (T_interval_is_bot a <= ScalarTime.c_scalar)%N in Htime.
    unfold T_is_bot, c_val, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + 1))%N) by lia. nia.
  Qed.
  (** Widening charges both values and the widening parameters. *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. pose proof (ScalarTime.T_interval_stable_widen_le p a b) as Htime.
    change (T_interval_stable_widen p a b <=
      ScalarTime.c_scalar * N.of_nat (size a + size b + wsize p + 1))%N in Htime.
    unfold T_widen, c_val, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + size b + wsize p + 1))%N) by lia. nia.
  Qed.
  (** Narrowing charges both abstract values. *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (ScalarTime.T_interval_narrow_le a b) as Htime.
    change (T_interval_narrow a b <= ScalarTime.c_scalar)%N in Htime.
    unfold T_narrow, c_val, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + size b + 1))%N) by lia. nia.
  Qed.
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
  Proof.
    intros a b. pose proof (ScalarTime.interval_meet_bits a b) as Hbits.
    change (size (meet a b) <= size a + size b) in Hbits.
    unfold c_val. nia.
  Qed.
  (** Join results fit within the combined operand sizes. *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (ScalarTime.interval_join_bits a b) as Hbits.
    change (size (join a b) <= size a + size b) in Hbits.
    unfold c_val. nia.
  Qed.
  (** Widening results fit within the operand and parameter sizes. *)
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. pose proof (ScalarTime.interval_stable_widen_bits p a b) as Hbits.
    change (size (widen p a b) <= size a + size b + T.tree_bits p) in Hbits.
    assert (Hparam : T.tree_bits p <= wsize p) by (unfold wsize; nia).
    unfold c_val. nia.
  Qed.
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
  Proof.
    intros o xs. unfold work, operand_bits. lia.
  Qed.
  (** Guard work accounts for every operand size. *)
  Lemma gwork_sizes : forall g xs, fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof.
    intros g xs. unfold gwork, operand_bits. lia.
  Qed.
  (** Interval size records the largest endpoint bit size. *)
  Lemma size_bits : forall a, size a = itv_bits a.
  Proof.
    reflexivity.
  Qed.
  (** Point recognition charges both endpoint comparisons. *)
  Lemma T_point_le : forall a, (T_point a <= c_interval * N.of_nat ((size a + 1)%nat))%N.
  Proof.
    intros a. pose proof (ScalarTime.T_interval_singleton_le a) as Htime.
    change (T_interval_singleton a <=
      ScalarTime.c_scalar * N.of_nat (size a + 1))%N in Htime.
    unfold T_point, c_interval, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + 1))%N) by lia. nia.
  Qed.
  (** A singleton interval shares its integer argument. *)
  Lemma T_abst_le : forall z, (T_abst z <= c_interval)%N.
  Proof.
    intros z. unfold T_abst, c_interval. nia.
  Qed.
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
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward subtraction charges the result and both operands. *)
  Lemma T_sub_back_le : forall r a b, (T_sub_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward multiplication charges the result and both operands. *)
  Lemma T_mul_back_le : forall r a b, (T_mul_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward unsigned division charges the result and both operands. *)
  Lemma T_udiv_back_le : forall r a b, (T_udiv_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward unsigned remainder charges the result and both operands. *)
  Lemma T_urem_back_le : forall r a b, (T_urem_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Backward comparison charges the result and both operands. *)
  Lemma T_ult_back_le : forall r a b, (T_ult_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Signed splitting charges the width and endpoints. *)
  Lemma T_signed_split_le : forall w a, (T_signed_split w a <=
    c_interval * N.of_nat (((Pos.to_nat w + size a + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Threshold widening charges a search path and endpoint bit sizes. *)
  Lemma T_widen_thresholds_le : forall ts a b, (T_widen ts a b <=
    c_interval * N.of_nat
      ((size a + size b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1)%nat))%N.
  Proof.
    intros ts a b. pose proof (ScalarTime.T_interval_stable_widen_le ts a b) as Htime.
    change (T_interval_stable_widen ts a b <=
      ScalarTime.c_scalar * N.of_nat (size a + size b + wsize ts + 1))%N in Htime.
    change (T_widen ts a b <=
      c_interval * N.of_nat (size a + size b + wsize ts + 1))%N.
    unfold T_widen, c_interval, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + size b + wsize ts + 1))%N) by lia. nia.
  Qed.
  (** Interval concretization is inclusive endpoint membership. *)
  Lemma F1_gamma : forall a z, gamma a z <-> in_itv a z.
  Proof.
    reflexivity.
  Qed.
  (** Widening uses the count of thresholds beyond each finite endpoint. *)
  Lemma F2_wrank : forall ts a, wrank ts a = interval_wrank ts a.
  Proof.
    reflexivity.
  Qed.
  (** Each endpoint contributes at most one plus the threshold count. *)
  Lemma F3_wrank_le : forall ts a, wrank ts a <= 2 * (length (T.vals ts) + 1).
  Proof.
    intros ts [|lo hi]; [cbn; lia|].
    change (upper_rank (T.vals ts) hi + lower_rank (T.vals ts) lo <=
      2 * (length (T.vals ts) + 1)).
    destruct lo as [|lo|], hi as [|hi|]; cbn [upper_rank lower_rank];
      try pose proof (lower_count_bounded (T.vals ts) lo);
      try pose proof (upper_count_bounded (T.vals ts) hi); lia.
  Qed.
  (** Raising a finite upper endpoint to its next threshold removes one rank unit. *)
  Lemma F4_count_gt : forall ts z u, In u (T.vals ts) ->
    (z < u)%Z -> count_gt ts u < count_gt ts z.
  Proof.
    intros ts z u Hin Hlt. exact (upper_count_strict (T.vals ts) z u Hin Hlt).
  Qed.
  (** Lowering a finite lower endpoint to its previous threshold removes one rank unit. *)
  Lemma F5_count_lt : forall ts z u, In u (T.vals ts) ->
    (u < z)%Z -> count_lt ts u < count_lt ts z.
  Proof.
    intros ts z u Hin Hlt. exact (lower_count_strict (T.vals ts) u z Hin Hlt).
  Qed.
  (** Widening parameter size pays for a threshold search path. *)
  Lemma F_wsize : forall ts, wsize ts = (T.depth ts + 1) * (T.tree_bits ts + 1).
  Proof.
    reflexivity.
  Qed.
  (** Shift transfer computes finite endpoints below the cutoff and a sound infinity above it. *)
  Lemma F_shl_cutoff : forall a b, shl a b = shift_cutoff a b.
  Proof.
    reflexivity.
  Qed.
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
  Proof.
    reflexivity.
  Qed.
  (** Viewed strict guards dispatch to unsigned comparison refinement. *)
  Lemma F_guard_lt : forall g a b, L.gview g = ZGuardUlt ->
    guard g (a :: b :: nil) =
      let result := ult_back (I (Fin 1) (Fin 1)) a b in
      fst result :: snd result :: nil.
  Proof.
    intros g a b Hview. unfold guard. now rewrite Hview.
  Qed.
  (** Cutoff shifting keeps the published quadratic endpoint bound. *)
  Lemma T3_shl : forall a b,
    (T_shl a b <= k_interval_arith * N.of_nat (binary_work a b))%N.
  Proof. Admitted. (* STUB *)
  (** Addition retains every sum of represented operands. *)
  Lemma F6_add_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (add a b) (x + y).
  Proof.
    exact add_sound.
  Qed.
  (** Subtraction retains every difference of represented operands. *)
  Lemma F7_sub_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (sub a b) (x - y).
  Proof.
    exact sub_sound.
  Qed.
  (** Multiplication retains every product of represented operands. *)
  Lemma F8_mul_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (mul a b) (x * y).
  Proof.
    exact mul_sound.
  Qed.
  (** Unsigned division retains each defined quotient of nonnegative operands. *)
  Lemma F9_udiv_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= x)%Z -> (0 < y)%Z -> in_itv (udiv a b) (Z.div x y).
  Proof.
    intros a b x y Ha Hb _ _. now apply raw_udiv_sound.
  Qed.
  (** Unsigned remainder retains each defined remainder of nonnegative operands. *)
  Lemma F10_urem_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= x)%Z -> (0 < y)%Z -> in_itv (urem a b) (Z.modulo x y).
  Proof.
    intros a b x y Ha Hb _ _. now apply raw_urem_sound.
  Qed.
  (** Bitwise conjunction retains every represented pair of operands. *)
  Lemma F11_and_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (bitand a b) (Z.land x y).
  Proof.
    exact raw_bitand_sound.
  Qed.
  (** Bitwise disjunction retains every represented pair of operands. *)
  Lemma F12_or_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (bitor a b) (Z.lor x y).
  Proof.
    exact raw_bitor_sound.
  Qed.
  (** Left shifting retains represented operands for every nonnegative shift. *)
  Lemma F13_shl_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= y)%Z -> in_itv (shl a b) (Z.shiftl x y).
  Proof.
    exact raw_shl_sound.
  Qed.
  (** Unsigned comparison refinement descends in both operands. *)
  Lemma F22_ult_back_lower : forall r a b,
    leb (fst (ult_back r a b)) a = true /\ leb (snd (ult_back r a b)) b = true.
  Proof.
    exact ult_back_refines.
  Qed.
  (** Comparison contains the Boolean result as zero or one. *)
  Lemma F14_cmp_sound : forall c a b x y, in_itv a x -> in_itv b y ->
    in_itv (cmp c a b) (match Z.compare x y, c with Eq, Eq | Lt, Lt | Gt, Gt => 1 | _, _ => 0 end).
  Proof.
    intros c a b x y Ha Hb. pose proof (raw_cmp_sound c a b x y Ha Hb) as Hcmp.
    destruct (Z.compare x y), c; exact Hcmp.
  Qed.
  (** Signed splitting retains the signed view of every normalized word. *)
  Lemma F15_signed_split_sound : forall w a x, in_itv a x ->
    (0 <= x < 2 ^ Zpos w)%Z ->
    exists b, In b (signed_split w a) /\
      in_itv b (if (x <? 2 ^ (Zpos w - 1))%Z then x else x - 2 ^ Zpos w).
  Proof.
    intros w a x Ha Hword. unfold signed_split.
    set (m := (2 ^ Zpos w)%Z) in *.
    set (h := (2 ^ (Zpos w - 1))%Z).
    destruct (Z.ltb x h) eqn:Hhalf.
    - exists (meet a (I (Fin 0) (Fin (h - 1)))). split; [now left|].
      apply gamma_meet; [exact Ha|]. change (0 <= x <= h - 1)%Z.
      apply Z.ltb_lt in Hhalf. lia.
    - exists (sub (meet a (I (Fin h) (Fin (m - 1)))) (abst m)).
      split; [right; now left|]. apply sub_sound; [|apply abst_sound].
      apply gamma_meet; [exact Ha|]. change (h <= x <= m - 1)%Z.
      apply Z.ltb_ge in Hhalf. lia.
  Qed.
  (** Backward addition retains operands consistent with its result. *)
  Lemma F16_add_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x + y) ->
    in_itv (fst (add_back r a b)) x /\ in_itv (snd (add_back r a b)) y.
  Proof.
    exact add_back_sound.
  Qed.
  (** Backward subtraction retains operands consistent with its result. *)
  Lemma F17_sub_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x - y) ->
    in_itv (fst (sub_back r a b)) x /\ in_itv (snd (sub_back r a b)) y.
  Proof.
    exact sub_back_sound.
  Qed.
  (** Backward multiplication retains operands consistent with its result. *)
  Lemma F18_mul_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x * y) ->
    in_itv (fst (mul_back r a b)) x /\ in_itv (snd (mul_back r a b)) y.
  Proof.
    exact mul_back_sound.
  Qed.
  (** Backward division retains operands consistent with a defined unsigned quotient. *)
  Lemma F19_udiv_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 < y)%Z -> in_itv r (Z.div x y) ->
    in_itv (fst (udiv_back r a b)) x /\ in_itv (snd (udiv_back r a b)) y.
  Proof.
    intros r a b x y Ha Hb Hx Hy _. now apply unsigned_back_sound.
  Qed.
  (** Backward remainder retains operands consistent with a defined unsigned remainder. *)
  Lemma F20_urem_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 < y)%Z -> in_itv r (Z.modulo x y) ->
    in_itv (fst (urem_back r a b)) x /\ in_itv (snd (urem_back r a b)) y.
  Proof.
    intros r a b x y Ha Hb Hx Hy _. now apply unsigned_back_sound.
  Qed.
  (** Backward unsigned comparison retains operands with the specified Boolean result. *)
  Lemma F21_ult_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 <= y)%Z ->
    in_itv r (if (x <? y)%Z then 1 else 0) ->
    in_itv (fst (ult_back r a b)) x /\ in_itv (snd (ult_back r a b)) y.
  Proof.
    intros r a b x y Ha Hb _ _ Hr. now apply ult_back_sound.
  Qed.
  (** Endpoint arithmetic bounds multiplication before dispatch overhead. *)
  Lemma T1_mul : forall a b, (T_mul a b <= k_interval_arith * N.of_nat (binary_work a b))%N.
  Proof. Admitted. (* STUB *)
  (** Threshold searches bound widening before dispatch overhead. *)
  Lemma T2_widen : forall ts a b,
    (T_widen ts a b <= k_interval_widen * N.of_nat
      (size a + size b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1))%N.
  Proof.
    intros ts a b. pose proof (ScalarTime.T_interval_stable_widen_le ts a b) as Htime.
    change (T_interval_stable_widen ts a b <=
      ScalarTime.c_scalar * N.of_nat (size a + size b + wsize ts + 1))%N in Htime.
    change (T_widen ts a b <=
      k_interval_widen * N.of_nat (size a + size b + wsize ts + 1))%N.
    unfold T_widen, k_interval_widen, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + size b + wsize ts + 1))%N) by lia. nia.
  Qed.
  (** Multiplication has the published quadratic endpoint bound. *)
  Lemma mul_bigO : (bigO (fun _ => True)
    (fun ab => N.of_nat ((binary_work (fst ab) (snd ab))%nat))
    (fun ab => T_mul (fst ab) (snd ab)))%N.
  Proof. Admitted. (* STUB *)
End IntervalT.
