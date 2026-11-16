(** * Interval lattice operations

    Intervals use integer bounds and threshold widening.
    For example, meeting disjoint finite intervals returns bottom.
    Builds on: IntervalSig and ThresholdsSig. *)

From Stdlib Require Import ZArith Zpow_facts NArith Bool List Lia.
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

  (** Scalar inclusion has the published endpoint-bit class. *)
  Lemma interval_leb_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (interval_bits (fst x) + interval_bits (snd x) + 1))
    (fun x => T_interval_leb (fst x) (snd x)).
  Proof. Admitted. (* STUB *)

  (** Scalar join has the published endpoint-bit class. *)
  Lemma interval_join_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (interval_bits (fst x) + interval_bits (snd x) + 1))
    (fun x => T_interval_join (fst x) (snd x)).
  Proof. Admitted. (* STUB *)

  (** Scalar meet has the published endpoint-bit class. *)
  Lemma interval_meet_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (interval_bits (fst x) + interval_bits (snd x) + 1))
    (fun x => T_interval_meet (fst x) (snd x)).
  Proof. Admitted. (* STUB *)

  (** Scalar widening has the published bits-plus-search-path class. *)
  Lemma interval_stable_widen_bigO : bigO (X := ttree * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (interval_bits (fst (snd x)) + interval_bits (snd (snd x)) +
      (T.depth (fst x) + 1) * (T.tree_bits (fst x) + 1) + 1))
    (fun x => T_interval_stable_widen (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)

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
  (** Adding positive integers increases the combined bit bound by at most one. *)
  Lemma positive_add_bits : forall p q,
    Pos.size_nat (p + q) <= Pos.size_nat p + Pos.size_nat q + 1.
  Proof.
    intros p q. apply Std.Pos.size_nat_least.
    rewrite Pos2Nat.inj_add, !Nat.pow_add_r. cbn [Nat.pow].
    pose proof (Std.Pos.size_nat_upper p).
    pose proof (Std.Pos.size_nat_upper q).
    pose proof (Pos2Nat.is_pos p). pose proof (Pos2Nat.is_pos q). nia.
  Qed.

  (** A signed difference of positive integers fits their combined bit sizes. *)
  Lemma positive_difference_bits : forall p q,
    Z.size_nat (Z.pos_sub p q) <= Pos.size_nat p + Pos.size_nat q.
  Proof.
    intros p q. rewrite Z.pos_sub_spec. destruct (Pos.compare p q);
      cbn [Z.size_nat]; try lia;
      pose proof (Std.Pos.size_nat_sub p q);
      pose proof (Std.Pos.size_nat_sub q p); lia.
  Qed.

  (** Negation preserves the bit size of an integer. *)
  Lemma integer_opp_bits : forall z, Z.size_nat (- z) = Z.size_nat z.
  Proof.
    intros []; reflexivity.
  Qed.

  (** Integer addition has a linear result-size bound. *)
  Lemma integer_add_bits : forall x y,
    Z.size_nat (x + y) <= Z.size_nat x + Z.size_nat y + 1.
  Proof.
    intros [|p|p] [|q|q]; cbn [Z.add Z.size_nat]; try lia;
      try apply positive_add_bits;
      pose proof (positive_difference_bits p q);
      pose proof (positive_difference_bits q p); lia.
  Qed.

  (** Integer subtraction has the same linear result-size bound. *)
  Lemma integer_sub_bits : forall x y,
    Z.size_nat (x - y) <= Z.size_nat x + Z.size_nat y + 1.
  Proof.
    intros x y. change (Z.size_nat (x + - y) <= Z.size_nat x + Z.size_nat y + 1).
    pose proof (integer_add_bits x (- y)). rewrite integer_opp_bits in *. lia.
  Qed.

  (** Integer multiplication adds the operand bit bounds. *)
  Lemma integer_mul_bits : forall x y,
    Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y.
  Proof.
    intros [|p|p] [|q|q]; cbn [Z.mul Z.size_nat]; try lia;
      apply Std.Pos.size_nat_mul.
  Qed.

  (** Minimum selects one of the input integers. *)
  Lemma integer_min_bits : forall x y,
    Z.size_nat (Z.min x y) <= Nat.max (Z.size_nat x) (Z.size_nat y).
  Proof.
    intros x y. unfold Z.min. destruct (Z.compare x y);
      first [apply Nat.le_max_l | apply Nat.le_max_r].
  Qed.

  (** Maximum selects one of the input integers. *)
  Lemma integer_max_bits : forall x y,
    Z.size_nat (Z.max x y) <= Nat.max (Z.size_nat x) (Z.size_nat y).
  Proof.
    intros x y. unfold Z.max. destruct (Z.compare x y);
      first [apply Nat.le_max_l | apply Nat.le_max_r].
  Qed.

  (** Both endpoint bit sizes are bounded by the interval size. *)
  Lemma endpoint_sizes : forall lo hi,
    bnd_bits lo <= size (I lo hi) /\ bnd_bits hi <= size (I lo hi).
  Proof.
    intros lo hi. unfold size, itv_bits. split;
      [apply Nat.le_max_l | apply Nat.le_max_r].
  Qed.

  (** A finite endpoint addition is linear in its arguments. *)
  Lemma endpoint_add_time : forall a b,
    ((match a, b with Fin x, Fin y => Std.Z.T_add x y | _, _ => 0 end) <=
      3 * N.of_nat (bnd_bits a + bnd_bits b) + 1)%N.
  Proof.
    intros [|x|] [|y|]; cbn [bnd_bits]; try nia.
    apply Std.Z.T_add_le.
  Qed.

  (** A finite endpoint subtraction is linear in its arguments. *)
  Lemma endpoint_sub_time : forall a b,
    ((match a, b with Fin x, Fin y => Std.Z.T_sub x y | _, _ => 0 end) <=
      3 * N.of_nat (bnd_bits a + bnd_bits b) + 3)%N.
  Proof.
    intros [|x|] [|y|]; cbn [bnd_bits]; try nia.
    apply Std.Z.T_sub_le.
  Qed.

  (** Interval addition pays for at most two endpoint additions. *)
  Lemma add_time_linear : forall a b,
    (T_add a b <= 8 * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|la ha] [|lb hb]; time_unfold T_add; try nia.
    pose proof (endpoint_sizes la ha) as [Hla Hha].
    pose proof (endpoint_sizes lb hb) as [Hlb Hhb].
    pose proof (endpoint_add_time la lb).
    pose proof (endpoint_add_time ha hb). nia.
  Qed.

  (** Interval subtraction pays for at most two endpoint subtractions. *)
  Lemma sub_time_linear : forall a b,
    (T_sub a b <= 8 * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|la ha] [|lb hb]; time_unfold T_sub; try nia.
    pose proof (endpoint_sizes la ha) as [Hla Hha].
    pose proof (endpoint_sizes lb hb) as [Hlb Hhb].
    pose proof (endpoint_sub_time la hb).
    pose proof (endpoint_sub_time ha lb). nia.
  Qed.

  (** Endpoint addition fits the operand sizes and one carry bit. *)
  Lemma endpoint_add_bits : forall a b,
    (match a, b with Fin x, Fin y => Z.size_nat (x + y) | _, _ => 0 end) <=
      bnd_bits a + bnd_bits b + 1.
  Proof.
    intros [|x|] [|y|]; cbn [bnd_bits]; try lia. apply integer_add_bits.
  Qed.

  (** Endpoint subtraction fits the operand sizes and one carry bit. *)
  Lemma endpoint_sub_bits : forall a b,
    (match a, b with Fin x, Fin y => Z.size_nat (x - y) | _, _ => 0 end) <=
      bnd_bits a + bnd_bits b + 1.
  Proof.
    intros [|x|] [|y|]; cbn [bnd_bits]; try lia. apply integer_sub_bits.
  Qed.

  (** Addition stores at most a linear number of endpoint bits. *)
  Lemma add_result_bits : forall a b, size (add a b) <= size a + size b + 1.
  Proof.
    intros [|la ha] [|lb hb]; cbn [add size itv_bits]; try lia.
    pose proof (endpoint_sizes la ha) as [Hla Hha].
    pose proof (endpoint_sizes lb hb) as [Hlb Hhb].
    pose proof (endpoint_add_bits la lb). pose proof (endpoint_add_bits ha hb).
    unfold size, itv_bits in *. apply Nat.max_lub;
      destruct la, ha, lb, hb; cbn [bnd_bits] in *; lia.
  Qed.

  (** Subtraction stores at most a linear number of endpoint bits. *)
  Lemma sub_result_bits : forall a b, size (sub a b) <= size a + size b + 1.
  Proof.
    intros [|la ha] [|lb hb]; cbn [sub size itv_bits]; try lia.
    pose proof (endpoint_sizes la ha) as [Hla Hha].
    pose proof (endpoint_sizes lb hb) as [Hlb Hhb].
    pose proof (endpoint_sub_bits la hb). pose proof (endpoint_sub_bits ha lb).
    unfold size, itv_bits in *. apply Nat.max_lub;
      destruct la, ha, lb, hb; cbn [bnd_bits] in *; lia.
  Qed.

  (** A singleton stores the bit size of its integer. *)
  Lemma abst_result_bits : forall z, size (abst z) = Z.size_nat z.
  Proof.
    intro z. unfold abst, size, itv_bits, bnd_bits. apply Nat.max_id.
  Qed.

  (** A recognized point is one of the stored finite endpoints. *)
  Lemma point_result_bits : forall a z, point a = Some z -> Z.size_nat z <= size a.
  Proof.
    intros [|[|lo|] [|hi|]] z Hpoint; cbn in Hpoint;
      try discriminate.
    destruct (Z.eqb lo hi); inversion Hpoint; subst.
    unfold size, itv_bits, bnd_bits. apply Nat.le_max_l.
  Qed.

  (** Meeting costs linearly in raw interval sizes with a fixed scalar constant. *)
  Lemma meet_time_linear : forall a b,
    (T_meet a b <= 64 * (T.c_thresholds + 1) * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (ScalarTime.T_interval_meet_le a b) as Htime.
    change (T_interval_meet a b <=
      ScalarTime.c_scalar * N.of_nat (size a + size b + 1))%N in Htime.
    unfold T_meet, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + size b + 1))%N) by lia. nia.
  Qed.

  (** Point recognition has a small linear endpoint bound. *)
  Lemma point_time_linear : forall a,
    (T_point a <= 64 * (T.c_thresholds + 1) * N.of_nat (size a + 1))%N.
  Proof.
    intros a. pose proof (ScalarTime.T_interval_singleton_le a) as Htime.
    change (T_interval_singleton a <=
      ScalarTime.c_scalar * N.of_nat (size a + 1))%N in Htime.
    unfold T_point, ScalarTime.c_scalar in *.
    assert (Hpos : (1 <= N.of_nat (size a + 1))%N) by lia. nia.
  Qed.

  (** Multiplication is quadratic in a common bound on its operand sizes. *)
  Lemma integer_mul_time : forall x y k,
    Z.size_nat x + Z.size_nat y + 1 <= k ->
    (Std.Z.T_mul x y <= 3 * N.of_nat (k * k))%N.
  Proof.
    intros x y k Hbits. pose proof (Std.Z.T_mul_le x y).
    rewrite Nat2N.inj_mul. nia.
  Qed.

  (** The four products all fit the combined endpoint size. *)
  Lemma mul_result_bits : forall a b, size (mul a b) <= size a + size b.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      cbn [mul top size itv_bits bnd_bits]; try lia.
    pose proof (integer_mul_bits la lb).
    pose proof (integer_mul_bits la hb).
    pose proof (integer_mul_bits ha lb).
    pose proof (integer_mul_bits ha hb).
    pose proof (integer_min_bits (la * lb) (la * hb)).
    pose proof (integer_min_bits (ha * lb) (ha * hb)).
    pose proof (integer_min_bits (Z.min (la * lb) (la * hb))
      (Z.min (ha * lb) (ha * hb))).
    pose proof (integer_max_bits (la * lb) (la * hb)).
    pose proof (integer_max_bits (ha * lb) (ha * hb)).
    pose proof (integer_max_bits (Z.max (la * lb) (la * hb))
      (Z.max (ha * lb) (ha * hb))). lia.
  Qed.

  (** Extrema cost linearly in any bound on the first operand bits. *)
  Lemma integer_extrema_time : forall x y k,
    Z.size_nat x <= k ->
    (Std.Z.T_min x y <= N.of_nat k + 4 /\
      Std.Z.T_max x y <= N.of_nat k + 4)%N.
  Proof.
    intros x y k Hbits. pose proof (Std.Z.T_min_le x y).
    pose proof (Std.Z.T_max_le x y). split; lia.
  Qed.

  (** Four products and six extrema have a uniform quadratic interval cost. *)
  Lemma mul_time_quadratic : forall a b,
    (T_mul a b <= 64 * N.of_nat (binary_work a b))%N.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      time_unfold T_mul; try (unfold binary_work; cbn [Nat.pow]; nia).
    set (s := (size (I (Fin la) (Fin ha)) + size (I (Fin lb) (Fin hb)) + 1)%nat).
    assert (Hpair : forall x y, (x = la \/ x = ha) -> (y = lb \/ y = hb) ->
      Z.size_nat x + Z.size_nat y + 1 <= s).
    { intros x y [Hx | Hx] [Hy | Hy]; subst x; subst y;
        unfold s, size, itv_bits, bnd_bits; lia. }
    pose proof (integer_mul_time la lb s (Hpair _ _ (or_introl eq_refl)
      (or_introl eq_refl))) as Hmul1.
    pose proof (integer_mul_time la hb s (Hpair _ _ (or_introl eq_refl)
      (or_intror eq_refl))) as Hmul2.
    pose proof (integer_mul_time ha lb s (Hpair _ _ (or_intror eq_refl)
      (or_introl eq_refl))) as Hmul3.
    pose proof (integer_mul_time ha hb s (Hpair _ _ (or_intror eq_refl)
      (or_intror eq_refl))) as Hmul4.
    assert (Hprod : forall x y, (x = la \/ x = ha) -> (y = lb \/ y = hb) ->
      Z.size_nat (x * y) <= s).
    { intros x y Hx Hy. pose proof (Hpair x y Hx Hy).
      pose proof (integer_mul_bits x y). lia. }
    assert (Hbits1 : Z.size_nat (la * lb) <= s) by (apply Hprod; auto).
    assert (Hbits2 : Z.size_nat (la * hb) <= s) by (apply Hprod; auto).
    assert (Hbits3 : Z.size_nat (ha * lb) <= s) by (apply Hprod; auto).
    pose proof (integer_extrema_time (la * lb) (la * hb) s Hbits1) as [Hmin1 Hmax1].
    pose proof (integer_extrema_time (ha * lb) (ha * hb) s Hbits3) as [Hmin2 Hmax2].
    assert (Hminbits : Z.size_nat (Z.min (la * lb) (la * hb)) <= s)
      by (pose proof (integer_min_bits (la * lb) (la * hb)); lia).
    assert (Hmaxbits : Z.size_nat (Z.max (la * lb) (la * hb)) <= s)
      by (pose proof (integer_max_bits (la * lb) (la * hb)); lia).
    pose proof (proj1 (integer_extrema_time _ (Z.min (ha * lb) (ha * hb)) s Hminbits))
      as Hmin3.
    pose proof (proj2 (integer_extrema_time _ (Z.max (ha * lb) (ha * hb)) s Hmaxbits))
      as Hmax3.
    replace (binary_work (I (Fin la) (Fin ha)) (I (Fin lb) (Fin hb)))
      with (s * s) by (unfold binary_work, s, size; cbn [Nat.pow]; lia).
    assert (Hs : (1 <= N.of_nat s)%N) by (unfold s; lia).
    clear Hpair Hprod Hbits1 Hbits2 Hbits3 Hminbits Hmaxbits.
    rewrite Nat2N.inj_mul in *. nia.
  Qed.

  (** Absolute value preserves the bit size of an integer. *)
  Lemma integer_abs_bits : forall z, Z.size_nat (Z.abs z) = Z.size_nat z.
  Proof.
    intros []; reflexivity.
  Qed.

  (** Integer division cannot increase the absolute value of its numerator. *)
  Lemma integer_div_abs : forall x y, (Z.abs (x / y) <= Z.abs x)%Z.
  Proof.
    intros x y. destruct (Z.eq_dec y 0) as [-> | Hnonzero].
    - rewrite Z.div_0_r. cbn [Z.abs]. apply Z.abs_nonneg.
    - pose proof (Z.div_mod x y Hnonzero) as Hdiv.
      destruct (Z_lt_ge_dec 0 y) as [Hpositive | Hnegative].
      + pose proof (Z.mod_pos_bound x y Hpositive) as Hmod.
        destruct (Z_le_gt_dec 0 x), (Z_le_gt_dec 0 (x / y));
          rewrite ?Z.abs_eq, ?Z.abs_neq by lia; nia.
      + assert (Hnegative' : (y < 0)%Z) by lia.
        pose proof (Z.mod_neg_bound x y Hnegative') as Hmod.
        destruct (Z_le_gt_dec 0 x), (Z_le_gt_dec 0 (x / y));
          rewrite ?Z.abs_eq, ?Z.abs_neq by lia; nia.
  Qed.

  (** Integer division does not add numerator bits. *)
  Lemma integer_div_bits : forall x y, Z.size_nat (x / y) <= Z.size_nat x.
  Proof.
    intros x y. rewrite <- (integer_abs_bits (x / y)), <- (integer_abs_bits x).
    apply Std.Z.size_nat_mono. split; [apply Z.abs_nonneg | apply integer_div_abs].
  Qed.

  (** Division is quadratic in a common operand bit bound. *)
  Lemma integer_div_time : forall x y k,
    Z.size_nat x + Z.size_nat y + 1 <= k ->
    (Std.Z.T_div x y <= 33 * N.of_nat (k * k))%N.
  Proof.
    intros x y k Hbits. pose proof (Std.Z.T_div_le x y).
    rewrite Nat2N.inj_mul. nia.
  Qed.


  (** Unsigned interval division keeps the numerator endpoint bit bound. *)
  Lemma udiv_result_bits : forall a b, size (udiv a b) <= size a.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      cbn [udiv top size itv_bits bnd_bits]; try lia.
    destruct ((0 <=? la)%Z && (0 <? lb)%Z); cbn [top size itv_bits bnd_bits Z.size_nat]; try lia.
    pose proof (integer_div_bits la hb). pose proof (integer_div_bits ha lb). lia.
  Qed.

  (** The remainder cap uses only an input endpoint and one subtraction. *)
  Lemma urem_result_bits : forall a b, size (urem a b) <= size a + size b + 2.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      cbn [urem top size itv_bits bnd_bits]; try lia.
    destruct ((0 <=? la)%Z && (0 <? lb)%Z); cbn [top size itv_bits bnd_bits Z.size_nat]; try lia.
    pose proof (integer_sub_bits hb 1). cbn [Z.size_nat Pos.size_nat] in *.
    pose proof (integer_min_bits ha (hb - 1)). lia.
  Qed.

  (** Bitwise conjunction's cap is selected from an input endpoint. *)
  Lemma bitand_result_bits : forall a b, size (bitand a b) <= size a + size b.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      cbn [bitand top size itv_bits bnd_bits]; try lia.
    destruct ((0 <=? la)%Z && (0 <=? lb)%Z); cbn [top size itv_bits bnd_bits Z.size_nat]; try lia.
    pose proof (integer_min_bits ha hb). lia.
  Qed.

  (** Two integer divisions and their guards have a quadratic interval cost. *)
  Lemma udiv_time_quadratic : forall a b,
    (T_udiv a b <= 128 * N.of_nat (binary_work a b))%N.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      time_unfold T_udiv; try (unfold binary_work; cbn [Nat.pow]; nia).
    set (s := (size (I (Fin la) (Fin ha)) + size (I (Fin lb) (Fin hb)) + 1)%nat).
    assert (Hfirst : Z.size_nat la + Z.size_nat hb + 1 <= s)
      by (unfold s, size, itv_bits, bnd_bits; lia).
    assert (Hsecond : Z.size_nat ha + Z.size_nat lb + 1 <= s)
      by (unfold s, size, itv_bits, bnd_bits; lia).
    pose proof (integer_div_time la hb s Hfirst).
    pose proof (integer_div_time ha lb s Hsecond).
    pose proof (Std.Z.T_leb_le 0 la). pose proof (Std.Z.T_ltb_le 0 lb).
    time_unfold Datatypes.T_andb.
    destruct ((0 <=? la)%Z && (0 <? lb)%Z);
      replace (binary_work (I (Fin la) (Fin ha)) (I (Fin lb) (Fin hb)))
        with (s * s) by (unfold binary_work, s, size; cbn [Nat.pow]; lia);
      cbn [Z.size_nat] in *; rewrite Nat2N.inj_mul; nia.
  Qed.

  (** Computing a remainder cap is linear and therefore within the quadratic work. *)
  Lemma urem_time_quadratic : forall a b,
    (T_urem a b <= 32 * N.of_nat (binary_work a b))%N.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      time_unfold T_urem; try (unfold binary_work; cbn [Nat.pow]; nia).
    pose proof (Std.Z.T_leb_le 0 la). pose proof (Std.Z.T_ltb_le 0 lb).
    pose proof (Std.Z.T_sub_le hb 1). pose proof (Std.Z.T_min_le ha (hb - 1)).
    time_unfold Datatypes.T_andb.
    destruct ((0 <=? la)%Z && (0 <? lb)%Z);
      unfold binary_work, itv_bits, bnd_bits;
      cbn [Z.size_nat Pos.size_nat Nat.pow] in *; nia.
  Qed.

  (** Computing a bitwise cap fits the published quadratic work. *)
  Lemma bitand_time_quadratic : forall a b,
    (T_bitand a b <= 16 * N.of_nat (binary_work a b))%N.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      time_unfold T_bitand; try (unfold binary_work; cbn [Nat.pow]; nia).
    pose proof (Std.Z.T_leb_le 0 la). pose proof (Std.Z.T_leb_le 0 lb).
    pose proof (Std.Z.T_min_le ha hb). time_unfold Datatypes.T_andb.
    destruct ((0 <=? la)%Z && (0 <=? lb)%Z);
      unfold binary_work, itv_bits, bnd_bits; cbn [Z.size_nat Nat.pow] in *; nia.
  Qed.

  (** Constructing an abstract Boolean uses two constant-time wrappers. *)
  Lemma truth_time_constant : forall b, (T_truth b <= 2)%N.
  Proof.
    intros []; unfold T_truth, T_abst; lia.
  Qed.

  (** An abstract comparison stores at most one result bit. *)
  Lemma cmp_result_bits : forall c a b, size (cmp c a b) <= 1.
  Proof.
    intros c [|la ha] [|lb hb]; cbn [cmp size itv_bits]; try lia.
    destruct (point (I la ha)) as [x |], (point (I lb hb)) as [y |];
      cbn [size itv_bits bnd_bits Z.size_nat Pos.size_nat]; try lia.
    destruct (Z.compare x y), c; cbn [truth abst size itv_bits bnd_bits Z.size_nat
      Pos.size_nat]; lia.
  Qed.

  (** Comparing intervals has a linear endpoint cost. *)
  Lemma cmp_time_linear : forall c a b,
    (T_cmp c a b <= 256 * (T.c_thresholds + 1) *
      N.of_nat (size a + size b + 1))%N.
  Proof.
    intros c a b. pose proof (point_time_linear a) as Ha.
    pose proof (point_time_linear b) as Hb.
    destruct a as [|la ha], b as [|lb hb]; time_unfold T_cmp; try nia.
    destruct (point (I la ha)) as [x |] eqn:Hx; try nia.
    destruct (point (I lb hb)) as [y |] eqn:Hy; try nia.
    pose proof (point_result_bits _ _ Hx).
    pose proof (Std.Z.T_compare_le x y).
    pose proof (truth_time_constant
      (match Z.compare x y, c with Eq, Eq | Lt, Lt | Gt, Gt => true | _, _ => false end)).
    nia.
  Qed.

  (** Meeting selects existing endpoints or returns bottom. *)
  Lemma meet_result_bits : forall a b, size (meet a b) <= size a + size b.
  Proof.
    intros a b. exact (ScalarTime.interval_meet_bits a b).
  Qed.

  (** Backward addition costs linearly in its result and both arguments. *)
  Lemma add_back_time_linear : forall r a b,
    (T_add_back r a b <= 512 * (T.c_thresholds + 1) *
      N.of_nat (size r + size a + size b + 1))%N.
  Proof.
    intros r a b. pose proof (sub_time_linear r b).
    pose proof (sub_time_linear r a).
    pose proof (meet_time_linear a (sub r b)).
    pose proof (meet_time_linear b (sub r a)).
    pose proof (sub_result_bits r b). pose proof (sub_result_bits r a).
    unfold T_add_back. nia.
  Qed.

  (** Backward subtraction costs linearly in its result and both arguments. *)
  Lemma sub_back_time_linear : forall r a b,
    (T_sub_back r a b <= 512 * (T.c_thresholds + 1) *
      N.of_nat (size r + size a + size b + 1))%N.
  Proof.
    intros r a b. pose proof (add_time_linear r b).
    pose proof (sub_time_linear a r).
    pose proof (meet_time_linear a (add r b)).
    pose proof (meet_time_linear b (sub a r)).
    pose proof (add_result_bits r b). pose proof (sub_result_bits a r).
    unfold T_sub_back. nia.
  Qed.

  (** Backward addition stores at most two copies of its linear input budget. *)
  Lemma add_back_result_bits : forall r a b,
    size (fst (add_back r a b)) + size (snd (add_back r a b)) <=
      2 * (size r + size a + size b + 1).
  Proof.
    intros r a b. pose proof (meet_result_bits a (sub r b)).
    pose proof (meet_result_bits b (sub r a)).
    pose proof (sub_result_bits r b). pose proof (sub_result_bits r a).
    unfold add_back. cbn [fst snd]. lia.
  Qed.

  (** Backward subtraction stores at most two copies of its linear input budget. *)
  Lemma sub_back_result_bits : forall r a b,
    size (fst (sub_back r a b)) + size (snd (sub_back r a b)) <=
      2 * (size r + size a + size b + 1).
  Proof.
    intros r a b. pose proof (meet_result_bits a (add r b)).
    pose proof (meet_result_bits b (sub a r)).
    pose proof (add_result_bits r b). pose proof (sub_result_bits a r).
    unfold sub_back. cbn [fst snd]. lia.
  Qed.

  (** A multiplication preimage is the request, its negation, or top. *)
  Lemma mul_preimage_result_bits : forall r x,
    size (mul_preimage r x) <= size r + 1.
  Proof.
    intros r x. unfold mul_preimage. destruct (point x) as [z |];
      [|cbn [top size itv_bits bnd_bits]; lia].
    destruct (Z.eqb z 1); [lia |]. destruct (Z.eqb z (-1));
      [|cbn [top size itv_bits bnd_bits]; lia].
    pose proof (sub_result_bits (abst 0) r). rewrite abst_result_bits in *.
    cbn [Z.size_nat] in *. lia.
  Qed.

  (** Recognizing a unit multiplication preimage has a linear input cost. *)
  Lemma mul_preimage_time_linear : forall r x,
    (T_mul_preimage r x <= 256 * (T.c_thresholds + 1) *
      N.of_nat (size r + size x + 1))%N.
  Proof.
    intros r x. pose proof (point_time_linear x) as Hpoint.
    pose proof (sub_time_linear (abst 0) r) as Hsub.
    rewrite abst_result_bits in Hsub. cbn [Z.size_nat] in Hsub.
    time_unfold T_mul_preimage. destruct (point x) as [z |] eqn:Hx; try nia.
    pose proof (point_result_bits _ _ Hx).
    pose proof (Std.Z.T_eqb_le z 1). pose proof (Std.Z.T_eqb_le z (-1)).
    destruct (Z.eqb z 1), (Z.eqb z (-1)); unfold T_abst; nia.
  Qed.

  (** Backward multiplication costs linearly in its result and both arguments. *)
  Lemma mul_back_time_linear : forall r a b,
    (T_mul_back r a b <= 2048 * (T.c_thresholds + 1) *
      N.of_nat (size r + size a + size b + 1))%N.
  Proof.
    intros r a b. pose proof (mul_preimage_time_linear r a).
    pose proof (mul_preimage_time_linear r b).
    pose proof (mul_preimage_result_bits r a).
    pose proof (mul_preimage_result_bits r b).
    pose proof (meet_time_linear a (mul_preimage r b)).
    pose proof (meet_time_linear b (mul_preimage r a)).
    unfold T_mul_back. nia.
  Qed.

  (** Backward multiplication stores at most two linear input budgets. *)
  Lemma mul_back_result_bits : forall r a b,
    size (fst (mul_back r a b)) + size (snd (mul_back r a b)) <=
      2 * (size r + size a + size b + 1).
  Proof.
    intros r a b. pose proof (mul_preimage_result_bits r a).
    pose proof (mul_preimage_result_bits r b).
    pose proof (meet_result_bits a (mul_preimage r b)).
    pose proof (meet_result_bits b (mul_preimage r a)).
    unfold mul_back. cbn [fst snd]. lia.
  Qed.


  (** A finite upper cut stores precisely its endpoint bits. *)
  Lemma upper_cut_bits : forall b, size (I NegInf b) = bnd_bits b.
  Proof.
    reflexivity.
  Qed.

  (** A finite lower cut stores precisely its endpoint bits. *)
  Lemma lower_cut_bits : forall b, size (I b PosInf) = bnd_bits b.
  Proof.
    intro b. unfold size, itv_bits. cbn [bnd_bits]. apply Nat.max_0_r.
  Qed.

  (** The unsigned precondition clamps each operand with a constant-sized interval. *)
  Lemma unsigned_back_time_linear : forall a b,
    (T_unsigned_back a b <= 256 * (T.c_thresholds + 1) *
      N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (meet_time_linear a (I (Fin 0) PosInf)).
    pose proof (meet_time_linear b (I (Fin 1) PosInf)).
    cbn [size itv_bits bnd_bits Z.size_nat Pos.size_nat] in *.
    unfold T_unsigned_back. nia.
  Qed.

  (** Unsigned precondition clamps add at most one stored endpoint bit. *)
  Lemma unsigned_back_result_bits : forall a b,
    size (fst (unsigned_back a b)) + size (snd (unsigned_back a b)) <=
      size a + size b + 1.
  Proof.
    intros a b. pose proof (meet_result_bits a (I (Fin 0) PosInf)).
    pose proof (meet_result_bits b (I (Fin 1) PosInf)).
    cbn [size itv_bits bnd_bits Z.size_nat Pos.size_nat] in *.
    unfold unsigned_back. cbn [fst snd]. lia.
  Qed.

  (** Decrementing a finite strict upper endpoint adds at most two bits. *)
  Lemma strict_upper_bits : forall b,
    bnd_bits (match b with Fin z => Fin (z - 1) | _ => b end) <= bnd_bits b + 2.
  Proof.
    intros [|z|]; cbn [bnd_bits]; try lia.
    pose proof (integer_sub_bits z 1). cbn [Z.size_nat Pos.size_nat] in *. lia.
  Qed.

  (** Incrementing a finite strict lower endpoint adds at most two bits. *)
  Lemma strict_lower_bits : forall b,
    bnd_bits (match b with Fin z => Fin (z + 1) | _ => b end) <= bnd_bits b + 2.
  Proof.
    intros [|z|]; cbn [bnd_bits]; try lia.
    pose proof (integer_add_bits z 1). cbn [Z.size_nat Pos.size_nat] in *. lia.
  Qed.

  (** A strict upper endpoint requires at most one linear subtraction. *)
  Lemma strict_upper_time : forall b,
    ((match b with Fin z => Std.Z.T_sub z 1 | _ => 0 end) <=
      3 * N.of_nat (bnd_bits b) + 6)%N.
  Proof.
    intros [|z|]; cbn [bnd_bits]; try nia.
    pose proof (Std.Z.T_sub_le z 1). cbn [Z.size_nat Pos.size_nat] in *. nia.
  Qed.

  (** A strict lower endpoint requires at most one linear addition. *)
  Lemma strict_lower_time : forall b,
    ((match b with Fin z => Std.Z.T_add z 1 | _ => 0 end) <=
      3 * N.of_nat (bnd_bits b) + 4)%N.
  Proof.
    intros [|z|]; cbn [bnd_bits]; try nia.
    pose proof (Std.Z.T_add_le z 1). cbn [Z.size_nat Pos.size_nat] in *. nia.
  Qed.

  (** Strict refinement costs linearly in both operands. *)
  Lemma strict_back_time_linear : forall a b,
    (T_strict_back a b <= 1024 * (T.c_thresholds + 1) *
      N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|la ha] [|lb hb]; time_unfold T_strict_back; try nia.
    pose proof (endpoint_sizes la ha) as [Hla Hha].
    pose proof (endpoint_sizes lb hb) as [Hlb Hhb].
    pose proof (strict_upper_time hb). pose proof (strict_lower_time la).
    pose proof (strict_upper_bits hb). pose proof (strict_lower_bits la).
    pose proof (meet_time_linear (I la ha)
      (I NegInf (match hb with Fin z => Fin (z - 1) | _ => hb end))).
    pose proof (meet_time_linear (I lb hb)
      (I (match la with Fin z => Fin (z + 1) | _ => la end) PosInf)).
    rewrite upper_cut_bits, lower_cut_bits in *.
    nia.
  Qed.

  (** Strict refinement stores only operand endpoints and unit adjustments. *)
  Lemma strict_back_result_bits : forall a b,
    size (fst (strict_back a b)) + size (snd (strict_back a b)) <=
      2 * (size a + size b + 2).
  Proof.
    intros [|la ha] [|lb hb]; cbn [strict_back fst snd];
      try (cbn [size itv_bits]; lia).
    pose proof (strict_upper_bits hb). pose proof (strict_lower_bits la).
    pose proof (meet_result_bits (I la ha)
      (I NegInf (match hb with Fin z => Fin (z - 1) | _ => hb end))).
    pose proof (meet_result_bits (I lb hb)
      (I (match la with Fin z => Fin (z + 1) | _ => la end) PosInf)).
    rewrite upper_cut_bits, lower_cut_bits in *.
    pose proof (endpoint_sizes la ha). pose proof (endpoint_sizes lb hb). lia.
  Qed.

  (** Unsigned comparison refinement has a linear result-and-operand cost. *)
  Lemma ult_back_time_linear : forall r a b,
    (T_ult_back r a b <= 2048 * (T.c_thresholds + 1) *
      N.of_nat (size r + size a + size b + 1))%N.
  Proof.
    intros r a b. pose proof (point_time_linear r) as Hpoint.
    time_unfold T_ult_back. destruct (point r) as [z |] eqn:Hr.
    - pose proof (point_result_bits _ _ Hr) as Hbits.
      pose proof (Std.Z.T_eqb_le z 1) as Heq.
      pose proof (strict_back_time_linear a b) as Hstrict.
      assert (Hcombined : (T_point r + Std.Z.T_eqb z 1 + T_strict_back a b + 2 <=
        2048 * (T.c_thresholds + 1) *
          N.of_nat (size r + size a + size b + 1))%N) by nia.
      destruct a as [|[|la|] ha], b as [|lb [|hb|]]; try lia.
      destruct (Z.eqb z 1); [unfold T_strict_back in Hcombined; lia | lia].
    - nia.
  Qed.


  (** Unsigned comparison refinement stores only strict operand cuts. *)
  Lemma ult_back_result_bits : forall r a b,
    size (fst (ult_back r a b)) + size (snd (ult_back r a b)) <=
      2 * (size a + size b + 2).
  Proof.
    intros r a b. pose proof (strict_back_result_bits a b) as Hstrict.
    unfold ult_back. destruct (point r) as [z |];
      [|cbn [fst snd]; lia].
    destruct a as [|[|la|] ha], b as [|lb [|hb|]]; cbn [fst snd]; try lia.
    destruct (Z.eqb z 1); cbn [fst snd]; [exact Hstrict | lia].
  Qed.

  (** A positive integer's bit count is bounded by its value. *)
  Lemma shift_positive_bits_value : forall p, Pos.size_nat p <= Pos.to_nat p.
  Proof.
    induction p as [p IH|p IH|]; cbn [Pos.size_nat];
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
  Qed.

  (** The positive and natural bit-count representations agree. *)
  Lemma shift_positive_size_value : forall p, Pos.to_nat (Pos.size p) = Pos.size_nat p.
  Proof.
    induction p as [p IH|p IH|]; cbn [Pos.size Pos.size_nat];
      rewrite ?Pos2Nat.inj_succ, ?IH; reflexivity.
  Qed.

  (** Nonnegative integer bit counts are bounded by their natural values. *)
  Lemma shift_nonnegative_bits : forall z, (0 <= z)%Z -> Z.size_nat z <= Z.to_nat z.
  Proof.
    intros [|p|p] Hz; cbn [Z.size_nat Z.to_nat]; try lia.
    apply shift_positive_bits_value.
  Qed.

  (** Converting a natural does not create more bits than its value. *)
  Lemma shift_of_nat_bits : forall n, Z.size_nat (Z.of_nat n) <= n.
  Proof.
    intro n. pose proof (shift_nonnegative_bits (Z.of_nat n) (Nat2Z.is_nonneg n)) as Hbits.
    now rewrite Nat2Z.id in Hbits.
  Qed.

  (** A nonnegative integer below a power of two fits within its exponent. *)
  Lemma shift_bits_below_pow : forall z n,
    (0 <= z < 2 ^ Z.of_nat n)%Z -> Z.size_nat z <= n.
  Proof.
    intros [|z|z] n Hrange; cbn [Z.size_nat]; try lia.
    now apply Zpower2_Psize.
  Qed.

  (** A power of two uses its exponent plus one bit. *)
  Lemma shift_pow2_bits : forall n, (0 <= n)%Z ->
    Z.size_nat (2 ^ n) <= Z.to_nat n + 1.
  Proof.
    intros n Hn. apply shift_bits_below_pow. split.
    - pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as Hpositive; lia.
    - rewrite Nat2Z.inj_add, Z2Nat.id by exact Hn.
      apply Z.pow_lt_mono_r; lia.
  Qed.

  (** A nonnegative all-ones mask fits within its requested width. *)
  Lemma shift_ones_bits : forall n, (0 <= n)%Z -> Z.size_nat (Z.ones n) <= Z.to_nat n.
  Proof.
    intros n Hn. apply shift_bits_below_pow. rewrite Z2Nat.id by exact Hn.
    rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as Hpositive.
    lia.
  Qed.

  (** A nonnegative shift adds at most the shift amount and one bit. *)
  Lemma shift_left_bits : forall x n, (0 <= n)%Z ->
    Z.size_nat (Z.shiftl x n) <= Z.size_nat x + Z.to_nat n + 1.
  Proof.
    intros x n Hn. rewrite Z.shiftl_mul_pow2 by exact Hn.
    pose proof (integer_mul_bits x (2 ^ n)) as Hproduct.
    pose proof (shift_pow2_bits n Hn) as Hpower. lia.
  Qed.

  (** The integer logarithm is bounded by the input's bit count, including negative inputs. *)
  Lemma shift_log2_value : forall z,
    (0 <= Z.log2 z <= Z.of_nat (Z.size_nat z))%Z.
  Proof.
    intros [|[p|p|]|p]; cbn [Z.log2 Z.size_nat Pos.size_nat]; try lia.
    all: rewrite <- (positive_nat_Z (Pos.size p)), shift_positive_size_value; lia.
  Qed.

  (** The logarithm's own bit count also fits the input bit count. *)
  Lemma shift_log2_bits : forall z, Z.size_nat (Z.log2 z) <= Z.size_nat z.
  Proof.
    intro z. pose proof (shift_log2_value z) as [Hnonnegative Hupper].
    pose proof (shift_nonnegative_bits (Z.log2 z) Hnonnegative) as Hbits.
    pose proof (Z2Nat.id (Z.log2 z) Hnonnegative) as Hvalue. lia.
  Qed.

  (** Absolute-value conversion agrees with natural conversion on nonnegative integers. *)
  Lemma shift_abs_N_nat : forall z, (0 <= z)%Z ->
    Z.abs_N z = N.of_nat (Z.to_nat z).
  Proof.
    intros [|p|p] Hz; cbn [Z.abs_N Z.to_nat]; try reflexivity; try lia.
  Qed.

  (** Computing a positive bit count is bounded by the square of the input bit count. *)
  Lemma shift_positive_size_time : forall p,
    (Fun.Pos.T_size p <= N.of_nat ((Pos.size_nat p + 1) ^ 2))%N.
  Proof.
    induction p as [p IH|p IH|]; unfold Fun.Pos.T_size; fold Fun.Pos.T_size;
      cbn beta iota zeta.
    all: try pose proof (Std.Pos.T_succ_le (Pos.size p)) as Hsucc.
    all: try pose proof (shift_positive_bits_value (Pos.size p)) as Hbits.
    all: try rewrite shift_positive_size_value in Hbits.
    all: cbn [Pos.size_nat] in *; rewrite !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add in *;
      nia.
  Qed.

  (** Computing an integer logarithm has a quadratic bit-count bound. *)
  Lemma shift_log2_time : forall z,
    (Fun.Z.T_log2 z <= 2 * N.of_nat ((Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros [|[p|p|]|p]; unfold Fun.Z.T_log2; cbn beta iota zeta;
      try pose proof (shift_positive_size_time p) as Hsize;
      cbn [Z.size_nat Pos.size_nat] in *;
      rewrite !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add in *; nia.
  Qed.

  (** Constructing a positive from a natural has a quadratic value bound. *)
  Lemma shift_of_succ_nat_time : forall n,
    (Op.Pos.T_of_succ_nat n <= N.of_nat ((n + 1) ^ 2))%N.
  Proof.
    induction n as [|n IH]; unfold Op.Pos.T_of_succ_nat; fold Op.Pos.T_of_succ_nat;
      cbn beta iota zeta.
    - reflexivity.
    - pose proof (Std.Pos.T_succ_le (Pos.of_succ_nat n)) as Hsucc.
      pose proof (shift_positive_bits_value (Pos.of_succ_nat n)) as Hbits.
      rewrite SuccNat2Pos.id_succ in Hbits.
      rewrite !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
  Qed.

  (** The integer conversion has the same quadratic value budget. *)
  Lemma shift_of_nat_time : forall n,
    (Op.Z.T_of_nat n <= 2 * N.of_nat ((n + 1) ^ 2))%N.
  Proof.
    intros [|n]; unfold Op.Z.T_of_nat; cbn beta iota zeta;
      [change (1 <= 2)%N; lia|].
    pose proof (shift_of_succ_nat_time n) as Hpositive.
    rewrite !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
  Qed.

  (** Reading an integer's bit count traverses its binary representation. *)
  Lemma shift_integer_size_time : forall z,
    (Word.Z.T_size_nat z <= N.of_nat (Z.size_nat z) + 1)%N.
  Proof.
    intros [|p|p]; unfold Word.Z.T_size_nat; cbn beta iota zeta;
      cbn [Z.size_nat]; try lia; pose proof (Std.Pos.T_size_nat_le p) as Hsize; lia.
  Qed.

  (** Comparing unary bit counts takes at most the first count plus one step. *)
  Lemma shift_nat_max_time : forall n m,
    (Nat.T_max n m <= N.of_nat n + 1)%N.
  Proof.
    induction n as [|n IH]; intros [|m]; unfold Nat.T_max; fold Nat.T_max;
      cbn beta iota zeta; try lia.
    pose proof (IH m) as Htail. rewrite Nat2N.inj_succ. lia.
  Qed.

  (** Endpoint size inspection adds one constructor branch. *)
  Lemma shift_bound_size_time : forall b,
    (T_code_bnd_bits b <= N.of_nat (bnd_bits b) + 2)%N.
  Proof.
    intros [|z|]; unfold T_code_bnd_bits; cbn beta iota zeta; cbn [bnd_bits]; try lia.
    pose proof (shift_integer_size_time z) as Hbits. lia.
  Qed.

  (** Computing the interval bit count is linear in the maximum endpoint bit count. *)
  Lemma shift_interval_size_time : forall a,
    (T_code_itv_bits a <= 8 * N.of_nat (size a + 1))%N.
  Proof.
    intros [|lo hi]; unfold T_code_itv_bits; cbn beta iota zeta; try nia.
    pose proof (shift_bound_size_time lo) as Hlo.
    pose proof (shift_bound_size_time hi) as Hhi.
    pose proof (shift_nat_max_time (code_bnd_bits lo) (code_bnd_bits hi)) as Hmax.
    pose proof (endpoint_sizes lo hi) as [Hlobits Hhibits].
    change (Nat.T_max (code_bnd_bits lo) (code_bnd_bits hi) <=
      N.of_nat (bnd_bits lo) + 1)%N in Hmax.
    rewrite Nat2N.inj_add. nia.
  Qed.

  (** Forming an all-ones mask has a linear bound in its nonnegative width. *)
  Lemma shift_ones_time : forall n, (0 <= n)%Z ->
    (Word.Z.T_ones n <= 16 * N.of_nat (Z.to_nat n + 1))%N.
  Proof.
    intros n Hn. pose proof (Std.Z.T_shiftl_le 1 n) as Hshift.
    pose proof (Std.Z.T_pred_le (Z.shiftl 1 n)) as Hpred.
    pose proof (shift_pow2_bits n Hn) as Hbits. rewrite <- Z.shiftl_1_l in Hbits.
    change (Std.Z.T_shiftl 1 n <= 6 * Z.abs_N n + 1)%N in Hshift.
    rewrite shift_abs_N_nat in Hshift by exact Hn.
    unfold Word.Z.T_ones. rewrite Nat2N.inj_add. nia.
  Qed.
  (** Integer disjunction stores no more than the operand bit bounds and one mask bit. *)
  Lemma bitor_result_bits : forall a b, size (bitor a b) <= size a + size b + 1.
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      cbn [bitor size itv_bits bnd_bits top]; try lia.
    destruct ((0 <=? la)%Z && (0 <=? lb)%Z); cbn [size itv_bits bnd_bits top]; try lia.
    pose proof (integer_max_bits ha hb) as Hmax.
    pose proof (shift_log2_value (Z.max ha hb)) as [Hlog0 Hlog].
    pose proof (shift_ones_bits (Z.log2 (Z.max ha hb) + 1) ltac:(lia)) as Hones.
    pose proof (Z2Nat.id (Z.log2 (Z.max ha hb) + 1) ltac:(lia)) as Hwidth.
    change (Z.size_nat 0) with 0. cbn [Nat.max]. lia.
  Qed.

  (** Disjunction pays for endpoint comparison, logarithm and mask construction. *)
  Lemma bitor_time_quadratic : forall a b,
    (T_bitor a b <= 8192 * N.of_nat (binary_work a b))%N.
  Proof.
    assert (Hsmall : forall n, (1 <= 8192 * N.of_nat ((n + 1) ^ 2))%N).
    { intro n. rewrite Nat.pow_2_r, Nat2N.inj_mul, Nat2N.inj_add. nia. }
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      unfold T_bitor, binary_work; fold size; cbn beta iota zeta; try apply Hsmall.
    set (s := size (I (Fin la) (Fin ha)) + size (I (Fin lb) (Fin hb)) + 1).
    set (budget := N.of_nat (s ^ 2)).
    assert (Hs : 1 <= s) by (unfold s; lia).
    assert (Hbudget : (1 <= budget /\ N.of_nat s <= budget)%N).
    { unfold budget. rewrite Nat.pow_2_r, Nat2N.inj_mul. nia. }
    pose proof (endpoint_sizes (Fin la) (Fin ha)) as [Hla Hha].
    pose proof (endpoint_sizes (Fin lb) (Fin hb)) as [Hlb Hhb].
    cbn [bnd_bits] in Hla, Hha, Hlb, Hhb.
    set (h := Z.max ha hb).
    assert (Hh : Z.size_nat h + 1 <= s).
    { pose proof (integer_max_bits ha hb) as Hmax. unfold h, s; lia. }
    assert (Hmax : (Std.Z.T_max ha hb <= 5 * budget)%N).
    { pose proof (Std.Z.T_max_le ha hb) as Htime. unfold s in Hh.
      assert (Hbits : Z.size_nat ha + 1 <= s) by (unfold s; lia). lia. }
    assert (Hlog : (Fun.Z.T_log2 h <= 2 * budget)%N).
    { eapply N.le_trans; [apply shift_log2_time|]. unfold budget.
      apply N.mul_le_mono_l. rewrite !Nat.pow_2_r, !Nat2N.inj_mul.
      apply N.mul_le_mono; lia. }
    pose proof (shift_log2_value h) as [Hlog0 Hlogvalue].
    assert (Hadd : (Std.Z.T_add (Z.log2 h) 1 <= 4 * budget)%N).
    { pose proof (Std.Z.T_add_le (Z.log2 h) 1) as Htime.
      pose proof (shift_log2_bits h) as Hbits.
      change (Std.Z.T_add (Z.log2 h) 1 <=
        3 * N.of_nat (Z.size_nat (Z.log2 h) + 1) + 1)%N in Htime.
      rewrite Nat2N.inj_add in Htime. lia. }
    assert (Hones : (Word.Z.T_ones (Z.log2 h + 1) <= 32 * budget)%N).
    { pose proof (shift_ones_time (Z.log2 h + 1) ltac:(lia)) as Htime.
      pose proof (Z2Nat.id (Z.log2 h + 1) ltac:(lia)) as Hvalue.
      rewrite Nat2N.inj_add in Htime. lia. }
    pose proof (Std.Z.T_leb_le 0 la) as Htesta.
    pose proof (Std.Z.T_leb_le 0 lb) as Htestb.
    pose proof (Std.Datatypes.T_andb_le (0 <=? la)%Z (0 <=? lb)%Z) as Hand.
    change (Std.Z.T_leb 0 la <= 4)%N in Htesta.
    change (Std.Z.T_leb 0 lb <= 4)%N in Htestb.
    fold h s budget. destruct ((0 <=? la)%Z && (0 <=? lb)%Z); lia.
  Qed.
  (** Computing the dynamic cutoff fits the quadratic operand bit budget. *)
  Lemma shift_preparation_time : forall a b,
    (T_code_itv_bits a + T_code_itv_bits b +
      Std.Nat.T_add (code_itv_bits a) (code_itv_bits b) +
      Std.Nat.T_add (code_itv_bits a + code_itv_bits b) 1 +
      Op.Z.T_of_nat (code_itv_bits a + code_itv_bits b + 1) <=
      128 * N.of_nat (binary_work a b))%N.
  Proof.
    intros a b. pose proof (shift_interval_size_time a) as Ha.
    pose proof (shift_interval_size_time b) as Hb.
    pose proof (Std.Nat.T_add_le (code_itv_bits a) (code_itv_bits b)) as Hsum.
    pose proof (Std.Nat.T_add_le (code_itv_bits a + code_itv_bits b) 1) as Hsucc.
    pose proof (shift_of_nat_time (code_itv_bits a + code_itv_bits b + 1)) as Hconvert.
    change (code_itv_bits a) with (size a) in *.
    change (code_itv_bits b) with (size b) in *.
    unfold binary_work. fold size.
    rewrite !Nat.pow_2_r, !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  Qed.

  (** Shifting by a bounded nonnegative count fits a quadratic bit budget. *)
  Lemma shift_left_time : forall x n k,
    1 <= k -> Z.size_nat x <= k -> (0 <= n <= Z.of_nat k)%Z ->
    (Std.Z.T_shiftl x n <= 16 * N.of_nat (k ^ 2))%N.
  Proof.
    intros x n k Hk Hbits [Hn Hnk].
    pose proof (Std.Z.T_shiftl_le x n) as Htime.
    rewrite shift_abs_N_nat in Htime by exact Hn.
    pose proof (Z2Nat.id n Hn) as Hcount.
    assert (Hproduct :
      ((N.of_nat (Z.size_nat x) + 5) * N.of_nat (Z.to_nat n) <=
       (N.of_nat k + 5) * N.of_nat k)%N).
    { apply N.mul_le_mono; lia. }
    rewrite Nat.pow_2_r, Nat2N.inj_mul. nia.
  Qed.

  (** The cutoff keeps every computed shift result within a linear endpoint bit bound. *)
  Lemma shl_result_bits : forall a b, size (shl a b) <= 2 * (size a + size b + 1).
  Proof.
    intros [|[|la|] [|ha|]] [|[|lb|] [|hb|]];
      unfold shl; cbn beta iota zeta; cbn [size itv_bits bnd_bits top]; try lia.
    all: destruct ((0 <=? la)%Z && (0 <=? lb)%Z) eqn:Hnonnegative;
      cbn [size itv_bits bnd_bits top]; try lia.
    apply andb_true_iff in Hnonnegative as [Hla Hlb].
    apply Z.leb_le in Hla, Hlb.
    destruct ((lb <=? hb)%Z &&
      (hb <=? Z.of_nat
        (code_itv_bits (I (Fin la) (Fin ha)) + code_itv_bits (I (Fin lb) (Fin hb)) + 1))%Z)
      eqn:Hcutoff; cbn [size itv_bits bnd_bits]; try lia.
    apply andb_true_iff in Hcutoff as [Hordered Hupper].
    apply Z.leb_le in Hordered, Hupper.
    pose proof (shift_left_bits la lb Hlb) as Hlow.
    pose proof (shift_left_bits ha hb ltac:(lia)) as Hhigh.
    pose proof (Z2Nat.id lb Hlb) as Hlbvalue.
    pose proof (Z2Nat.id hb ltac:(lia)) as Hhbvalue.
    cbn [code_itv_bits code_bnd_bits] in Hupper.
    apply Nat.max_lub; lia.
  Qed.

  (** Shift transfer charges size inspection and only shifts below the checked cutoff. *)
  Lemma shl_time_quadratic : forall a b,
    (T_shl a b <= 8192 * N.of_nat (binary_work a b))%N.
  Proof.
    intros a b. pose proof (shift_preparation_time a b) as Hprepare.
    unfold binary_work in Hprepare |- *. fold size in Hprepare |- *.
    set (s := size a + size b + 1) in *.
    set (budget := N.of_nat (s ^ 2)) in *.
    assert (Hs : 1 <= s) by (unfold s; lia).
    assert (Hbudget : (1 <= budget /\ N.of_nat s <= budget)%N).
    { unfold budget. rewrite Nat.pow_2_r, Nat2N.inj_mul. nia. }
    unfold T_shl.
    change (code_itv_bits a) with (size a) in *.
    change (code_itv_bits b) with (size b) in *.
    fold s in Hprepare |- *.
    destruct a as [|[|la|] ha], b as [|[|lb|] hb]; cbn beta iota zeta; try lia.
    pose proof (Std.Z.T_leb_le 0 la) as Htesta.
    pose proof (Std.Z.T_leb_le 0 lb) as Htestb.
    pose proof (Std.Datatypes.T_andb_le (0 <=? la)%Z (0 <=? lb)%Z) as Hand.
    change (Std.Z.T_leb 0 la <= 4)%N in Htesta.
    change (Std.Z.T_leb 0 lb <= 4)%N in Htestb.
    destruct ((0 <=? la)%Z && (0 <=? lb)%Z) eqn:Hnonnegative; try lia.
    apply andb_true_iff in Hnonnegative as [Hla Hlb].
    apply Z.leb_le in Hla, Hlb.
    destruct ha as [|ha|], hb as [|hb|]; cbn beta iota zeta; try lia.
    pose proof (endpoint_sizes (Fin la) (Fin ha)) as [Hlabits Hhabits].
    pose proof (endpoint_sizes (Fin lb) (Fin hb)) as [Hlbbits Hhbbits].
    cbn [bnd_bits] in Hlabits, Hhabits, Hlbbits, Hhbbits.
    assert (Hla_s : Z.size_nat la <= s) by (unfold s; lia).
    assert (Hha_s : Z.size_nat ha <= s) by (unfold s; lia).
    assert (Hlb_s : Z.size_nat lb <= s) by (unfold s; lia).
    assert (Hhb_s : Z.size_nat hb <= s) by (unfold s; lia).
    pose proof (Std.Z.T_leb_le lb hb) as Hcompare.
    pose proof (Std.Z.T_leb_le hb (Z.of_nat s)) as Hcutoff.
    pose proof (Std.Datatypes.T_andb_le (lb <=? hb)%Z (hb <=? Z.of_nat s)%Z) as Hchecked.
    destruct ((lb <=? hb)%Z && (hb <=? Z.of_nat s)%Z) eqn:Hbounds; try lia.
    apply andb_true_iff in Hbounds as [Hordered Hupper].
    apply Z.leb_le in Hordered, Hupper.
    pose proof (shift_left_time la lb s Hs Hla_s ltac:(lia)) as Hlow.
    pose proof (shift_left_time ha hb s Hs Hha_s ltac:(lia)) as Hhigh.
    fold budget in Hlow, Hhigh. lia.
  Qed.
  (** Repeated multiplication by two has constant cost per produced bit. *)
  Lemma shift_pow2_time : forall z,
    (Word.Z.T_pow 2 z <= 5 * Z.abs_N z + 2)%N.
  Proof.
    intros [|p|p]; unfold Word.Z.T_pow, Word.Z.T_pow_pos;
      cbn beta iota zeta; try nia.
    pose proof (Std.Pos.T_iter_le (Z.mul 2)
      (fun x => Std.Z.T_mul 2 x) (fun _ => True) 3 1%Z p
      ltac:(easy) ltac:(intros; apply Std.Z.T_mul_two_le) ltac:(constructor)) as Hiter.
    change (Z.abs_N (Z.pos p)) with (N.pos p). nia.
  Qed.

  (** Signed split boundaries fit the width plus three bookkeeping bits. *)
  Lemma split_power_bits : forall w,
    Z.size_nat (2 ^ Z.pos w) <= Pos.to_nat w + 1 /\
    Z.size_nat (2 ^ (Z.pos w - 1)) <= Pos.to_nat w + 1 /\
    Z.size_nat (2 ^ Z.pos w - 1) <= Pos.to_nat w + 3 /\
    Z.size_nat (2 ^ (Z.pos w - 1) - 1) <= Pos.to_nat w + 3.
  Proof.
    intro w. pose proof (shift_pow2_bits (Z.pos w) ltac:(lia)) as Hmodulus.
    pose proof (shift_pow2_bits (Z.pos w - 1) ltac:(lia)) as Hhalf.
    pose proof (Z2Nat.id (Z.pos w - 1) ltac:(lia)) as Hhalfwidth.
    pose proof (positive_nat_Z w) as Hwidth.
    change (Z.to_nat (Z.pos w)) with (Pos.to_nat w) in Hmodulus.
    pose proof (integer_sub_bits (2 ^ Z.pos w) 1) as Hmoduluscap.
    pose proof (integer_sub_bits (2 ^ (Z.pos w - 1)) 1) as Hhalfcap.
    change (Z.size_nat 1) with 1 in Hmoduluscap, Hhalfcap. lia.
  Qed.

  (** Both signed split ranges have linear width-sized endpoints. *)
  Lemma split_range_bits : forall w,
    size (I (Fin 0) (Fin (2 ^ (Z.pos w - 1) - 1))) <= Pos.to_nat w + 3 /\
    size (I (Fin (2 ^ (Z.pos w - 1))) (Fin (2 ^ Z.pos w - 1))) <= Pos.to_nat w + 3.
  Proof.
    intro w. pose proof (split_power_bits w) as [Hmodulus [Hhalf [Hmoduluscap Hhalfcap]]].
    unfold size, itv_bits, bnd_bits. change (Z.size_nat 0) with 0. lia.
  Qed.

  (** Preparing the two powers and their predecessor boundaries has a linear width cost. *)
  Lemma split_power_time : forall w,
    (Word.Z.T_pow 2 (Z.pos w) + Std.Z.T_sub (Z.pos w) 1 +
      Word.Z.T_pow 2 (Z.pos w - 1) + Std.Z.T_sub (2 ^ (Z.pos w - 1)) 1 +
      Std.Z.T_sub (2 ^ Z.pos w) 1 <= 64 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    intro w. pose proof (shift_pow2_time (Z.pos w)) as Hmodulus.
    pose proof (shift_pow2_time (Z.pos w - 1)) as Hhalf.
    rewrite !shift_abs_N_nat in Hmodulus, Hhalf by lia.
    change (Z.to_nat (Z.pos w)) with (Pos.to_nat w) in Hmodulus.
    pose proof (Z2Nat.id (Z.pos w - 1) ltac:(lia)) as Hhalfwidth.
    pose proof (positive_nat_Z w) as Hwidth.
    pose proof (shift_positive_bits_value w) as Hwidthbits.
    pose proof (Std.Z.T_sub_le (Z.pos w) 1) as Hdecrement.
    pose proof (Std.Z.T_sub_le (2 ^ (Z.pos w - 1)) 1) as Hhalfcap.
    pose proof (Std.Z.T_sub_le (2 ^ Z.pos w) 1) as Hmoduluscap.
    pose proof (split_power_bits w) as [Hmodulusbits [Hhalfbits _]].
    change (Z.size_nat 1) with 1 in Hdecrement, Hhalfcap, Hmoduluscap.
    change (Z.size_nat (Z.pos w)) with (Pos.size_nat w) in Hdecrement.
    rewrite !Nat2N.inj_add in *. lia.
  Qed.

  (** A scalar meet wrapper retains the tight threshold-independent endpoint bound. *)
  Lemma split_meet_time : forall a b,
    (T_meet a b <= 33 * (T.c_thresholds + 1) * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (ScalarTime.T_interval_meet_le a b) as Htime.
    change (T_interval_meet a b <=
      ScalarTime.c_scalar * N.of_nat (size a + size b + 1))%N in Htime.
    unfold T_meet, ScalarTime.c_scalar in *. rewrite Nat2N.inj_add in *. nia.
  Qed.

  (** The scalar meet only selects endpoints already present in its inputs. *)
  Lemma split_meet_bits : forall a b, size (meet a b) <= size a + size b.
  Proof.
    intros a b. exact (ScalarTime.interval_meet_bits a b).
  Qed.

  (** Meeting a split range fits the common width and operand budget. *)
  Lemma split_meet_width_time : forall w a r, size r <= Pos.to_nat w + 3 ->
    (T_meet a r <=
      132 * ((T.c_thresholds + 1) * N.of_nat (Pos.to_nat w + size a + 1)))%N.
  Proof.
    intros w a r Hr. eapply N.le_trans; [apply split_meet_time|].
    replace (132 * ((T.c_thresholds + 1) * N.of_nat (Pos.to_nat w + size a + 1)))%N
      with ((33 * (T.c_thresholds + 1)) *
        (4 * N.of_nat (Pos.to_nat w + size a + 1)))%N by ring.
    apply N.mul_le_mono_l. rewrite !Nat2N.inj_add. lia.
  Qed.

  (** Translating the high range by the modulus has a linear width and operand cost. *)
  Lemma split_sub_width_time : forall w a r, size r <= Pos.to_nat w + 3 ->
    (T_sub (meet a r) (abst (2 ^ Z.pos w)) <=
      40 * N.of_nat (Pos.to_nat w + size a + 1))%N.
  Proof.
    intros w a r Hr. pose proof (sub_time_linear (meet a r) (abst (2 ^ Z.pos w))) as Htime.
    pose proof (split_meet_bits a r) as Hmeet.
    pose proof (split_power_bits w) as [Hmodulus _].
    assert (Hpoint : size (abst (2 ^ Z.pos w)) = Z.size_nat (2 ^ Z.pos w)).
    { unfold size, abst, itv_bits, bnd_bits. apply Nat.max_id. }
    rewrite Hpoint in Htime. rewrite !Nat2N.inj_add in *. lia.
  Qed.

  (** Signed splitting pays for two ranges and their finite translation. *)
  Lemma signed_split_time_quadratic : forall w a,
    (T_signed_split w a <= 8192 * (T.c_thresholds + 1) *
      N.of_nat ((Pos.to_nat w + size a + 1) ^ 2))%N.
  Proof.
    intros w a. set (s := Pos.to_nat w + size a + 1).
    set (budget := ((T.c_thresholds + 1) * N.of_nat s)%N).
    assert (Hs : 1 <= s) by (unfold s; lia).
    assert (Hbudget : (1 <= budget /\ N.of_nat s <= budget)%N) by (unfold budget; nia).
    pose proof (split_power_time w) as Hpower.
    pose proof (split_range_bits w) as [Hlowrange Hhighrange].
    pose proof (split_meet_width_time w a
      (I (Fin 0) (Fin (2 ^ (Z.pos w - 1) - 1))) Hlowrange) as Hlow.
    pose proof (split_meet_width_time w a
      (I (Fin (2 ^ (Z.pos w - 1))) (Fin (2 ^ Z.pos w - 1))) Hhighrange) as Hhigh.
    pose proof (split_sub_width_time w a
      (I (Fin (2 ^ (Z.pos w - 1))) (Fin (2 ^ Z.pos w - 1))) Hhighrange) as Htranslate.
    fold s budget in Hlow, Hhigh. fold s in Htranslate.
    assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= budget)%N).
    { assert (Hpart : (N.of_nat (Pos.to_nat w + 1) <= N.of_nat s)%N) by (unfold s; lia).
      lia. }
    eapply N.le_trans with (512 * budget)%N.
    - unfold T_signed_split, T_abst. cbn beta iota zeta. lia.
    - fold s. unfold budget. rewrite Nat.pow_2_r, Nat2N.inj_mul. nia.
  Qed.

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
  (** Backward transfer additionally charges the requested result. *)
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o r xs. pose proof (L.T_view_le o) as Hview.
    pose proof (work_sizes o xs) as Hwork.
    remember (work o xs) as budget eqn:Hbudget in *. clear Hbudget.
    assert (Hpositive : (1 <= N.of_nat (budget + size r + 1))%N) by lia.
    unfold T_backward.
    destruct (L.view o); destruct xs as [|a [|b [|extra xs]]];
      cbn beta iota zeta;
      unfold Datatypes.T_fst, Datatypes.T_snd;
      cbn beta zeta;
      cbn [map fold_right] in Hwork.
    all: try match goal with
    | |- context [T_add_back ?r ?a ?b] =>
        pose proof (add_back_time_linear r a b) as Hprimitive
    | |- context [T_sub_back ?r ?a ?b] =>
        pose proof (sub_back_time_linear r a b) as Hprimitive
    | |- context [T_mul_back ?r ?a ?b] =>
        pose proof (mul_back_time_linear r a b) as Hprimitive
    | |- context [T_udiv_back ?r ?a ?b] =>
        pose proof (unsigned_back_time_linear a b) as Hprimitive; unfold T_udiv_back
    | |- context [T_urem_back ?r ?a ?b] =>
        pose proof (unsigned_back_time_linear a b) as Hprimitive; unfold T_urem_back
    end.
    all: unfold c_val in *; nia.
  Qed.
  (** Guard transfer is bounded by guard work. *)
  Lemma T_guard_le : forall g xs, (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. pose proof (L.T_gview_le g) as Hview.
    pose proof (gwork_sizes g xs) as Hwork.
    remember (gwork g xs) as budget eqn:Hbudget in *. clear Hbudget.
    assert (Hpositive : (1 <= N.of_nat (budget + 1))%N) by lia.
    unfold T_guard.
    destruct (L.gview g) as [c| |]; [destruct c| |];
      destruct xs as [|a [|b [|extra xs]]]; cbn beta iota zeta;
      unfold Datatypes.T_fst, Datatypes.T_snd;
      cbn beta zeta; cbn [map fold_right] in Hwork.
    all: try match goal with
    | |- context [T_strict_back ?a ?b] =>
        pose proof (strict_back_time_linear a b) as Hprimitive
    | |- context [T_ult_back (abst 1) ?a ?b] =>
        pose proof (ult_back_time_linear (abst 1) a b) as Hprimitive;
        rewrite abst_result_bits in Hprimitive;
        cbn [Z.size_nat Pos.size_nat] in Hprimitive; unfold T_abst
    | |- context [T_meet ?a ?b] =>
        pose proof (meet_time_linear a b) as Hleft;
        pose proof (meet_time_linear b a) as Hright
    end.
    all: unfold c_val in *; nia.
  Qed.
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
  Proof.
    intros o r xs. pose proof (work_sizes o xs) as Hwork.
    remember (work o xs) as budget eqn:Hbudget in *. clear Hbudget.
    unfold backward.
    destruct (L.view o); destruct xs as [|a [|b [|extra xs]]];
      cbn beta iota zeta; cbn [map fold_right] in Hwork |- *.
    all: try match goal with
    | |- context [add_back ?r ?a ?b] =>
        pose proof (add_back_result_bits r a b) as Hprimitive
    | |- context [sub_back ?r ?a ?b] =>
        pose proof (sub_back_result_bits r a b) as Hprimitive
    | |- context [mul_back ?r ?a ?b] =>
        pose proof (mul_back_result_bits r a b) as Hprimitive
    | |- context [udiv_back ?r ?a ?b] =>
        unfold udiv_back; pose proof (unsigned_back_result_bits a b) as Hprimitive
    | |- context [urem_back ?r ?a ?b] =>
        unfold urem_back; pose proof (unsigned_back_result_bits a b) as Hprimitive
    end.
    all: unfold c_val; nia.
  Qed.
  (** Guard results fit within the charged guard work. *)
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. pose proof (gwork_sizes g xs) as Hwork.
    remember (gwork g xs) as budget eqn:Hbudget in *. clear Hbudget.
    unfold guard.
    destruct (L.gview g) as [c| |]; [destruct c| |];
      destruct xs as [|a [|b [|extra xs]]]; cbn beta iota zeta;
      cbn [map fold_right] in Hwork |- *.
    all: try match goal with
    | |- context [strict_back ?a ?b] =>
        pose proof (strict_back_result_bits a b) as Hprimitive
    | |- context [ult_back (abst 1) ?a ?b] =>
        pose proof (ult_back_result_bits (abst 1) a b) as Hprimitive
    | |- context [meet ?a ?b] =>
        pose proof (meet_result_bits a b) as Hleft;
        pose proof (meet_result_bits b a) as Hright
    end.
    all: unfold c_val; nia.
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
  Proof.
    intros a b. pose proof (add_time_linear a b). unfold c_interval. nia.
  Qed.
  (** Subtraction charges linear endpoint arithmetic. *)
  Lemma T_sub_le : forall a b, (T_sub a b <= c_interval * N.of_nat ((size a + size b +
    1)%nat))%N.
  Proof.
    intros a b. pose proof (sub_time_linear a b). unfold c_interval. nia.
  Qed.
  (** Multiplication has the published quadratic endpoint bound. *)
  Lemma T_mul_le : forall a b, (T_mul a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  Proof.
    intros a b. pose proof (mul_time_quadratic a b). unfold c_interval. nia.
  Qed.
  (** Unsigned division has the published quadratic endpoint bound. *)
  Lemma T_udiv_le : forall a b, (T_udiv a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  Proof.
    intros a b. pose proof (udiv_time_quadratic a b). unfold c_interval. nia.
  Qed.
  (** Unsigned remainder has the published quadratic endpoint bound. *)
  Lemma T_urem_le : forall a b, (T_urem a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  Proof.
    intros a b. pose proof (urem_time_quadratic a b). unfold c_interval. nia.
  Qed.
  (** Bitwise conjunction has the published quadratic endpoint bound. *)
  Lemma T_bitand_le : forall a b, (T_bitand a b <= c_interval * N.of_nat ((binary_work a
    b)%nat))%N.
  Proof.
    intros a b. pose proof (bitand_time_quadratic a b). unfold c_interval. nia.
  Qed.
  (** Bitwise disjunction has the published quadratic endpoint bound. *)
  Lemma T_bitor_le : forall a b, (T_bitor a b <= c_interval * N.of_nat ((binary_work a
    b)%nat))%N.
  Proof.
    intros a b. pose proof (bitor_time_quadratic a b). unfold c_interval. nia.
  Qed.
  (** Shift transfer has the published quadratic endpoint bound. *)
  Lemma T_shl_le : forall a b, (T_shl a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  Proof.
    intros a b. pose proof (shl_time_quadratic a b). unfold c_interval. nia.
  Qed.
  (** Comparison charges linear endpoint comparisons. *)
  Lemma T_cmp_le : forall c a b, (T_cmp c a b <= c_interval * N.of_nat ((size a + size b +
    1)%nat))%N.
  Proof.
    intros c a b. pose proof (cmp_time_linear c a b). unfold c_interval. nia.
  Qed.
  (** Backward addition charges the result and both operands. *)
  Lemma T_add_back_le : forall r a b, (T_add_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof.
    intros r a b. pose proof (add_back_time_linear r a b).
    assert (Hbudget : size r + size a + size b + 1 <=
      size r + (size a + size b + 1) ^ 2) by (cbn [Nat.pow]; nia).
    unfold c_interval. nia.
  Qed.
  (** Backward subtraction charges the result and both operands. *)
  Lemma T_sub_back_le : forall r a b, (T_sub_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof.
    intros r a b. pose proof (sub_back_time_linear r a b).
    assert (Hbudget : size r + size a + size b + 1 <=
      size r + (size a + size b + 1) ^ 2) by (cbn [Nat.pow]; nia).
    unfold c_interval. nia.
  Qed.
  (** Backward multiplication charges the result and both operands. *)
  Lemma T_mul_back_le : forall r a b, (T_mul_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof.
    intros r a b. pose proof (mul_back_time_linear r a b).
    assert (Hbudget : size r + size a + size b + 1 <=
      size r + (size a + size b + 1) ^ 2) by (cbn [Nat.pow]; nia).
    unfold c_interval. nia.
  Qed.
  (** Backward unsigned division charges the result and both operands. *)
  Lemma T_udiv_back_le : forall r a b, (T_udiv_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof.
    intros r a b. pose proof (unsigned_back_time_linear a b).
    assert (Hbudget : size a + size b + 1 <=
      size r + (size a + size b + 1) ^ 2) by (cbn [Nat.pow]; nia).
    unfold T_udiv_back, c_interval. nia.
  Qed.
  (** Backward unsigned remainder charges the result and both operands. *)
  Lemma T_urem_back_le : forall r a b, (T_urem_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof.
    intros r a b. pose proof (unsigned_back_time_linear a b).
    assert (Hbudget : size a + size b + 1 <=
      size r + (size a + size b + 1) ^ 2) by (cbn [Nat.pow]; nia).
    unfold T_urem_back, c_interval. nia.
  Qed.
  (** Backward comparison charges the result and both operands. *)
  Lemma T_ult_back_le : forall r a b, (T_ult_back r a b <=
    c_interval * N.of_nat ((size r + (size a + size b + 1) ^ 2)%nat))%N.
  Proof.
    intros r a b. pose proof (ult_back_time_linear r a b).
    assert (Hbudget : size r + size a + size b + 1 <=
      size r + (size a + size b + 1) ^ 2) by (cbn [Nat.pow]; nia).
    unfold c_interval. nia.
  Qed.
  (** Signed splitting charges the width and endpoints. *)
  Lemma T_signed_split_le : forall w a, (T_signed_split w a <=
    c_interval * N.of_nat (((Pos.to_nat w + size a + 1) ^ 2)%nat))%N.
  Proof.
    exact signed_split_time_quadratic.
  Qed.
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
  (** The declared work of a binary call includes its quadratic primitive budget. *)
  Lemma forward_work_quadratic : forall o a b,
    binary_work a b <= work o (a :: b :: nil) + 1.
  Proof.
    intros o a b. unfold binary_work, work, operand_bits. fold size.
    cbn [map fold_right length]. rewrite Nat.add_0_r. lia.
  Qed.

  (** The same work budget includes a linear pair of endpoint sizes. *)
  Lemma forward_work_linear : forall o a b,
    size a + size b + 1 <= work o (a :: b :: nil) + 1.
  Proof.
    intros o a b. unfold work, operand_bits.
    cbn [map fold_right length]. rewrite Nat.pow_2_r. nia.
  Qed.

  (** Constant primitive clocks fit every declared forward work budget. *)
  Lemma forward_constant_time : forall o xs,
    (1 <= c_interval * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. assert (Hwork : (1 <= N.of_nat (work o xs + 1))%N) by lia.
    unfold c_interval. nia.
  Qed.

  (** Primitive time bounds may use the enclosing dispatch work budget. *)
  Lemma forward_time_weaken : forall o xs cost n,
    (cost <= c_interval * N.of_nat n)%N -> n <= work o xs + 1 ->
    (cost <= c_interval * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs cost n Htime Hwork. eapply N.le_trans; [exact Htime|].
    apply N.mul_le_mono_l. lia.
  Qed.

  (** The value-domain constant pays for the operator view and primitive call. *)
  Lemma forward_dispatch_time : forall o xs cost,
    (cost <= c_interval * N.of_nat (work o xs + 1))%N ->
    (1 + (L.T_view o + cost) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs cost Hprimitive. pose proof (L.T_view_le o) as Hview.
    set (budget := N.of_nat (work o xs + 1)) in *.
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; lia).
    assert (Hoverhead : (1 + L.T_view o <= (L.c_view + 1) * budget)%N) by nia.
    assert (Hcoeff : (c_interval + L.c_view + 1 <= c_val)%N).
    { unfold c_interval, c_val. nia. }
    eapply N.le_trans with ((c_interval + L.c_view + 1) * budget)%N; [nia|].
    now apply N.mul_le_mono_r.
  Qed.


  (** Binary result bounds can be charged to the enclosing forward work. *)
  Lemma forward_pair_size : forall o a b r,
    size r <= 2 * (size a + size b + 1) -> size r <= 2 * (work o (a :: b :: nil) + 1).
  Proof.
    intros o a b r Hresult. pose proof (forward_work_linear o a b) as Hwork. lia.
  Qed.

  (** Forward results fit a small multiple of the declared work before constant scaling. *)
  Lemma forward_result_bits : forall o xs, size (forward o xs) <= 2 * (work o xs + 1).
  Proof.
    intros o xs. unfold forward.
    destruct (L.view o) as [ | | | | | | | | c | z | ] eqn:Hview;
      destruct xs as [|a [|b [|extra rest]]]; cbn beta iota zeta;
      try (unfold top, size, itv_bits, bnd_bits; lia).
    - apply forward_pair_size. pose proof (add_result_bits a b) as Hbits; lia.
    - apply forward_pair_size. pose proof (sub_result_bits a b) as Hbits; lia.
    - apply forward_pair_size. pose proof (mul_result_bits a b) as Hbits; lia.
    - apply forward_pair_size. pose proof (udiv_result_bits a b) as Hbits; lia.
    - apply forward_pair_size. pose proof (urem_result_bits a b) as Hbits; lia.
    - apply forward_pair_size. pose proof (bitand_result_bits a b) as Hbits; lia.
    - apply forward_pair_size. pose proof (bitor_result_bits a b) as Hbits; lia.
    - apply forward_pair_size. apply shl_result_bits.
    - apply forward_pair_size. pose proof (cmp_result_bits c a b) as Hbits; lia.
    - rewrite abst_result_bits. unfold work, operand_bits. rewrite Hview.
      cbn [map fold_right length Nat.pow]. lia.
  Qed.


  (** Forward transfer is bounded by operator work. *)
  Lemma T_forward_le : forall o xs, (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. unfold T_forward.
    destruct (L.view o) as [ | | | | | | | | c | z | ] eqn:Hview;
      destruct xs as [|a [|b [|extra rest]]]; cbn beta iota zeta;
      apply forward_dispatch_time; try apply N.le_0_l; try apply forward_constant_time.
    - eapply forward_time_weaken; [apply T_add_le|apply forward_work_linear].
    - eapply forward_time_weaken; [apply T_sub_le|apply forward_work_linear].
    - eapply forward_time_weaken; [apply T_mul_le|apply forward_work_quadratic].
    - eapply forward_time_weaken; [apply T_udiv_le|apply forward_work_quadratic].
    - eapply forward_time_weaken; [apply T_urem_le|apply forward_work_quadratic].
    - eapply forward_time_weaken; [apply T_bitand_le|apply forward_work_quadratic].
    - eapply forward_time_weaken; [apply T_bitor_le|apply forward_work_quadratic].
    - eapply forward_time_weaken; [apply T_shl_le|apply forward_work_quadratic].
    - eapply forward_time_weaken; [apply T_cmp_le|apply forward_work_linear].
  Qed.

  (** Forward results fit within the charged operator work. *)
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. pose proof (forward_result_bits o xs) as Hbits.
    eapply N.le_trans with (2 * N.of_nat (work o xs + 1))%N; [lia|].
    apply N.mul_le_mono_r. unfold c_val. nia.
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
  Proof.
    exact shl_time_quadratic.
  Qed.
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
  Proof.
    intros a b. pose proof (mul_time_quadratic a b). unfold k_interval_arith. nia.
  Qed.
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
  Proof.
    unfold bigO. exists 64%N. intros [a b] _.
    cbn [fst snd]. pose proof (mul_time_quadratic a b). nia.
  Qed.
  (** Addition has the published linear class. *)
  Lemma add_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (snd x) + 1))
    (fun x => T_add (fst x) (snd x)).
  Proof. Admitted. (* STUB *)
  (** Subtraction has the published linear class. *)
  Lemma sub_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (snd x) + 1))
    (fun x => T_sub (fst x) (snd x)).
  Proof. Admitted. (* STUB *)
  (** Unsigned division has the published quadratic endpoint class. *)
  Lemma udiv_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (binary_work (fst x) (snd x))) (fun x => T_udiv (fst x) (snd x)).
  Proof. Admitted. (* STUB *)
  (** Unsigned remainder has the published quadratic endpoint class. *)
  Lemma urem_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (binary_work (fst x) (snd x))) (fun x => T_urem (fst x) (snd x)).
  Proof. Admitted. (* STUB *)
  (** Shift has the published quadratic endpoint class. *)
  Lemma shl_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (binary_work (fst x) (snd x))) (fun x => T_shl (fst x) (snd x)).
  Proof. Admitted. (* STUB *)
  (** Threshold widening has the published bits-plus-search-path class. *)
  Lemma widen_bigO : bigO (X := ttree * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (size (fst (snd x)) + size (snd (snd x)) +
      (T.depth (fst x) + 1) * (T.tree_bits (fst x) + 1) + 1))
    (fun x => T_widen (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)
  (** Backward addition is linear in the result and operand sizes. *)
  Lemma add_back_bigO : bigO (X := itv * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (fst (snd x)) + size (snd (snd x)) + 1))
    (fun x => T_add_back (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)
  (** Backward subtraction is linear in the result and operand sizes. *)
  Lemma sub_back_bigO : bigO (X := itv * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (fst (snd x)) + size (snd (snd x)) + 1))
    (fun x => T_sub_back (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)
  (** Bitwise conjunction is linear, because the result is a minimum of upper endpoints. *)
  Lemma bitand_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (snd x) + 1)) (fun x => T_bitand (fst x) (snd x)).
  Proof. Admitted. (* STUB *)
  (** Bitwise disjunction is linear, because the result is a mask of one bit length. *)
  Lemma bitor_bigO : bigO (X := itv * itv) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (snd x) + 1)) (fun x => T_bitor (fst x) (snd x)).
  Proof. Admitted. (* STUB *)
  (** Comparison has the published linear class. *)
  Lemma cmp_bigO : bigO (X := comparison * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (size (fst (snd x)) + size (snd (snd x)) + 1))
    (fun x => T_cmp (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)
  (** Backward multiplication is linear, because a preimage only reads a point. *)
  Lemma mul_back_bigO : bigO (X := itv * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (fst (snd x)) + size (snd (snd x)) + 1))
    (fun x => T_mul_back (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)
  (** Backward division is linear, because it only meets with fixed bounds. *)
  Lemma udiv_back_bigO : bigO (X := itv * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (fst (snd x)) + size (snd (snd x)) + 1))
    (fun x => T_udiv_back (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)
  (** Backward remainder is linear, because it only meets with fixed bounds. *)
  Lemma urem_back_bigO : bigO (X := itv * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (fst (snd x)) + size (snd (snd x)) + 1))
    (fun x => T_urem_back (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)
  (** Backward comparison is linear in the result and operand sizes. *)
  Lemma ult_back_bigO : bigO (X := itv * (itv * itv)) (fun _ => True)
    (fun x => N.of_nat (size (fst x) + size (fst (snd x)) + size (snd (snd x)) + 1))
    (fun x => T_ult_back (fst x) (fst (snd x)) (snd (snd x))).
  Proof. Admitted. (* STUB *)
  (** Signed splitting is linear in the width and the endpoints. *)
  Lemma signed_split_bigO : bigO (X := positive * itv) (fun _ => True)
    (fun x => N.of_nat (Pos.to_nat (fst x) + size (snd x) + 1))
    (fun x => T_signed_split (fst x) (snd x)).
  Proof. Admitted. (* STUB *)
  (** Forward transfer has the published operator-work class. *)
  Lemma forward_bigO : (bigO (fun _ => True)
    (fun ox => N.of_nat ((work (fst ox) (snd ox))%nat))
    (fun ox => T_forward (fst ox) (snd ox)))%N.
  Proof. Admitted. (* STUB *)
End IntervalT.
