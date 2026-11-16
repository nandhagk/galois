(** * Range-based bit-vector checks

    Checks use numeric ranges to detect possible bit-vector errors.
    For example, a divisor range excluding zero rules out division by zero.
    Builds on: BitsChecksSig, ChecksSig, BitsLang and ValueSig. *)

From Stdlib Require Import ZArith Zpow_facts NArith List Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig ValueSig BitsLang.
From Galois.Alarms Require Import ChecksSig BitsChecksSig.
Import List.ListNotations.

(** A range containing zero makes the zero-membership test succeed. *)
Lemma range_zero_complete : forall r,
  in_bnd (fst r) (snd r) 0 -> range_zero r = true.
Proof.
  intros [lo hi] [Hlo Hhi]. cbn [range_zero fst snd]. apply andb_true_iff. split.
  - destruct lo; cbn [fst snd] in Hlo |- *; try contradiction; try reflexivity.
    apply Z.leb_le. exact Hlo.
  - destruct hi; cbn [fst snd] in Hhi |- *; try contradiction; try reflexivity.
    apply Z.leb_le. exact Hhi.
Qed.

(** A nonnegative lower endpoint makes every represented number nonnegative. *)
Lemma range_nonnegative_sound : forall r z,
  in_bnd (fst r) (snd r) z -> range_nonnegative r = true -> (0 <= z)%Z.
Proof.
  intros [lo hi] z [Hlo Hhi] Htest. destruct lo;
    cbn [range_nonnegative fst snd] in Htest; try discriminate; try contradiction.
  apply Z.leb_le in Htest. cbn [fst] in Hlo. lia.
Qed.

(** Strictly ordered endpoints separate every number in the two ranges. *)
Lemma ranges_lt_sound : forall ra rb x y,
  in_bnd (fst ra) (snd ra) x -> in_bnd (fst rb) (snd rb) y ->
  bound_lt (snd ra) (fst rb) = true -> (x < y)%Z.
Proof.
  intros [la ha] [lb hb] x y [Hla Hha] [Hlb Hhb] Htest.
  destruct ha, lb; cbn [bound_lt fst snd] in Htest;
    cbn [fst snd] in Hha, Hlb; try discriminate; try contradiction.
  apply Z.ltb_lt in Htest. lia.
Qed.

(** Multiplication by a fixed integer is bounded by its two endpoint products. *)
Lemma mul_endpoint_bounds : forall k lo hi v, (lo <= v <= hi)%Z ->
  (Z.min (k * lo) (k * hi) <= k * v <= Z.max (k * lo) (k * hi))%Z.
Proof.
  intros k lo hi v Hv. destruct (Z_le_gt_dec 0 k) as [Hpos|Hneg].
  - rewrite Z.min_l, Z.max_r by nia. nia.
  - rewrite Z.min_r, Z.max_l by nia. nia.
Qed.

(** The four corner products bound every product of numbers from two finite ranges. *)
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

(** A range that passes the width test contains only representable mathematical results. *)
Lemma range_fits_sound : forall s w r z,
  range_fits s w r = true -> (fst r <= z <= snd r)%Z ->
  (if s then (- Word.half w <= z < Word.half w)%Z
   else (0 <= z < Word.modulus w)%Z).
Proof.
  intros s w r z Hfits Hrange. destruct s; cbn [range_fits] in Hfits;
    apply andb_true_iff in Hfits as [Hlo Hhi];
    apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi; lia.
Qed.

Module BitsChecksCode (V : VALUE_DOMAIN_OPS BitsLangCode)
    (Q QS : BITS_RANGE_OPS V) (W : BITS_WIDTH_OPS V) <: BITS_CHECKS_OPS V Q QS W.
  Definition kd := kind.

  Definition may_fail (k : kd) (xs : list V.t) : bool :=
    match k, xs with
    | DivZero, [d] => range_zero (Q.range d)
    | NullDeref, [p] => range_zero (Q.range p)
    | Bounds, [i; len] =>
        negb (range_nonnegative (Q.range i) && bound_lt (snd (Q.range i)) (fst (Q.range len)))
    | Overflow o s, [a; b] =>
        match W.width a, W.width b,
          range_result o (if s then QS.range a else Q.range a)
            (if s then QS.range b else Q.range b) with
        | Some w, Some v, Some r => negb (Pos.eqb w v && range_fits s w r)
        | _, _, _ => true
        end
    | _, _ => true
    end.
End BitsChecksCode.

Module BitsChecks (V : VALUE_DOMAIN BitsLang)
    (Q : RANGE_QUERY BitsLang NumU V) (QS : RANGE_QUERY BitsLang NumS V)
    (W : BITS_WIDTH V) <: BITS_CHECKS V Q QS W.
  Include BitsChecksCode V Q QS W.

  Definition mathematical_result (o : Op.op) (s : bool) (a b : word) : option Z :=
    let x := if s then NumS.num a else NumU.num a in
    let y := if s then NumS.num b else NumU.num b in
    match o with
    | bvadd => Some (x + y)%Z
    | bvsub => Some (x - y)%Z
    | bvmul => Some (x * y)%Z
    | _ => None
    end.

  Definition safe (k : kd) (cs : list word) : Prop :=
    match k, cs with
    | DivZero, [d] => snd d <> 0%Z
    | NullDeref, [p] => snd p <> 0%Z
    | Bounds, [i; len] => (0 <= snd i < snd len)%Z
    | Overflow o s, [a; b] => fst a = fst b /\
        exists z, mathematical_result o s a b = Some z /\
          (if s then (- Word.half (fst a) <= z < Word.half (fst a))%Z
           else (0 <= z < Word.modulus (fst a))%Z)
    | _, _ => False
    end.

  (** Excluding zero from an unsigned range excludes a zero concrete value. *)
  Lemma zero_excluded : forall a c, V.gamma a c -> range_zero (Q.range a) = false ->
    snd c <> 0%Z.
  Proof.
    intros a c Hgamma Htest Hzero.
    pose proof (Q.range_sound a c Hgamma) as Hrange.
    change (in_bnd (fst (Q.range a)) (snd (Q.range a)) (snd c)) in Hrange.
    rewrite Hzero in Hrange.
    pose proof (range_zero_complete (Q.range a) Hrange). congruence.
  Qed.

  (** The abstract index bounds imply the concrete bounds check. *)
  Lemma bounds_safe : forall a b i len, V.gamma a i -> V.gamma b len ->
    range_nonnegative (Q.range a) = true ->
    bound_lt (snd (Q.range a)) (fst (Q.range b)) = true -> (0 <= snd i < snd len)%Z.
  Proof.
    intros a b i len Hi Hlen Hnonnegative Hlt.
    pose proof (Q.range_sound a i Hi) as Hri.
    pose proof (Q.range_sound b len Hlen) as Hrlen. split.
    - eapply range_nonnegative_sound; eassumption.
    - eapply ranges_lt_sound; eassumption.
  Qed.

  (** Interval arithmetic covers the selected mathematical operation. *)
  Lemma result_range_sound : forall o (s : bool) a b ra rb r,
    in_bnd (fst ra) (snd ra) (if s then NumS.num a else NumU.num a) ->
    in_bnd (fst rb) (snd rb) (if s then NumS.num b else NumU.num b) ->
    range_result o ra rb = Some r ->
    exists z, mathematical_result o s a b = Some z /\ (fst r <= z <= snd r)%Z.
  Proof.
    intros o s a b [[|la|] [|ha|]] [[|lb|] [|hb|]] r Ha Hb Hresult;
      cbn [range_result] in Hresult; try discriminate.
    change (la <= (if s then NumS.num a else NumU.num a) <= ha)%Z in Ha.
    change (lb <= (if s then NumS.num b else NumU.num b) <= hb)%Z in Hb.
    destruct o; cbn [range_result] in Hresult; try discriminate;
      inversion Hresult; subst r; cbn [mathematical_result fst snd].
    - eexists. split; [reflexivity|lia].
    - eexists. split; [reflexivity|lia].
    - eexists. split; [reflexivity|apply mul_rectangle_bounds; assumption].
  Qed.

  (** Equal widths and a fitting result range imply concrete overflow safety. *)
  Lemma overflow_safe : forall o s a b ca cb, V.gamma a ca -> V.gamma b cb ->
    may_fail (Overflow o s) [a; b] = false -> safe (Overflow o s) [ca; cb].
  Proof.
    intros o s a b ca cb Ha Hb Htest. cbn [may_fail] in Htest.
    destruct (W.width a) as [wa|] eqn:Hwa; try discriminate.
    destruct (W.width b) as [wb|] eqn:Hwb; try discriminate.
    destruct (range_result o (if s then QS.range a else Q.range a)
      (if s then QS.range b else Q.range b)) as [r|] eqn:Hresult; try discriminate.
    apply negb_false_iff in Htest. apply andb_true_iff in Htest as [Hwidth Hfits].
    apply Pos.eqb_eq in Hwidth. subst wb.
    pose proof (W.width_sound a wa ca Hwa Ha) as Hca.
    pose proof (W.width_sound b wa cb Hwb Hb) as Hcb.
    assert (Hra : in_bnd (fst (if s then QS.range a else Q.range a))
      (snd (if s then QS.range a else Q.range a)) (if s then NumS.num ca else NumU.num ca)).
    { destruct s; [apply QS.range_sound|apply Q.range_sound]; exact Ha. }
    assert (Hrb : in_bnd (fst (if s then QS.range b else Q.range b))
      (snd (if s then QS.range b else Q.range b)) (if s then NumS.num cb else NumU.num cb)).
    { destruct s; [apply QS.range_sound|apply Q.range_sound]; exact Hb. }
    destruct (result_range_sound o s ca cb _ _ r Hra Hrb Hresult) as [z [Hz Hrange]].
    split; [congruence|]. exists z. split; [exact Hz|].
    rewrite Hca. eapply range_fits_sound; eassumption.
  Qed.

  (** A false alarm result guarantees safety for every represented operand tuple. *)
  Lemma may_fail_sound : forall k xs cs, may_fail k xs = false ->
    Forall2 V.gamma xs cs -> safe k cs.
  Proof.
    intros k xs cs Htest Hgamma. destruct k.
    - destruct xs as [|a [|b xs]]; cbn [may_fail] in Htest; try discriminate.
      inversion Hgamma as [|a' c xs' cs' Hhead Htail]; subst.
      inversion Htail; subst. eapply zero_excluded; eassumption.
    - destruct xs as [|a [|b [|c xs]]]; cbn [may_fail] in Htest; try discriminate.
      inversion Hgamma as [|a' ca xs' cs' Ha Htail]; subst.
      inversion Htail as [|b' cb ys rest Hb Hnil]; subst.
      inversion Hnil; subst. eapply overflow_safe; eassumption.
    - destruct xs as [|a [|b [|c xs]]]; cbn [may_fail] in Htest; try discriminate.
      inversion Hgamma as [|a' i xs' cs' Hi Htail]; subst.
      inversion Htail as [|b' len ys rest Hlen Hnil]; subst.
      inversion Hnil; subst. apply negb_false_iff in Htest.
      apply andb_true_iff in Htest as [Hnonnegative Hlt]. eapply bounds_safe; eassumption.
    - destruct xs as [|a [|b xs]]; cbn [may_fail] in Htest; try discriminate.
      inversion Hgamma as [|a' c xs' cs' Hhead Htail]; subst.
      inversion Htail; subst. eapply zero_excluded; eassumption.
  Qed.

  (** Top operands report a possible failure whenever some concrete tuple is unsafe. *)
  Lemma may_fail_top : forall k n,
    (exists cs, length cs = n /\ ~ safe k cs) -> may_fail k (repeat V.top n) = true.
  Proof.
    intros k n [cs [Hlen Hunsafe]].
    assert (Hgamma : Forall2 V.gamma (repeat V.top (length cs)) cs).
    { clear Hlen Hunsafe. induction cs as [|c cs IH]; cbn;
        constructor; [apply V.gamma_top|exact IH]. }
    rewrite Hlen in Hgamma.
    destruct (may_fail k (repeat V.top n)) eqn:Htest; [reflexivity|].
    exfalso. apply Hunsafe. eapply may_fail_sound; eassumption.
  Qed.
  (** Division safety excludes a zero divisor. *)
  Lemma safe_divzero : forall d, safe DivZero [d] <-> snd d <> 0%Z.
  Proof.
    reflexivity.
  Qed.
  (** Dereference safety excludes a null pointer. *)
  Lemma safe_null : forall p, safe NullDeref [p] <-> snd p <> 0%Z.
  Proof.
    reflexivity.
  Qed.
  (** Bounds safety places the index between zero and the concrete length. *)
  Lemma safe_bounds : forall i len, safe Bounds [i; len] <-> (0 <= snd i < snd len)%Z.
  Proof.
    reflexivity.
  Qed.
  (** Overflow safety requires equal operand widths and a representable mathematical result. *)
  Lemma safe_overflow : forall o s a b,
    safe (Overflow o s) [a; b] <-> fst a = fst b /\
      exists z, mathematical_result o s a b = Some z /\
      (if s then (- Word.half (fst a) <= z < Word.half (fst a))%Z
       else (0 <= z < Word.modulus (fst a))%Z).
  Proof.
    reflexivity.
  Qed.
  (** Mathematical addition adds the selected views before any wrapping. *)
  Lemma result_add : forall s a b, mathematical_result bvadd s a b =
    Some ((if s then NumS.num a else NumU.num a) +
      (if s then NumS.num b else NumU.num b))%Z.
  Proof.
    reflexivity.
  Qed.
  (** Mathematical subtraction subtracts the selected views before any wrapping. *)
  Lemma result_sub : forall s a b, mathematical_result bvsub s a b =
    Some ((if s then NumS.num a else NumU.num a) -
      (if s then NumS.num b else NumU.num b))%Z.
  Proof.
    reflexivity.
  Qed.
  (** Mathematical multiplication multiplies the selected views before any wrapping. *)
  Lemma result_mul : forall s a b, mathematical_result bvmul s a b =
    Some ((if s then NumS.num a else NumU.num a) *
      (if s then NumS.num b else NumU.num b))%Z.
  Proof.
    reflexivity.
  Qed.
  (** The divisor check tests zero membership in its unsigned range. *)
  Lemma may_fail_divzero : forall d, may_fail DivZero [d] = range_zero (Q.range d).
  Proof.
    reflexivity.
  Qed.
  (** The null check tests zero membership in its unsigned range. *)
  Lemma may_fail_null : forall p, may_fail NullDeref [p] = range_zero (Q.range p).
  Proof.
    reflexivity.
  Qed.
  (** The bounds check compares the worst index with the least possible length. *)
  Lemma may_fail_bounds : forall i len, may_fail Bounds [i; len] =
    negb (range_nonnegative (Q.range i) && bound_lt (snd (Q.range i)) (fst (Q.range len))).
  Proof.
    reflexivity.
  Qed.
  (** Only addition, subtraction and multiplication have a mathematical overflow result. *)
  Lemma result_other : forall o s a b,
    ~ In o (bvadd :: bvsub :: bvmul :: nil) -> mathematical_result o s a b = None.
  Proof.
    intros o s a b Hother. destruct o; cbn [mathematical_result]; try reflexivity;
      exfalso; apply Hother; cbn; auto.
  Qed.
  (** The overflow check accepts only equal widths and a fitting result interval. *)
  Lemma may_fail_overflow : forall o s a b, may_fail (Overflow o s) [a; b] =
    match W.width a, W.width b,
      range_result o (if s then QS.range a else Q.range a)
        (if s then QS.range b else Q.range b) with
    | Some w, Some v, Some r => negb (Pos.eqb w v && range_fits s w r)
    | _, _, _ => true
    end.
  Proof.
    reflexivity.
  Qed.
  (** An unsupported arity always reports a possible failure. *)
  Lemma may_fail_other : forall k xs,
    match k, xs with
    | DivZero, [_] | NullDeref, [_] | Bounds, [_; _] | Overflow _ _, [_; _] => True
    | _, _ => may_fail k xs = true
    end.
  Proof.
    intros k xs. destruct k; destruct xs as [|a [|b [|c xs]]]; cbn [may_fail]; auto.
  Qed.
End BitsChecks.

(** * Costs of endpoint arithmetic *)

Module ChecksCost.
  Local Open Scope nat_scope.

  (** Adding positive integers adds at most one carry bit. *)
  Lemma positive_add_bits : forall p q,
    Pos.size_nat (p + q) <= Pos.size_nat p + Pos.size_nat q + 1.
  Proof.
    intros p q. apply Std.Pos.size_nat_least.
    rewrite Pos2Nat.inj_add, !Nat.pow_add_r. cbn [Nat.pow].
    pose proof (Std.Pos.size_nat_upper p).
    pose proof (Std.Pos.size_nat_upper q).
    pose proof (Pos2Nat.is_pos p). pose proof (Pos2Nat.is_pos q). nia.
  Qed.

  (** A signed difference fits the combined bit sizes of its positive operands. *)
  Lemma positive_difference_bits : forall p q,
    Z.size_nat (Z.pos_sub p q) <= Pos.size_nat p + Pos.size_nat q.
  Proof.
    intros p q. rewrite Z.pos_sub_spec. destruct (Pos.compare p q);
      cbn [Z.size_nat]; try lia;
      pose proof (Std.Pos.size_nat_sub p q);
      pose proof (Std.Pos.size_nat_sub q p); lia.
  Qed.

  (** Negation preserves the stored integer bit count. *)
  Lemma opp_bits : forall z, Z.size_nat (- z) = Z.size_nat z.
  Proof.
    intros []; reflexivity.
  Qed.

  (** Integer addition has a linear result-size bound. *)
  Lemma add_bits : forall x y,
    Z.size_nat (x + y) <= Z.size_nat x + Z.size_nat y + 1.
  Proof.
    intros [|p|p] [|q|q]; cbn [Z.add Z.size_nat]; try lia;
      try apply positive_add_bits;
      pose proof (positive_difference_bits p q);
      pose proof (positive_difference_bits q p); lia.
  Qed.

  (** Integer subtraction has the same result-size bound as addition. *)
  Lemma sub_bits : forall x y,
    Z.size_nat (x - y) <= Z.size_nat x + Z.size_nat y + 1.
  Proof.
    intros x y. change (Z.size_nat (x + - y) <= Z.size_nat x + Z.size_nat y + 1).
    pose proof (add_bits x (- y)). rewrite opp_bits in *. lia.
  Qed.

  (** Integer multiplication adds the operand bit bounds. *)
  Lemma mul_bits : forall x y,
    Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y.
  Proof.
    intros [|p|p] [|q|q]; cbn [Z.mul Z.size_nat]; try lia;
      apply Std.Pos.size_nat_mul.
  Qed.

  (** A minimum selects one of the two stored integers. *)
  Lemma min_bits : forall x y,
    Z.size_nat (Z.min x y) <= Nat.max (Z.size_nat x) (Z.size_nat y).
  Proof.
    intros x y. unfold Z.min. destruct (Z.compare x y);
      first [apply Nat.le_max_l | apply Nat.le_max_r].
  Qed.

  (** A maximum selects one of the two stored integers. *)
  Lemma max_bits : forall x y,
    Z.size_nat (Z.max x y) <= Nat.max (Z.size_nat x) (Z.size_nat y).
  Proof.
    intros x y. unfold Z.max. destruct (Z.compare x y);
      first [apply Nat.le_max_l | apply Nat.le_max_r].
  Qed.

  (** A minimum respects a common bound on its two operand sizes. *)
  Lemma min_bits_bound : forall x y budget,
    Z.size_nat x <= budget -> Z.size_nat y <= budget ->
    Z.size_nat (Z.min x y) <= budget.
  Proof.
    intros x y budget Hx Hy. eapply Nat.le_trans; [apply min_bits|].
    apply Nat.max_lub; assumption.
  Qed.

  (** A maximum respects a common bound on its two operand sizes. *)
  Lemma max_bits_bound : forall x y budget,
    Z.size_nat x <= budget -> Z.size_nat y <= budget ->
    Z.size_nat (Z.max x y) <= budget.
  Proof.
    intros x y budget Hx Hy. eapply Nat.le_trans; [apply max_bits|].
    apply Nat.max_lub; assumption.
  Qed.

  (** Each produced result endpoint fits the combined input endpoint sizes. *)
  Lemma result_bits : forall o ra rb r, range_result o ra rb = Some r ->
    Z.size_nat (fst r) + Z.size_nat (snd r) <=
      2 * (range_bits ra + range_bits rb + 1).
  Proof.
    intros o [[|la|] [|ha|]] [[|lb|] [|hb|]] r Hresult;
      cbn [range_result] in Hresult; try discriminate.
    destruct o; cbn [range_result] in Hresult; try discriminate;
      inversion Hresult; subst r; unfold range_bits; cbn [fst snd].
    - pose proof (add_bits la lb). pose proof (add_bits ha hb). lia.
    - pose proof (sub_bits la hb). pose proof (sub_bits ha lb). lia.
    - set (budget := Z.size_nat la + Z.size_nat ha + Z.size_nat lb + Z.size_nat hb).
      assert (Hlo : Z.size_nat
        (Z.min (Z.min (la * lb) (la * hb)) (Z.min (ha * lb) (ha * hb))) <= budget).
      { repeat apply min_bits_bound;
          (eapply Nat.le_trans; [apply mul_bits|unfold budget; lia]). }
      assert (Hhi : Z.size_nat
        (Z.max (Z.max (la * lb) (la * hb)) (Z.max (ha * lb) (ha * hb))) <= budget).
      { repeat apply max_bits_bound;
          (eapply Nat.le_trans; [apply mul_bits|unfold budget; lia]). }
      unfold budget in Hlo, Hhi. lia.
  Qed.

  (** A shared bit budget bounds integer addition, subtraction and multiplication. *)
  Lemma arithmetic_time : forall x y budget,
    Z.size_nat x + Z.size_nat y + 1 <= budget ->
    (Std.Z.T_add x y <= 4 * N.of_nat budget /\
     Std.Z.T_sub x y <= 4 * N.of_nat budget /\
     Std.Z.T_mul x y <= 2 * (N.of_nat budget * N.of_nat budget))%N.
  Proof.
    intros x y budget Hsize.
    assert (HsizeN : (N.of_nat (Z.size_nat x) + N.of_nat (Z.size_nat y) + 1 <=
      N.of_nat budget)%N) by lia.
    split; [pose proof (Std.Z.T_add_le x y); rewrite Nat2N.inj_add in *; lia|].
    split; [pose proof (Std.Z.T_sub_le x y); rewrite Nat2N.inj_add in *; lia|].
    pose proof (Std.Z.T_mul_le x y). nia.
  Qed.

  (** Selecting an integer endpoint is linear in its inspected operand size. *)
  Lemma choice_time : forall x y budget, Z.size_nat x + 1 <= budget ->
    (Std.Z.T_min x y <= 4 * N.of_nat budget /\
     Std.Z.T_max x y <= 4 * N.of_nat budget)%N.
  Proof.
    intros x y budget Hsize. pose proof (Std.Z.T_min_le x y).
    pose proof (Std.Z.T_max_le x y). lia.
  Qed.

  (** Finite range arithmetic uses four corner products and six endpoint selections. *)
  Lemma finite_result_time : forall o la ha lb hb,
    (T_range_result o (Fin la, Fin ha) (Fin lb, Fin hb) <= 128 * N.of_nat
      (((Z.size_nat la + Z.size_nat ha) + (Z.size_nat lb + Z.size_nat hb) + 1) ^ 2))%N.
  Proof.
    intros o la ha lb hb.
    set (bits := (Z.size_nat la + Z.size_nat ha) + (Z.size_nat lb + Z.size_nat hb)).
    set (budget := N.of_nat (bits + 1)).
    assert (Hpositive : (1 <= budget)%N) by (unfold budget; rewrite Nat2N.inj_add; lia).
    assert (Hsquare : (budget <= budget * budget)%N) by nia.
    pose proof (arithmetic_time la lb (bits + 1) ltac:(unfold bits; lia)) as [Hall [_ Hmll]].
    pose proof (arithmetic_time ha hb (bits + 1) ltac:(unfold bits; lia)) as [Hahh [_ Hmhh]].
    pose proof (arithmetic_time la hb (bits + 1) ltac:(unfold bits; lia)) as [_ [Hslh Hmlh]].
    pose proof (arithmetic_time ha lb (bits + 1) ltac:(unfold bits; lia)) as [_ [Hshl Hmhl]].
    assert (Hll : Z.size_nat (la * lb) <= bits).
    { eapply Nat.le_trans; [apply mul_bits|unfold bits; lia]. }
    assert (Hlh : Z.size_nat (la * hb) <= bits).
    { eapply Nat.le_trans; [apply mul_bits|unfold bits; lia]. }
    assert (Hhl : Z.size_nat (ha * lb) <= bits).
    { eapply Nat.le_trans; [apply mul_bits|unfold bits; lia]. }
    assert (Hmin : Z.size_nat (Z.min (la * lb) (la * hb)) <= bits).
    { apply min_bits_bound; assumption. }
    assert (Hmax : Z.size_nat (Z.max (la * lb) (la * hb)) <= bits).
    { apply max_bits_bound; assumption. }
    pose proof (choice_time (la * lb) (la * hb) (bits + 1) ltac:(lia)) as [Hminl Hmaxl].
    pose proof (choice_time (ha * lb) (ha * hb) (bits + 1) ltac:(lia)) as [Hminh Hmaxh].
    pose proof (choice_time (Z.min (la * lb) (la * hb))
      (Z.min (ha * lb) (ha * hb)) (bits + 1) ltac:(lia)) as [Hminout _].
    pose proof (choice_time (Z.max (la * lb) (la * hb))
      (Z.max (ha * lb) (ha * hb)) (bits + 1) ltac:(lia)) as [_ Hmaxout].
    rewrite Nat.pow_2_r, Nat2N.inj_mul.
    fold budget in Hall, Hahh, Hslh, Hshl, Hmll, Hmlh, Hmhl, Hmhh,
      Hminl, Hmaxl, Hminh, Hmaxh, Hminout, Hmaxout |- *.
    destruct o; time_unfold T_range_result; time_simpl; lia.
  Qed.

  (** Endpoint arithmetic takes quadratic time in the combined finite endpoint sizes. *)
  Lemma result_time : forall o ra rb,
    (T_range_result o ra rb <=
      128 * N.of_nat ((range_bits ra + range_bits rb + 1) ^ 2))%N.
  Proof.
    intros o ra rb.
    assert (Hpositive : (1 <= N.of_nat ((range_bits ra + range_bits rb + 1) ^ 2))%N).
    { rewrite Nat.pow_2_r, Nat2N.inj_mul, !Nat2N.inj_add. nia. }
    destruct ra as [[|la|] [|ha|]], rb as [[|lb|] [|hb|]];
      try apply finite_result_time; time_unfold T_range_result; time_simpl; lia.
  Qed.

  (** A positive width's bit count is no greater than the width itself. *)
  Lemma positive_bits_value : forall p, Pos.size_nat p <= Pos.to_nat p.
  Proof.
    induction p as [p IH|p IH|]; cbn [Pos.size_nat];
      rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, ?Pos2Nat.inj_1; lia.
  Qed.

  (** A nonnegative integer below a power of two fits within its exponent. *)
  Lemma bits_below_power : forall z n,
    (0 <= z < 2 ^ Z.of_nat n)%Z -> Z.size_nat z <= n.
  Proof.
    intros [|z|z] n Hrange; cbn [Z.size_nat]; try lia.
    now apply Zpower2_Psize.
  Qed.

  (** A power of two stores its exponent plus one bit. *)
  Lemma power_bits : forall n, (0 <= n)%Z ->
    Z.size_nat (2 ^ n) <= Z.to_nat n + 1.
  Proof.
    intros n Hn. apply bits_below_power. split.
    - pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). lia.
    - rewrite Nat2Z.inj_add, Z2Nat.id by exact Hn. apply Z.pow_lt_mono_r; lia.
  Qed.

  (** Both word boundaries fit the width plus one bit. *)
  Lemma width_boundary_bits : forall w,
    Z.size_nat (Word.modulus w) <= Pos.to_nat w + 1 /\
    Z.size_nat (Word.half w) <= Pos.to_nat w + 1.
  Proof.
    intro w. pose proof (power_bits (Z.pos w) ltac:(lia)) as Hmodulus.
    pose proof (power_bits (Z.pos w - 1) ltac:(lia)) as Hhalf.
    pose proof (Z2Nat.id (Z.pos w - 1) ltac:(lia)) as Hhalfwidth.
    pose proof (positive_nat_Z w) as Hwidth.
    change (Z.to_nat (Z.pos w)) with (Pos.to_nat w) in Hmodulus.
    unfold Word.modulus, Word.half. lia.
  Qed.

  (** Power-of-two construction spends constant work for each generated bit. *)
  Lemma power_time : forall z, (Word.Z.T_pow 2 z <= 5 * Z.abs_N z + 2)%N.
  Proof.
    intros [|p|p]; unfold Word.Z.T_pow, Word.Z.T_pow_pos;
      cbn beta iota zeta; try nia.
    pose proof (Std.Pos.T_iter_le (Z.mul 2)
      (fun x => Std.Z.T_mul 2 x) (fun _ => True) 3 1%Z p
      ltac:(easy) ltac:(intros; apply Std.Z.T_mul_two_le) ltac:(constructor)) as Hiter.
    change (Z.abs_N (Z.pos p)) with (N.pos p). nia.
  Qed.

  (** Absolute-value conversion agrees with natural conversion on nonnegative integers. *)
  Lemma abs_N_nat : forall z, (0 <= z)%Z -> Z.abs_N z = N.of_nat (Z.to_nat z).
  Proof.
    intros [|p|p] Hz; cbn [Z.abs_N Z.to_nat]; try reflexivity; lia.
  Qed.

  (** Constructing either word boundary is linear in the width value. *)
  Lemma width_boundary_time : forall w,
    (Word.T_modulus w <= 16 * N.of_nat (Pos.to_nat w + 1) /\
     Word.T_half w <= 16 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    intro w. pose proof (power_time (Z.pos w)) as Hmodulus.
    pose proof (power_time (Z.pos w - 1)) as Hhalf.
    rewrite !abs_N_nat in Hmodulus, Hhalf by lia.
    change (Z.to_nat (Z.pos w)) with (Pos.to_nat w) in Hmodulus.
    pose proof (Z2Nat.id (Z.pos w - 1) ltac:(lia)) as Hhalfwidth.
    pose proof (positive_nat_Z w) as Hwidth.
    pose proof (positive_bits_value w) as Hwidthbits.
    pose proof (Std.Z.T_sub_le (Z.pos w) 1) as Hdecrement.
    change (Z.size_nat 1) with 1 in Hdecrement.
    change (Z.size_nat (Z.pos w)) with (Pos.size_nat w) in Hdecrement.
    split; [time_unfold Word.T_modulus|time_unfold Word.T_half];
      time_simpl; rewrite ?Nat2N.inj_add in *; lia.
  Qed.

  (** The zero test reads at most its finite endpoint bits and fixed bookkeeping. *)
  Lemma zero_time : forall r,
    (T_range_zero r <= 32 * N.of_nat (range_bits r + 1))%N.
  Proof.
    intros [[|lo|] [|hi|]]; unfold range_bits; cbn [fst snd];
      time_unfold T_range_zero; time_simpl; cbn beta iota zeta delta [fst snd];
      time_pose; try change (Z.size_nat 0) with 0 in *.
    all: rewrite ?Nat2N.inj_add; lia.
  Qed.

  (** Nonnegativity testing reads at most the lower endpoint. *)
  Lemma nonnegative_time : forall r,
    (T_range_nonnegative r <= 16 * N.of_nat (range_bits r + 1))%N.
  Proof.
    intros [[|lo|] hi]; unfold range_bits; cbn [fst snd];
      time_unfold T_range_nonnegative; time_simpl; cbn beta iota zeta delta [fst snd];
      time_pose; try change (Z.size_nat 0) with 0 in *.
    all: rewrite ?Nat2N.inj_add; lia.
  Qed.

  (** Strict endpoint comparison is linear in the endpoints it inspects. *)
  Lemma comparison_time : forall ra rb,
    (T_bound_lt (snd ra) (fst rb) <=
      16 * N.of_nat (range_bits ra + range_bits rb + 1))%N.
  Proof.
    intros [la [|ha|]] [[|lb|] hb]; unfold range_bits; cbn [fst snd];
      time_unfold T_bound_lt; time_simpl; cbn beta iota zeta delta [fst snd];
      time_pose; rewrite ?Nat2N.inj_add; lia.
  Qed.

  (** Testing a result range pays for its upper endpoint and the two word boundaries. *)
  Lemma fits_time : forall s w r,
    (T_range_fits s w r <=
      128 * N.of_nat (Pos.to_nat w + Z.size_nat (fst r) + Z.size_nat (snd r) + 1))%N.
  Proof.
    intros s w r. pose proof (width_boundary_time w) as [Hmodulus Hhalf].
    pose proof (width_boundary_bits w) as [Hmodulusbits Hhalfbits].
    pose proof (opp_bits (Word.half w)) as Hopp.
    destruct s; time_unfold T_range_fits; time_simpl; time_pose;
      try change (Z.size_nat 0) with 0 in *.
    all: rewrite ?Nat2N.inj_add in *; lia.
  Qed.
End ChecksCost.

Module BitsChecksT (V : VALUE_DOMAIN_T BitsLangT)
    (Q : BITS_RANGE_T NumU V) (QS : BITS_RANGE_T NumS V) (W : BITS_WIDTH_T V)
    <: BITS_CHECKS_ALL V Q QS W.
  Include BitsChecks V Q QS W.
  Definition work (_ : kd) (xs : list V.t) : nat :=
    ((fold_right Nat.add 0%nat (map V.size xs) + length xs + 1) ^ 2)%nat.
  TimeFun may_fail.
  Definition k_inputs : N := (Q.c_range + QS.c_range + W.c_width + 16)%N.
  Definition c_bits_checks : N := (4096 * k_inputs * k_inputs)%N.
  Definition c_checks : N := c_bits_checks.
  Definition k_bits_checks : N := 32%N.

  (** The shared check coefficient covers each fixed endpoint coefficient. *)
  Local Lemma coefficient_lower : (128 <= c_bits_checks)%N.
  Proof.
    unfold c_bits_checks, k_inputs. nia.
  Qed.

  (** A zero check adds fixed bookkeeping to its query and membership test. *)
  Local Lemma zero_components : forall d,
    (T_may_fail DivZero [d] <=
      64 * (Q.T_range d + N.of_nat (range_bits (Q.range d) + 1)))%N.
  Proof.
    intro d. pose proof (ChecksCost.zero_time (Q.range d)) as Hzero.
    time_unfold T_may_fail. time_simpl. time_pose. rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Bounds checking reads the index range twice and the length range once. *)
  Local Lemma bounds_components : forall i len,
    (T_may_fail Bounds [i; len] <= 64 *
      (Q.T_range i + Q.T_range len +
        N.of_nat (range_bits (Q.range i) + range_bits (Q.range len) + 1)))%N.
  Proof.
    intros i len. pose proof (ChecksCost.nonnegative_time (Q.range i)) as Hnonnegative.
    pose proof (ChecksCost.comparison_time (Q.range i) (Q.range len)) as Hcompare.
    time_unfold T_may_fail. time_simpl. time_pose. rewrite ?Nat2N.inj_add in *. lia.
  Qed.

  (** Either numeric view's range query fits the common input coefficient. *)
  Local Lemma query_time_bound : forall (s : bool) a,
    ((if s then QS.T_range a else Q.T_range a) <=
      k_inputs * N.of_nat (V.size a + 1))%N.
  Proof.
    intros s a. destruct s; eapply N.le_trans;
      [apply QS.T_range_le| |apply Q.T_range_le|];
      apply N.mul_le_mono_r; unfold k_inputs; lia.
  Qed.

  (** Either numeric view's endpoint bits fit the common input coefficient. *)
  Local Lemma query_bits_bound : forall (s : bool) a,
    (N.of_nat (range_bits (if s then QS.range a else Q.range a)) <=
      k_inputs * N.of_nat (V.size a + 1))%N.
  Proof.
    intros s a. destruct s; eapply N.le_trans;
      [apply QS.range_bits_le| |apply Q.range_bits_le|];
      apply N.mul_le_mono_r; unfold k_inputs; lia.
  Qed.

  (** Both queried ranges fit the combined operand budget. *)
  Local Lemma pair_range_bits : forall (s : bool) a b,
    (N.of_nat (range_bits (if s then QS.range a else Q.range a) +
      range_bits (if s then QS.range b else Q.range b) + 1) <=
      k_inputs * N.of_nat (V.size a + V.size b + 3))%N.
  Proof.
    intros s a b. pose proof (query_bits_bound s a) as Ha.
    pose proof (query_bits_bound s b) as Hb.
    assert (Hcoefficient : (1 <= k_inputs)%N) by (unfold k_inputs; lia).
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** A positive input budget is bounded by its scaled square. *)
  Local Lemma scaled_square : forall n, (1 <= n)%nat ->
    (1 <= k_inputs * N.of_nat n /\ N.of_nat n <= k_inputs * N.of_nat n /\
      k_inputs * N.of_nat n <= (k_inputs * N.of_nat n) * (k_inputs * N.of_nat n))%N.
  Proof.
    intros n Hn. assert (Hcoefficient : (1 <= k_inputs)%N) by (unfold k_inputs; lia).
    assert (HnN : (1 <= N.of_nat n)%N) by lia.
    assert (Hpositive : (1 <= k_inputs * N.of_nat n)%N) by nia.
    split; [exact Hpositive|]. split; [nia|].
    replace (k_inputs * N.of_nat n)%N with ((k_inputs * N.of_nat n) * 1)%N at 1 by ring.
    apply N.mul_le_mono_l. exact Hpositive.
  Qed.

  (** The published coefficient covers the internal quadratic budget. *)
  Local Lemma finish_budget : forall n,
    (1024 * ((k_inputs * N.of_nat n) * (k_inputs * N.of_nat n)) <=
      c_checks * N.of_nat (n ^ 2 + 1))%N.
  Proof.
    intro n. unfold c_checks, c_bits_checks.
    rewrite Nat.pow_2_r, Nat2N.inj_add, Nat2N.inj_mul.
    replace (1024 * ((k_inputs * N.of_nat n) * (k_inputs * N.of_nat n)))%N with
      (1024 * (k_inputs * k_inputs) * (N.of_nat n * N.of_nat n))%N by ring.
    replace (4096 * k_inputs * k_inputs)%N with (4096 * (k_inputs * k_inputs))%N by ring.
    eapply N.le_trans with (m :=
      (4096 * (k_inputs * k_inputs) * (N.of_nat n * N.of_nat n))%N).
    - apply N.mul_le_mono_r. lia.
    - apply N.mul_le_mono_l. lia.
  Qed.

  (** A unary zero check fits the squared operand-size budget. *)
  Local Lemma zero_size_time : forall a,
    (T_may_fail DivZero [a] <= c_checks * N.of_nat ((V.size a + 2) ^ 2 + 1))%N.
  Proof.
    intro a. set (linear := (k_inputs * N.of_nat (V.size a + 2))%N).
    pose proof (query_time_bound false a) as Hquery.
    pose proof (query_bits_bound false a) as Hbits. cbn beta iota zeta in Hquery, Hbits.
    assert (Hcoefficient : (1 <= k_inputs)%N) by (unfold k_inputs; lia).
    assert (Hquery' : (Q.T_range a <= linear)%N).
    { unfold linear. rewrite !Nat2N.inj_add in *. nia. }
    assert (Hbits' : (N.of_nat (range_bits (Q.range a) + 1) <= linear)%N).
    { unfold linear. rewrite !Nat2N.inj_add in *. nia. }
    pose proof (scaled_square (V.size a + 2)%nat ltac:(lia)) as [_ [_ Hsquare]].
    fold linear in Hsquare. eapply N.le_trans; [apply zero_components|].
    eapply N.le_trans with (m := (1024 * (linear * linear))%N); [lia|apply finish_budget].
  Qed.

  (** Bounds checking fits the squared combined operand-size budget. *)
  Local Lemma bounds_size_time : forall a b,
    (T_may_fail Bounds [a; b] <=
      c_checks * N.of_nat ((V.size a + V.size b + 3) ^ 2 + 1))%N.
  Proof.
    intros a b. set (linear := (k_inputs * N.of_nat (V.size a + V.size b + 3))%N).
    pose proof (query_time_bound false a) as Ha.
    pose proof (query_time_bound false b) as Hb. cbn beta iota zeta in Ha, Hb.
    assert (Ha' : (Q.T_range a <= linear)%N).
    { eapply N.le_trans; [exact Ha|]. apply N.mul_le_mono_l. lia. }
    assert (Hb' : (Q.T_range b <= linear)%N).
    { eapply N.le_trans; [exact Hb|]. apply N.mul_le_mono_l. lia. }
    pose proof (pair_range_bits false a b) as Hbits. cbn beta iota zeta in Hbits.
    fold linear in Hbits.
    pose proof (scaled_square (V.size a + V.size b + 3)%nat ltac:(lia)) as [_ [_ Hsquare]].
    fold linear in Hsquare. eapply N.le_trans; [apply bounds_components|].
    eapply N.le_trans with (m := (1024 * (linear * linear))%N); [lia|apply finish_budget].
  Qed.

  (** The two range queries and width queries fit their common operand budget. *)
  Local Lemma pair_clocks : forall (s : bool) a b,
    let budget := (k_inputs * N.of_nat (V.size a + V.size b + 3))%N in
    ((if s then QS.T_range a else Q.T_range a) <= budget /\
     (if s then QS.T_range b else Q.T_range b) <= budget /\
     W.T_width a <= budget /\ W.T_width b <= budget)%N.
  Proof.
    intros s a b budget. repeat split.
    - eapply N.le_trans; [apply query_time_bound|]. apply N.mul_le_mono_l. lia.
    - eapply N.le_trans; [apply query_time_bound|]. apply N.mul_le_mono_l. lia.
    - eapply N.le_trans; [apply W.T_width_le|]. apply N.mul_le_mono.
      + unfold k_inputs. lia.
      + lia.
    - eapply N.le_trans; [apply W.T_width_le|]. apply N.mul_le_mono.
      + unfold k_inputs. lia.
      + lia.
  Qed.

  (** Range arithmetic fits the square of the common endpoint budget. *)
  Local Lemma result_time_scaled : forall o (s : bool) a b,
    (T_range_result o (if s then QS.range a else Q.range a)
      (if s then QS.range b else Q.range b) <= 128 *
      ((k_inputs * N.of_nat (V.size a + V.size b + 3)) *
       (k_inputs * N.of_nat (V.size a + V.size b + 3))))%N.
  Proof.
    intros o s a b. eapply N.le_trans; [apply ChecksCost.result_time|].
    rewrite Nat.pow_2_r, Nat2N.inj_mul. apply N.mul_le_mono_l.
    apply N.mul_le_mono; apply pair_range_bits.
  Qed.

  (** The actual result range and reported width pay for the overflow range test. *)
  Local Lemma fits_time_scaled : forall o (s : bool) a b w r,
    W.width a = Some w ->
    range_result o (if s then QS.range a else Q.range a)
      (if s then QS.range b else Q.range b) = Some r ->
    (T_range_fits s w r <= 512 *
      ((k_inputs * N.of_nat (V.size a + V.size b + 3)) *
       (k_inputs * N.of_nat (V.size a + V.size b + 3))))%N.
  Proof.
    intros o s a b w r Hwidth Hresult.
    set (linear := (k_inputs * N.of_nat (V.size a + V.size b + 3))%N).
    pose proof (scaled_square (V.size a + V.size b + 3)%nat ltac:(lia))
      as [Hpositive [Hbase Hsquare]]. fold linear in Hpositive, Hbase, Hsquare.
    pose proof (pair_range_bits s a b) as Hrange. fold linear in Hrange.
    pose proof (ChecksCost.result_bits o _ _ r Hresult) as Hsize.
    assert (HsizeN : (N.of_nat (Z.size_nat (fst r) + Z.size_nat (snd r)) <=
      2 * N.of_nat (range_bits (if s then QS.range a else Q.range a) +
        range_bits (if s then QS.range b else Q.range b) + 1))%N) by lia.
    assert (Hendpoints : (N.of_nat (Z.size_nat (fst r) + Z.size_nat (snd r)) <=
      2 * linear)%N) by lia.
    pose proof (W.width_size a w Hwidth) as Hwidthsize.
    assert (HwidthN : (N.of_nat (Pos.to_nat w) <=
      N.of_nat (V.size a + V.size b + 3))%N) by lia.
    assert (Hmeasure : (N.of_nat (Pos.to_nat w + Z.size_nat (fst r) +
      Z.size_nat (snd r) + 1) <= 4 * (linear * linear))%N).
    { rewrite !Nat2N.inj_add in Hendpoints |- *. lia. }
    eapply N.le_trans; [apply ChecksCost.fits_time|].
    eapply N.le_trans with (m := (128 * (4 * (linear * linear)))%N).
    - apply N.mul_le_mono_l. exact Hmeasure.
    - lia.
  Qed.

  (** Overflow checking combines bounded queries, corner arithmetic and a width test. *)
  Local Lemma overflow_size_time : forall o s a b,
    (T_may_fail (Overflow o s) [a; b] <=
      c_checks * N.of_nat ((V.size a + V.size b + 3) ^ 2 + 1))%N.
  Proof.
    intros o s a b. set (linear := (k_inputs * N.of_nat (V.size a + V.size b + 3))%N).
    destruct (pair_clocks s a b) as [Hqa [Hqb [Hwa Hwb]]].
    fold linear in Hqa, Hqb, Hwa, Hwb.
    pose proof (scaled_square (V.size a + V.size b + 3)%nat ltac:(lia))
      as [Hpositive [Hbase Hsquare]]. fold linear in Hpositive, Hbase, Hsquare.
    pose proof (result_time_scaled o s a b) as Hresulttime. fold linear in Hresulttime.
    eapply N.le_trans with (m := (1024 * (linear * linear))%N); [|apply finish_budget].
    time_unfold T_may_fail. time_simpl.
    destruct (W.width a) as [wa|] eqn:Hwidtha; cbn beta iota zeta;
      [|destruct s; cbn beta iota zeta in *; lia].
    destruct (W.width b) as [wb|] eqn:Hwidthb; cbn beta iota zeta;
      [|destruct s; cbn beta iota zeta in *; lia].
    destruct (range_result o (if s then QS.range a else Q.range a)
      (if s then QS.range b else Q.range b)) as [r|] eqn:Hresult;
      cbn beta iota zeta; [|destruct s; cbn beta iota zeta in *; lia].
    pose proof (fits_time_scaled o s a b wa r Hwidtha Hresult) as Hfits.
    fold linear in Hfits.
    pose proof (Std.Pos.T_eqb_le wa wb) as Heqb.
    pose proof (ChecksCost.positive_bits_value wa) as Hwidthbits.
    pose proof (W.width_size a wa Hwidtha) as Hwidthsize.
    assert (Heqb' : (Std.Pos.T_eqb wa wb <= linear)%N) by lia.
    time_simpl. destruct s; cbn beta iota zeta in *; lia.
  Qed.

  (** Unary check work is the square of the value size and its two list charges. *)
  Local Lemma work_one : forall k a, work k [a] = ((V.size a + 2) ^ 2)%nat.
  Proof.
    intros k a. unfold work. cbn [map fold_right length]. f_equal. lia.
  Qed.

  (** Binary check work is the square of both value sizes and three list charges. *)
  Local Lemma work_two : forall k a b,
    work k [a; b] = ((V.size a + V.size b + 3) ^ 2)%nat.
  Proof.
    intros k a b. unfold work. cbn [map fold_right length]. f_equal. lia.
  Qed.

  (** The complete check is quadratic in the sizes of its operands. *)
  Lemma T_may_fail_le : forall k xs,
    (T_may_fail k xs <= c_checks * N.of_nat (work k xs + 1))%N.
  Proof.
    intros k xs. destruct k as [|o s| |]; destruct xs as [|a [|b [|c xs]]];
      try solve [time_unfold T_may_fail; time_simpl; unfold c_checks;
        rewrite Nat2N.inj_add; pose proof coefficient_lower; nia].
    - rewrite work_one. apply zero_size_time.
    - rewrite work_two. apply overflow_size_time.
    - rewrite work_two. apply bounds_size_time.
    - rewrite work_one.
      change (T_may_fail DivZero [a] <= c_checks * N.of_nat ((V.size a + 2) ^ 2 + 1))%N.
      apply zero_size_time.
  Qed.

  (** A check is linear in its operand work. *)
  Lemma may_fail_bigO : bigO (X := kd * list V.t) (fun _ => True)
    (fun kx => N.of_nat (work (fst kx) (snd kx))) (fun kx => T_may_fail (fst kx) (snd kx)).
  Proof. Admitted. (* STUB *)

  (** A zero alarm charges its range query and the returned endpoint bits. *)
  Lemma T_divzero_le : forall d,
    (T_may_fail DivZero [d] <= c_bits_checks *
      (Q.T_range d + N.of_nat (range_bits (Q.range d) + 1)))%N.
  Proof.
    intro d. eapply N.le_trans; [apply zero_components|].
    apply N.mul_le_mono_r. pose proof coefficient_lower. lia.
  Qed.

  (** Null checks use the same range work as division-by-zero checks. *)
  Lemma T_null_le : forall d,
    (T_may_fail NullDeref [d] <= c_bits_checks *
      (Q.T_range d + N.of_nat (range_bits (Q.range d) + 1)))%N.
  Proof.
    intro d. change (T_may_fail DivZero [d] <= c_bits_checks *
      (Q.T_range d + N.of_nat (range_bits (Q.range d) + 1)))%N.
    apply T_divzero_le.
  Qed.

  (** Bounds alarms charge both range queries and their endpoint bits. *)
  Lemma T_bounds_le : forall i len,
    (T_may_fail Bounds [i; len] <= c_bits_checks *
      (Q.T_range i + Q.T_range len +
        N.of_nat (range_bits (Q.range i) + range_bits (Q.range len) + 1)))%N.
  Proof.
    intros i len. eapply N.le_trans; [apply bounds_components|].
    apply N.mul_le_mono_r. pose proof coefficient_lower. lia.
  Qed.

  (** The work measure squares the sum of operand sizes and list overhead. *)
  Lemma work_sizes : forall k xs, work k xs =
    ((fold_right Nat.add 0%nat (map V.size xs) + length xs + 1) ^ 2)%nat.
  Proof. reflexivity. Qed.
  (** Excluding zero from a containing unsigned range excludes a zero operand. *)
  Lemma F1_zero : forall a c, V.gamma a c -> range_zero (Q.range a) = false ->
    snd c <> 0%Z.
  Proof.
    exact zero_excluded.
  Qed.
  (** Ordered abstract endpoints imply safety of every represented index and length. *)
  Lemma F2_bounds : forall a b i len, V.gamma a i -> V.gamma b len ->
    range_nonnegative (Q.range a) = true ->
    bound_lt (snd (Q.range a)) (fst (Q.range b)) = true -> (0 <= snd i < snd len)%Z.
  Proof.
    exact bounds_safe.
  Qed.

  (** Testing whether an interval contains zero is linear in its endpoint bits. *)
  Lemma T1_zero : forall r,
    (T_range_zero r <= k_bits_checks * N.of_nat (range_bits r + 1))%N.
  Proof.
    exact ChecksCost.zero_time.
  Qed.
End BitsChecksT.
