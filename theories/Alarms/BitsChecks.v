(** * Range-based bit-vector checks

    Checks use numeric ranges to detect possible bit-vector errors.
    For example, a divisor range excluding zero rules out division by zero.
    Builds on: BitsChecksSig, ChecksSig, BitsLang and ValueSig. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time.
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

Module BitsChecksT (V : VALUE_DOMAIN_T BitsLangT)
    (Q : BITS_RANGE_T NumU V) (QS : BITS_RANGE_T NumS V) (W : BITS_WIDTH_T V)
    <: BITS_CHECKS_ALL V Q QS W.
  Include BitsChecks V Q QS W.
  Definition work (_ : kd) (xs : list V.t) : nat :=
    ((fold_right Nat.add 0%nat (map V.size xs) + length xs + 1) ^ 2)%nat.
  TimeFun may_fail.
  Definition c_bits_checks : N := 1. (* STUB *)
  Definition c_checks : N := c_bits_checks.
  Definition k_bits_checks : N := 1. (* STUB *)
  Lemma T_may_fail_le : forall k xs,
    (T_may_fail k xs <= c_checks * N.of_nat (work k xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_divzero_le : forall d,
    (T_may_fail DivZero [d] <= c_bits_checks *
      (Q.T_range d + N.of_nat (range_bits (Q.range d) + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_null_le : forall d,
    (T_may_fail NullDeref [d] <= c_bits_checks *
      (Q.T_range d + N.of_nat (range_bits (Q.range d) + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_bounds_le : forall i len,
    (T_may_fail Bounds [i; len] <= c_bits_checks *
      (Q.T_range i + Q.T_range len +
        N.of_nat (range_bits (Q.range i) + range_bits (Q.range len) + 1)))%N.
  Proof. Admitted. (* STUB *)
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
  Lemma T1_zero : forall r,
    (T_range_zero r <= k_bits_checks * N.of_nat (range_bits r + 1))%N.
  Proof. Admitted. (* STUB *)
End BitsChecksT.
