(** * Range-based bit-vector checks

    Checks use numeric ranges to detect possible bit-vector errors.
    For example, a divisor range excluding zero rules out division by zero.
    Builds on: BitsChecksSig, ChecksSig, BitsLang and ValueSig. *)

From Stdlib Require Import ZArith List Bool.
From Argent Require Import Time.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig ValueSig BitsLang.
From Galois.Alarms Require Import ChecksSig BitsChecksSig.
Import List.ListNotations.

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

  Lemma may_fail_sound : forall k xs cs, may_fail k xs = false ->
    Forall2 V.gamma xs cs -> safe k cs.
  Proof. Admitted. (* STUB *)
  Lemma may_fail_top : forall k n,
    (exists cs, length cs = n /\ ~ safe k cs) -> may_fail k (repeat V.top n) = true.
  Proof. Admitted. (* STUB *)
  Lemma safe_divzero : forall d, safe DivZero [d] <-> snd d <> 0%Z.
  Proof. Admitted. (* STUB *)
  Lemma safe_null : forall p, safe NullDeref [p] <-> snd p <> 0%Z.
  Proof. Admitted. (* STUB *)
  Lemma safe_bounds : forall i len, safe Bounds [i; len] <-> (0 <= snd i < snd len)%Z.
  Proof. Admitted. (* STUB *)
  Lemma safe_overflow : forall o s a b,
    safe (Overflow o s) [a; b] <-> fst a = fst b /\
      exists z, mathematical_result o s a b = Some z /\
      (if s then (- Word.half (fst a) <= z < Word.half (fst a))%Z
       else (0 <= z < Word.modulus (fst a))%Z).
  Proof. Admitted. (* STUB *)
  Lemma result_add : forall s a b, mathematical_result bvadd s a b =
    Some ((if s then NumS.num a else NumU.num a) +
      (if s then NumS.num b else NumU.num b))%Z.
  Proof. Admitted. (* STUB *)
  Lemma result_sub : forall s a b, mathematical_result bvsub s a b =
    Some ((if s then NumS.num a else NumU.num a) -
      (if s then NumS.num b else NumU.num b))%Z.
  Proof. Admitted. (* STUB *)
  Lemma result_mul : forall s a b, mathematical_result bvmul s a b =
    Some ((if s then NumS.num a else NumU.num a) *
      (if s then NumS.num b else NumU.num b))%Z.
  Proof. Admitted. (* STUB *)
  Lemma may_fail_divzero : forall d, may_fail DivZero [d] = range_zero (Q.range d).
  Proof. Admitted. (* STUB *)
  Lemma may_fail_null : forall p, may_fail NullDeref [p] = range_zero (Q.range p).
  Proof. Admitted. (* STUB *)
  Lemma may_fail_bounds : forall i len, may_fail Bounds [i; len] =
    negb (range_nonnegative (Q.range i) && bound_lt (snd (Q.range i)) (fst (Q.range len))).
  Proof. Admitted. (* STUB *)
  Lemma result_other : forall o s a b,
    ~ In o (bvadd :: bvsub :: bvmul :: nil) -> mathematical_result o s a b = None.
  Proof. Admitted. (* STUB *)
  Lemma may_fail_overflow : forall o s a b, may_fail (Overflow o s) [a; b] =
    match W.width a, W.width b,
      range_result o (if s then QS.range a else Q.range a)
        (if s then QS.range b else Q.range b) with
    | Some w, Some v, Some r => negb (Pos.eqb w v && range_fits s w r)
    | _, _, _ => true
    end.
  Proof. Admitted. (* STUB *)
  Lemma may_fail_other : forall k xs,
    match k, xs with
    | DivZero, [_] | NullDeref, [_] | Bounds, [_; _] | Overflow _ _, [_; _] => True
    | _, _ => may_fail k xs = true
    end.
  Proof. Admitted. (* STUB *)
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
  Lemma F1_zero : forall a c, V.gamma a c -> range_zero (Q.range a) = false ->
    snd c <> 0%Z.
  Proof. Admitted. (* STUB *)
  Lemma F2_bounds : forall a b i len, V.gamma a i -> V.gamma b len ->
    range_nonnegative (Q.range a) = true ->
    bound_lt (snd (Q.range a)) (fst (Q.range b)) = true -> (0 <= snd i < snd len)%Z.
  Proof. Admitted. (* STUB *)
  Lemma T1_zero : forall r,
    (T_range_zero r <= k_bits_checks * N.of_nat (range_bits r + 1))%N.
  Proof. Admitted. (* STUB *)
End BitsChecksT.
