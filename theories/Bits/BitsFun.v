(** * Total word operations

    Each operation interprets its operands at the supplied width and follows total bitvector
    arithmetic. For example, unsigned division by zero gives the all-ones word.
    Builds on: BitsWord and Rocq Stdlib integer bit operations. *)

From Stdlib Require Import ZArith List Lia.
From Galois.Bits Require Import BitsWord.

Open Scope Z_scope.

(** Complement flips exactly the bits below the width. *)
Definition wnot (w : width) (x : Z) : Z := modulus w - 1 - wrap w x.

(** Negation computes the additive inverse modulo the word modulus. *)
Definition wneg (w : width) (x : Z) : Z := wrap w (- x).

(** Addition reduces the integer sum to the word range. *)
Definition wadd (w : width) (x y : Z) : Z := wrap w (x + y).

(** Subtraction reduces the integer difference to the word range. *)
Definition wsub (w : width) (x y : Z) : Z := wrap w (x - y).

(** Multiplication reduces the integer product to the word range. *)
Definition wmul (w : width) (x y : Z) : Z := wrap w (x * y).

(** Negation wraps the integer additive inverse for arbitrary operands. *)
Theorem wneg_value : forall w x, wneg w x = wrap w (- x).
Proof.
  intros w x. reflexivity.
Qed.

(** Addition wraps the integer sum for arbitrary operands. *)
Theorem wadd_value : forall w x y, wadd w x y = wrap w (x + y).
Proof.
  intros w x y. reflexivity.
Qed.

(** Subtraction wraps the integer difference for arbitrary operands. *)
Theorem wsub_value : forall w x y, wsub w x y = wrap w (x - y).
Proof.
  intros w x y. reflexivity.
Qed.

(** Multiplication wraps the integer product for arbitrary operands. *)
Theorem wmul_value : forall w x y, wmul w x y = wrap w (x * y).
Proof.
  intros w x y. reflexivity.
Qed.

(** Conjunction acts on the wrapped operands. *)
Definition wand (w : width) (x y : Z) : Z := Z.land (wrap w x) (wrap w y).

(** Disjunction acts on the wrapped operands. *)
Definition wor (w : width) (x y : Z) : Z := Z.lor (wrap w x) (wrap w y).

(** Exclusive disjunction acts on the wrapped operands. *)
Definition wxor (w : width) (x y : Z) : Z := Z.lxor (wrap w x) (wrap w y).

(** Unsigned division by zero returns all ones. *)
Definition wudiv (w : width) (x y : Z) : Z :=
  if wrap w y =? 0 then modulus w - 1 else wrap w x / wrap w y.

(** Unsigned remainder by zero returns the wrapped dividend. *)
Definition wurem (w : width) (x y : Z) : Z :=
  if wrap w y =? 0 then wrap w x else wrap w x mod wrap w y.

(** Signed division uses the SMT-LIB sign cases over unsigned division. *)
Definition wsdiv (w : width) (x y : Z) : Z :=
  match msb w x, msb w y with
  | false, false => wudiv w x y
  | true, false => wneg w (wudiv w (wneg w x) y)
  | false, true => wneg w (wudiv w x (wneg w y))
  | true, true => wudiv w (wneg w x) (wneg w y)
  end.

(** Signed division selects unsigned division and negation from the normalized sign bits. *)
Theorem wsdiv_value : forall w x y,
  wsdiv w x y =
    match msb w x, msb w y with
    | false, false => wudiv w x y
    | true, false => wneg w (wudiv w (wneg w x) y)
    | false, true => wneg w (wudiv w x (wneg w y))
    | true, true => wudiv w (wneg w x) (wneg w y)
    end.
Proof.
  intros w x y. reflexivity.
Qed.

(** Signed remainder has the sign of the dividend. *)
Definition wsrem (w : width) (x y : Z) : Z :=
  match msb w x, msb w y with
  | false, false => wurem w x y
  | true, false => wneg w (wurem w (wneg w x) y)
  | false, true => wurem w x (wneg w y)
  | true, true => wneg w (wurem w (wneg w x) (wneg w y))
  end.

(** Signed remainder selects unsigned remainder and negation from the normalized sign bits. *)
Theorem wsrem_value : forall w x y,
  wsrem w x y =
    match msb w x, msb w y with
    | false, false => wurem w x y
    | true, false => wneg w (wurem w (wneg w x) y)
    | false, true => wurem w x (wneg w y)
    | true, true => wneg w (wurem w (wneg w x) (wneg w y))
    end.
Proof.
  intros w x y. reflexivity.
Qed.

(** Signed modulus has the sign of the divisor when the remainder is nonzero. *)
Definition wsmod (w : width) (x y : Z) : Z :=
  let ax := if msb w x then wneg w x else wrap w x in
  let ay := if msb w y then wneg w y else wrap w y in
  let u := wurem w ax ay in
  match u =? 0, msb w x, msb w y with
  | true, _, _ => u
  | _, false, false => u
  | _, true, false => wadd w (wneg w u) y
  | _, false, true => wadd w u y
  | _, true, true => wneg w u
  end.

(** Signed modulus keeps a zero residue and adjusts nonzero residues using normalized signs. *)
Theorem wsmod_value : forall w x y,
  wsmod w x y =
    let ax := if msb w x then wneg w x else wrap w x in
    let ay := if msb w y then wneg w y else wrap w y in
    let u := wurem w ax ay in
    match u =? 0, msb w x, msb w y with
    | true, _, _ => u
    | _, false, false => u
    | _, true, false => wadd w (wneg w u) y
    | _, false, true => wadd w u y
    | _, true, true => wneg w u
    end.
Proof.
  intros w x y. reflexivity.
Qed.

(** Left shift discards bits above the width and gives zero for large amounts. *)
Definition wshl (w : width) (x y : Z) : Z :=
  if Zpos w <=? wrap w y then 0 else wrap w (wrap w x * 2 ^ wrap w y).

(** Left shift tests the wrapped amount against the width before multiplying. *)
Theorem wshl_value : forall w x y,
  wshl w x y =
    if Zpos w <=? wrap w y then 0 else wrap w (wrap w x * 2 ^ wrap w y).
Proof.
  intros w x y. reflexivity.
Qed.

(** Logical right shift fills with zero and gives zero for large amounts. *)
Definition wlshr (w : width) (x y : Z) : Z :=
  if Zpos w <=? wrap w y then 0 else wrap w x / 2 ^ wrap w y.

(** Logical right shift tests the wrapped amount against the width before dividing. *)
Theorem wlshr_value : forall w x y,
  wlshr w x y =
    if Zpos w <=? wrap w y then 0 else wrap w x / 2 ^ wrap w y.
Proof.
  intros w x y. reflexivity.
Qed.

(** Arithmetic right shift fills with the sign bit. *)
Definition washr (w : width) (x y : Z) : Z :=
  if Zpos w <=? wrap w y then (if msb w x then modulus w - 1 else 0)
  else wrap w (signed w x / 2 ^ wrap w y).

(** Arithmetic right shift uses the normalized sign bit when the wrapped amount is large. *)
Theorem washr_value : forall w x y,
  washr w x y =
    if Zpos w <=? wrap w y then (if msb w x then modulus w - 1 else 0)
    else wrap w (signed w x / 2 ^ wrap w y).
Proof.
  intros w x y. reflexivity.
Qed.

(** Left rotation reduces the shift amount modulo the width. *)
Definition wrotl (w : width) (x y : Z) : Z :=
  let k := wrap w y mod Zpos w in
  wrap w (wrap w x * 2 ^ k + wrap w x / 2 ^ (Zpos w - k)).

(** Right rotation uses the complementary left rotation amount. *)
Definition wrotr (w : width) (x y : Z) : Z :=
  wrotl w x (Zpos w - wrap w y mod Zpos w).

(** Right rotation uses the complementary normalized left-rotation amount. *)
Theorem wrotr_value : forall w x y,
  wrotr w x y = wrotl w x (Zpos w - wrap w y mod Zpos w).
Proof.
  intros w x y. reflexivity.
Qed.

(** Leading-zero count returns the width on zero. *)
Definition wclz (w : width) (x : Z) : Z :=
  if wrap w x =? 0 then Zpos w else Zpos w - 1 - Z.log2 (wrap w x).

(** Trailing-zero count returns the width on zero. *)
Definition wctz (w : width) (x : Z) : Z :=
  if wrap w x =? 0 then Zpos w else Z.log2 (Z.land (wrap w x) (- wrap w x)).

(** Population count traverses the binary digits of a positive integer. *)
Fixpoint popcount_pos (p : positive) : Z :=
  match p with
  | xH => 1
  | xO q => popcount_pos q
  | xI q => 1 + popcount_pos q
  end.

(** Population count is zero on nonpositive integers. *)
Definition popcount (z : Z) : Z :=
  match z with
  | Zpos p => popcount_pos p
  | _ => 0
  end.

(** Population count counts the set bits below the width. *)
Definition wpopcnt (w : width) (x : Z) : Z := popcount (wrap w x).

Local Lemma filter_seq_shift : forall (f : nat -> bool) n start,
  length (filter f (seq (S start) n)) =
    length (filter (fun i => f (S i)) (seq start n)).
Proof.
  intros f n. induction n as [|n IH]; intro start; [reflexivity|].
  cbn [seq filter]. destruct (f (S start)); cbn; now rewrite IH.
Qed.

Local Lemma count_even : forall a n,
  length (filter (fun i => Z.testbit (2 * a) (Z.of_nat i)) (seq 0 (S n))) =
    length (filter (fun i => Z.testbit a (Z.of_nat i)) (seq 0 n)).
Proof.
  intros a n. cbn [seq filter]. rewrite Z.testbit_even_0.
  rewrite filter_seq_shift. f_equal. apply filter_ext. intro i.
  rewrite Nat2Z.inj_succ, Z.testbit_even_succ by lia. reflexivity.
Qed.

Local Lemma count_odd : forall a n,
  length (filter (fun i => Z.testbit (2 * a + 1) (Z.of_nat i)) (seq 0 (S n))) =
    S (length (filter (fun i => Z.testbit a (Z.of_nat i)) (seq 0 n))).
Proof.
  intros a n. cbn [seq filter]. rewrite Z.testbit_odd_0. cbn [length].
  rewrite filter_seq_shift. f_equal. f_equal. apply filter_ext. intro i.
  rewrite Nat2Z.inj_succ, Z.testbit_odd_succ by lia. reflexivity.
Qed.

Local Lemma count_zero : forall n,
  length (filter (fun i => Z.testbit 0 (Z.of_nat i)) (seq 0 n)) = 0%nat.
Proof.
  intro n. generalize (seq 0 n) as xs. intro xs.
  induction xs as [|i xs IH]; [reflexivity|].
  cbn [filter]. rewrite Z.bits_0. exact IH.
Qed.

(** A nonnegative integer below two to the n has exactly its population count in the low n bits. *)
Theorem popcount_testbit : forall n z, 0 <= z < 2 ^ Z.of_nat n ->
  popcount z =
    Z.of_nat (length (filter (fun i => Z.testbit z (Z.of_nat i)) (seq 0 n))).
Proof.
  induction n as [|n IH]; intros z Hz.
  - assert (z = 0) by (cbn in Hz; lia). subst z. reflexivity.
  - destruct z as [|p|p]; [now rewrite count_zero| |lia].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hz by lia.
    destruct p as [p|p|].
    + change (0 <= 2 * Zpos p + 1 < 2 * 2 ^ Z.of_nat n) in Hz.
      rewrite (count_odd (Zpos p)).
      cbn [popcount popcount_pos]. rewrite Nat2Z.inj_succ.
      rewrite <- (IH (Zpos p)) by lia. cbn [popcount]. lia.
    + rewrite (count_even (Zpos p)).
      cbn [popcount popcount_pos]. apply (IH (Zpos p)).
      change (0 <= 2 * Zpos p < 2 * 2 ^ Z.of_nat n) in Hz. lia.
    + change (popcount 1 =
        Z.of_nat (length (filter (fun i => Z.testbit (2 * 0 + 1) (Z.of_nat i))
          (seq 0 (S n))))).
      rewrite count_odd, count_zero. reflexivity.
Qed.

(** Word population count agrees with the filter-count specification of the legacy interface. *)
Theorem wpopcnt_spec : forall w x, wpopcnt w x =
  Z.of_nat (length (filter (fun i => Z.testbit (wrap w x) (Z.of_nat i))
    (seq 0 (Pos.to_nat w)))).
Proof.
  intros w x. apply popcount_testbit.
  rewrite positive_nat_Z. apply wrap_is_word.
Qed.

(** The recursion-step count follows the same positive digit traversal as population count. *)
Fixpoint popcount_steps_pos (p : positive) : nat :=
  match p with
  | xH => 1%nat
  | xO q => S (popcount_steps_pos q)
  | xI q => S (popcount_steps_pos q)
  end.

(** Population count visits exactly one node per binary digit of a positive argument. *)
Theorem popcount_cost : forall p, popcount_steps_pos p = Pos.size_nat p.
Proof.
  intro p. induction p; cbn; congruence.
Qed.

(** Unsigned strict comparison compares the wrapped values. *)
Definition wult (w : width) (x y : Z) : bool := wrap w x <? wrap w y.

(** Unsigned non-strict comparison compares the wrapped values. *)
Definition wule (w : width) (x y : Z) : bool := wrap w x <=? wrap w y.

(** Signed strict comparison compares the signed views. *)
Definition wslt (w : width) (x y : Z) : bool := signed w x <? signed w y.

(** Signed non-strict comparison compares the signed views. *)
Definition wsle (w : width) (x y : Z) : bool := signed w x <=? signed w y.

(** Unsigned strict comparison uses the normalized operands for arbitrary integers. *)
Theorem wult_value : forall w x y, wult w x y = (wrap w x <? wrap w y).
Proof.
  intros w x y. reflexivity.
Qed.

(** Unsigned non-strict comparison uses the normalized operands for arbitrary integers. *)
Theorem wule_value : forall w x y, wule w x y = (wrap w x <=? wrap w y).
Proof.
  intros w x y. reflexivity.
Qed.

(** Signed strict comparison uses the signed interpretations for arbitrary integers. *)
Theorem wslt_value : forall w x y, wslt w x y = (signed w x <? signed w y).
Proof.
  intros w x y. reflexivity.
Qed.

(** Signed non-strict comparison uses the signed interpretations for arbitrary integers. *)
Theorem wsle_value : forall w x y, wsle w x y = (signed w x <=? signed w y).
Proof.
  intros w x y. reflexivity.
Qed.
