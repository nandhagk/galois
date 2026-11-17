(** * Total word operations

    Each operation interprets its operands at the supplied width and follows total bitvector
    arithmetic. For example, unsigned division by zero gives the all-ones word.
    Builds on: Word. *)

From Stdlib Require Import ZArith NArith List Lia.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word.
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

Module Pos.
  TimeFun Pos.size.
End Pos.

Module Z.
  TimeFun Z.log2.
End Z.

TimeFun wnot.
TimeFun wneg.
TimeFun wadd.
TimeFun wsub.
TimeFun wmul.
TimeFun wand.
TimeFun wor.
TimeFun wxor.
TimeFun wudiv.
TimeFun wurem.
TimeFun wsdiv.
TimeFun wsrem.
TimeFun wsmod.
TimeFun wshl.
TimeFun wlshr.
TimeFun washr.
TimeFun wrotl.
TimeFun wrotr.
TimeFun wclz.
TimeFun wctz.
TimeFun popcount_pos.
TimeFun popcount.
TimeFun wpopcnt.
TimeFun popcount_steps_pos.
TimeFun wult.
TimeFun wule.
TimeFun wslt.
TimeFun wsle.

(** * Linear operation contracts *)

(** Integer negation preserves magnitude bit length. *)
Lemma integer_opp_size : forall z, Z.size_nat (- z) = Z.size_nat z.
Proof.
  intro z. destruct z; reflexivity.
Qed.

(** Magnitude bit length gives a strict symmetric power-of-two bound. *)
Local Lemma integer_magnitude_bound : forall z,
  (- (2 ^ Z.of_nat (Z.size_nat z)) < z < 2 ^ Z.of_nat (Z.size_nat z))%Z.
Proof.
  intro z. destruct z as [|p|p]; [cbn; lia| |]; cbn [Z.size_nat];
    pose proof (Pos.size_nat_upper p) as Hupper;
    apply Nat2Z.inj_lt in Hupper;
    rewrite positive_nat_Z, Nat2Z.inj_pow in Hupper; lia.
Qed.

(** Addition needs at most one bit beyond the combined operand magnitude budget. *)
Lemma integer_add_size_le : forall x y,
  (Z.size_nat (x + y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros x y. apply integer_abs_size_le.
  pose proof (integer_magnitude_bound x) as Hx.
  pose proof (integer_magnitude_bound y) as Hy.
  assert (Hxp : (0 < 2 ^ Z.of_nat (Z.size_nat x))%Z) by
    (apply Z.pow_pos_nonneg; lia).
  assert (Hyp : (0 < 2 ^ Z.of_nat (Z.size_nat y))%Z) by
    (apply Z.pow_pos_nonneg; lia).
  rewrite !Nat2Z.inj_add. change (Z.of_nat 1%nat) with 1%Z.
  rewrite !Z.pow_add_r by lia. rewrite Z.pow_1_r. nia.
Qed.

(** Subtraction uses the same combined magnitude budget as addition. *)
Lemma integer_sub_size_le : forall x y,
  (Z.size_nat (x - y) <= Z.size_nat x + Z.size_nat y + 1)%nat.
Proof.
  intros x y. pose proof (integer_add_size_le x (- y)) as Hsize.
  rewrite integer_opp_size in Hsize. exact Hsize.
Qed.

(** Complement charges wrapping and two subtractions on values bounded by the word width. *)
Theorem wnot_time_le : forall w x,
  (T_wnot w x <= 128 * N.of_nat (Pos.to_nat w + Z.size_nat x + 1))%N.
Proof.
  intros w x. pose proof (wrap_time_le w x) as Hwrap.
  pose proof (modulus_time_le w) as Hmodulus.
  pose proof (Z.T_sub_le (modulus w) 1) as Hones.
  pose proof (Z.T_sub_le (modulus w - 1) (wrap w x)) as Hsub.
  pose proof (time_of_nat_le _ _ (wrap_size_le w x)) as Hsize.
  pose proof (time_of_nat_le _ _ (modulus_size_le w)) as Hmodsize.
  pose proof (time_of_nat_le _ _
    (Z.size_nat_mono (modulus w - 1) (modulus w)
      ltac:(pose proof (modulus_pos w); lia))) as Honessize.
  time_unfold T_wnot.
  rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
Qed.

(** Modular negation preserves the raw magnitude budget before wrapping. *)
Theorem wneg_time_le : forall w x,
  (T_wneg w x <= 64 * N.of_nat (Pos.to_nat w + Z.size_nat x + 1))%N.
Proof.
  intros w x. pose proof (wrap_time_le w (- x)) as Hwrap.
  pose proof (Z.T_opp_le x) as Hopp. rewrite integer_opp_size in Hwrap.
  time_unfold T_wneg.
  rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
Qed.

(** Modular addition charges a linear width and combined raw operand size budget. *)
Theorem wadd_time_le : forall w x y,
  (T_wadd w x y <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros w x y. pose proof (Z.T_add_le x y) as Hadd.
  pose proof (wrap_time_le w (x + y)) as Hwrap.
  pose proof (time_of_nat_le _ _ (integer_add_size_le x y)) as Hsize.
  time_unfold T_wadd.
  rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
Qed.

(** Modular subtraction charges a linear width and combined raw operand size budget. *)
Theorem wsub_time_le : forall w x y,
  (T_wsub w x y <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros w x y. pose proof (Z.T_sub_le x y) as Hsub.
  pose proof (wrap_time_le w (x - y)) as Hwrap.
  pose proof (time_of_nat_le _ _ (integer_sub_size_le x y)) as Hsize.
  time_unfold T_wsub.
  rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
Qed.

(** Bitwise conjunction normalizes both inputs before traversing at most their word bits. *)
Theorem wand_time_le : forall w x y,
  (T_wand w x y <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros w x y. pose proof (wrap_time_le w x) as Hx.
  pose proof (wrap_time_le w y) as Hy.
  pose proof (Z.T_land_le (wrap w x) (wrap w y)) as Hland.
  pose proof (time_of_nat_le _ _ (wrap_size_le w x)) as Hsx.
  pose proof (time_of_nat_le _ _ (wrap_size_le w y)) as Hsy.
  time_unfold T_wand.
  rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
Qed.

(** Bitwise disjunction normalizes both inputs before traversing at most their word bits. *)
Theorem wor_time_le : forall w x y,
  (T_wor w x y <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros w x y. pose proof (wrap_time_le w x) as Hx.
  pose proof (wrap_time_le w y) as Hy.
  pose proof (Z.T_lor_le (wrap w x) (wrap w y)) as Hlor.
  pose proof (time_of_nat_le _ _ (wrap_size_le w x)) as Hsx.
  pose proof (time_of_nat_le _ _ (wrap_size_le w y)) as Hsy.
  time_unfold T_wor.
  rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
Qed.

(** Exclusive disjunction normalizes both inputs before traversing at most their word bits. *)
Theorem wxor_time_le : forall w x y,
  (T_wxor w x y <=
    128 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros w x y. pose proof (wrap_time_le w x) as Hx.
  pose proof (wrap_time_le w y) as Hy.
  pose proof (Z.T_lxor_le (wrap w x) (wrap w y)) as Hlxor.
  pose proof (time_of_nat_le _ _ (wrap_size_le w x)) as Hsx.
  pose proof (time_of_nat_le _ _ (wrap_size_le w y)) as Hsy.
  time_unfold T_wxor.
  rewrite ?Nat2N.inj_add in *. time_cbn_all. lia.
Qed.
