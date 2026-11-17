(** * Congruence payload code

    Congruences describe residues of normalized words.
    For example, modulus two and residue zero describe even words.
    Builds on: CongruenceSig and the fixed-width word operations. *)

From Stdlib Require Import ZArith NArith Zpow_facts List Bool Lia Wellfounded.Inverse_Image.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Bits Require Import Word Fun Op Testbit Arith.
From Galois.Domains Require Import CongruenceSig WordSig BitsLang.
Import List.ListNotations.
Local Open Scope Z_scope.

Record congr_crt_state : Type := {
  crt_r1 : Z;
  crt_u1 : Z;
  crt_v1 : Z;
  crt_r2 : Z;
  crt_u2 : Z;
  crt_v2 : Z
}.

(** The Euclidean transition graph records only states and observable terminal triples. *)
Inductive congr_crt_graph (advance : congr_crt_state -> congr_crt_state) :
    congr_crt_state -> (Z * Z * Z) -> Prop :=
  | crt_graph_done : forall s,
      crt_r1 s = 0 -> congr_crt_graph advance s (crt_u2 s, crt_v2 s, crt_r2 s)
  | crt_graph_next : forall s result,
      crt_r1 s <> 0 -> congr_crt_graph advance (advance s) result ->
      congr_crt_graph advance s result.

TimeFun crt_r1.
TimeFun crt_u1.
TimeFun crt_v1.
TimeFun crt_r2.
TimeFun crt_u2.
TimeFun crt_v2.

Module Z.
  TimeFun Z.sgn.
  TimeFun Z.lcm.
End Z.

Module CongruenceCRT.
  (** Each iteration consumes one aligned quotient bit. *)
  Fixpoint div_scan (bits : nat) (divisor remainder quotient : Z) : Z * Z :=
    match bits with
    | O => (quotient, remainder)
    | S rest =>
      let take := (divisor <=? remainder)%Z in
      div_scan rest (Z.div2 divisor)
        (if take then remainder - divisor else remainder)
        (if take then 2 * quotient + 1 else 2 * quotient)
    end.
  TimeFun div_scan.

  Definition div_aligned (a b : Z) : Z * Z :=
    match a, b with
    | Zneg _, _ | _, Zneg _ | _, Z0 => Z.div_eucl a b
    | _, _ =>
      if (a <? b)%Z then (0, a) else
        let shift := (Z.size_nat a - Z.size_nat b)%nat in
        div_scan (S shift) (Z.shiftl b (Z.of_nat shift)) a 0
    end.
  TimeFun div_aligned.

  Definition k_div : N := 256%N.
  Definition k_gcd : N := 32768%N.

  (** Powers indexed by natural successors double. *)
  Lemma pow_nat_succ : forall n,
    2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n.
  Proof.
    intro n. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
  Qed.

  (** Dividing an aligned doubled divisor by two is exact. *)
  Lemma divisor_half : forall b n,
    b * (2 * 2 ^ Z.of_nat n) / 2 = b * 2 ^ Z.of_nat n.
  Proof.
    intros b n.
    replace (b * (2 * 2 ^ Z.of_nat n)) with ((b * 2 ^ Z.of_nat n) * 2) by ring.
    apply Z.div_mul. lia.
  Qed.

  (** The scan preserves the represented dividend and ends with a canonical remainder.
      The initial quotient is generalized because each recursive call shifts it. *)
  Lemma div_scan_spec : forall bits b r q,
    0 < b -> 0 <= r < b * 2 ^ Z.of_nat bits ->
    let qr := div_scan bits (b * 2 ^ Z.of_nat bits / 2) r q in
    0 <= snd qr < b /\
    b * fst qr + snd qr = b * q * 2 ^ Z.of_nat bits + r.
  Proof.
    induction bits as [| bits IH]; intros b r q Hb Hr.
    - cbn [div_scan fst snd].
      rewrite Z.pow_0_r, !Z.mul_1_r in *.
      split; [exact Hr | reflexivity].
    - rewrite pow_nat_succ in Hr |- *.
      rewrite divisor_half.
      cbn [div_scan]. rewrite Z.div2_div.
      destruct (b * 2 ^ Z.of_nat bits <=? r) eqn:Htake.
      + apply Z.leb_le in Htake.
        pose proof (IH b (r - b * 2 ^ Z.of_nat bits) (2 * q + 1)
          Hb ltac:(nia)) as Hscan.
        cbn beta zeta in Hscan |- *.
        destruct Hscan as [Hrange Heq].
        split; [exact Hrange |]. rewrite Heq. ring.
      + apply Z.leb_gt in Htake.
        pose proof (IH b r (2 * q) Hb ltac:(lia)) as Hscan.
        cbn beta zeta in Hscan |- *.
        destruct Hscan as [Hrange Heq].
        split; [exact Hrange |]. rewrite Heq. ring.
  Qed.

  (** A nonnegative integer is below the power given by its bit length. *)
  Lemma size_upper : forall a,
    0 <= a -> a < 2 ^ Z.of_nat (Z.size_nat a).
  Proof.
    intros a Ha. destruct a as [| p | p]; cbn [Z.size_nat]; try lia.
    apply Zpower2_Psize. lia.
  Qed.

  (** A positive integer reaches the preceding power of two. *)
  Lemma size_lower : forall b,
    0 < b -> 2 ^ Z.of_nat (Z.size_nat b - 1) <= b.
  Proof.
    intros b Hb. destruct b as [| p | p]; try lia.
    cbn [Z.size_nat].
    destruct (Z.lt_ge_cases (Z.pos p) (2 ^ Z.of_nat (Pos.size_nat p - 1)))
      as [Hsmall | Hlower]; [| exact Hlower].
    apply Zpower2_Psize in Hsmall.
    pose proof (Pos.size_nat_pos p) as Hsize. lia.
  Qed.

  (** The released alignment always supplies enough quotient bits.
      This stronger version does not need a >= b: truncated subtraction remains safe. *)
  Lemma alignment_bound : forall a b,
    0 <= a -> 0 < b ->
    a < b * 2 ^ Z.of_nat (S (Z.size_nat a - Z.size_nat b)).
  Proof.
    intros a b Ha Hb.
    pose proof (size_upper a Ha) as Hupper.
    pose proof (size_lower b Hb) as Hlower.
    assert (Hsize : (1 <= Z.size_nat b)%nat).
    { destruct b as [| p | p]; try lia. apply Pos.size_nat_pos. }
    assert (Hexponents : (Z.size_nat a <=
      Z.size_nat b - 1 + S (Z.size_nat a - Z.size_nat b))%nat) by lia.
    apply Nat2Z.inj_le in Hexponents.
    rewrite Nat2Z.inj_add in Hexponents.
    pose proof (Z.pow_le_mono_r 2 _ _ ltac:(lia) Hexponents) as Hpowers.
    rewrite Z.pow_add_r in Hpowers by lia.
    pose proof (Z.pow_pos_nonneg 2
      (Z.of_nat (S (Z.size_nat a - Z.size_nat b))) ltac:(lia) ltac:(lia)) as Hpositive.
    nia.
  Qed.

  (** The standard division pair has the usual quotient and remainder projections. *)
  Lemma div_eucl_pair : forall a b,
    Z.div_eucl a b = (a / b, a mod b).
  Proof.
    intros a b. unfold Z.div, Z.modulo.
    destruct (Z.div_eucl a b). reflexivity.
  Qed.

  (** A sufficiently long aligned scan computes standard division. *)
  Lemma scan_agrees : forall bits a b,
    0 < b -> 0 <= a < b * 2 ^ Z.of_nat (S bits) ->
    div_scan (S bits) (b * 2 ^ Z.of_nat bits) a 0 = (a / b, a mod b).
  Proof.
    intros bits a b Hb Ha.
    pose proof (div_scan_spec (S bits) b a 0 Hb Ha) as Hscan.
    rewrite pow_nat_succ, divisor_half in Hscan.
    destruct (div_scan (S bits) (b * 2 ^ Z.of_nat bits) a 0) as [q r] eqn:Hresult.
    cbn [fst snd] in Hscan.
    destruct Hscan as [Hrange Heq].
    assert (Hdivision : a = b * q + r) by nia.
    pose proof (Z.div_unique_pos a b q r Hrange Hdivision) as Hq.
    pose proof (Z.mod_unique_pos a b q r Hrange Hdivision) as Hr.
    now subst q r.
  Qed.


  (** Aligned division keeps the standard quotient and remainder on its input domain. *)
  Lemma div_aligned_def : forall a b, (0 <= a)%Z -> (0 < b)%Z ->
    div_aligned a b = Z.div_eucl a b.
  Proof.
    intros a b Ha Hb.
    destruct a as [| p | p].
    - destruct b as [| q | q]; try lia. reflexivity.
    - destruct b as [| q | q]; try lia.
      cbn [div_aligned].
      destruct (Z.pos p <? Z.pos q) eqn:Hsmall.
      + apply Z.ltb_lt in Hsmall.
        rewrite div_eucl_pair, Z.div_small, Z.mod_small by lia.
        reflexivity.
      + rewrite div_eucl_pair, Z.shiftl_mul_pow2 by lia.
        apply scan_agrees; [lia |].
        split; [lia | apply alignment_bound; lia].
    - lia.
  Qed.

  (** Negative or zero-divisor cases already use the standard fallback. *)
  Lemma div_aligned_all : forall a b,
    div_aligned a b = Z.div_eucl a b.
  Proof.
    intros a b. destruct a as [| p | p], b as [| q | q]; try reflexivity.
    apply div_aligned_def; lia.
  Qed.

  (** Each consumed scan bit pays for at most one additional quotient bit. The other
      two integers only shrink, so this total bit budget is invariant. *)
  Lemma div_scan_time_bound : forall bits d r q n,
    0 <= d -> 0 <= r -> 0 <= q ->
    (Z.size_nat d + Z.size_nat r + Z.size_nat q + bits <= n)%nat ->
    (T_div_scan bits d r q <= 32 * N.of_nat (S bits) * N.of_nat (S n))%N.
  Proof.
    induction bits as [|bits IH]; intros d r q n Hd Hr Hq Hbudget.
    - time_unfold T_div_scan. rewrite !Nat2N.inj_succ. time_cbn_all. nia.
    - assert (Hdhalf : 0 <= Z.div2 d).
      { rewrite Z.div2_div. apply Z.div_pos; lia. }
      pose proof (Z.size_nat_div2 d) as Hdsize.
      pose proof (Z.size_nat_double q Hq) as Hqsize.
      pose proof (Z.T_leb_le d r) as Hcompare.
      pose proof (Z.T_div2_le d) as Hhalf.
      pose proof (Z.T_sub_le r d) as Hsubtract.
      pose proof (Z.T_mul_two_le q) as Hdouble.
      pose proof (Z.T_add_le (2 * q) 1) as Hadd.
      time_unfold T_div_scan. destruct (d <=? r) eqn:Htake.
      + apply Z.leb_le in Htake.
        pose proof (Z.size_nat_mono (r - d) r ltac:(lia)) as Hrsize.
        pose proof (Z.size_nat_succ_double q Hq) as Hqnext.
        pose proof (IH (Z.div2 d) (r - d) (2 * q + 1) n
          Hdhalf ltac:(lia) ltac:(lia) ltac:(lia)) as Htail.
        apply time_of_nat_le in Hbudget. apply time_of_nat_le in Hqsize.
        rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
        time_cbn_all. nia.
      + apply Z.leb_gt in Htake.
        pose proof (IH (Z.div2 d) r (2 * q) n
          Hdhalf Hr ltac:(lia) ltac:(lia)) as Htail.
        apply time_of_nat_le in Hbudget.
        rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
        time_cbn_all. nia.
  Qed.

  (** Reading an integer's magnitude size traverses that many bits. *)
  Lemma integer_size_time_bound : forall z,
    (Word.Z.T_size_nat z <= N.of_nat (Z.size_nat z) + 1)%N.
  Proof.
    intro z. destruct z; time_unfold Word.Z.T_size_nat; cbn [Z.size_nat].
    - reflexivity.
    - pose proof (Pos.T_size_nat_le p). lia.
    - pose proof (Pos.T_size_nat_le p). lia.
  Qed.

  (** Unary subtraction visits no more constructors than its first operand. *)
  Lemma natural_subtract_time_bound : forall n m,
    (Op.Nat.T_sub n m <= N.of_nat n + 1)%N.
  Proof.
    induction n as [|n IH]; intros [|m]; time_unfold Op.Nat.T_sub;
      rewrite ?Nat2N.inj_succ; time_cbn_all; try lia.
    specialize (IH m). lia.
  Qed.

  (** A quadratic unary-to-binary conversion bound fits the alignment setup budget. *)
  Lemma positive_of_succ_time_bound : forall n,
    (Op.Pos.T_of_succ_nat n <= (N.of_nat n + 1) ^ 2)%N.
  Proof.
    induction n as [|n IH].
    - time_unfold Op.Pos.T_of_succ_nat. reflexivity.
    - pose proof (Pos.T_succ_le (Pos.of_succ_nat n)) as Hsucc.
      pose proof (WordTime.positive_size_value (Pos.of_succ_nat n)) as Hsize.
      rewrite SuccNat2Pos.id_succ in Hsize. apply time_of_nat_le in Hsize.
      time_unfold Op.Pos.T_of_succ_nat. rewrite !Nat2N.inj_succ in *.
      time_cbn_all. nia.
  Qed.

  Lemma natural_integer_time_bound : forall n,
    (Op.Z.T_of_nat n <= (N.of_nat n + 1) ^ 2 + 1)%N.
  Proof.
    intros [|n]; time_unfold Op.Z.T_of_nat.
    - time_cbn_all. lia.
    - pose proof (positive_of_succ_time_bound n).
      rewrite Nat2N.inj_succ. time_cbn_all. nia.
  Qed.

  (** Left alignment appends at most the requested number of zero bits. *)
  Lemma aligned_size_bound : forall b n, 0 <= b ->
    (Z.size_nat (Z.shiftl b (Z.of_nat n)) <= Z.size_nat b + n)%nat.
  Proof.
    intros b n Hb. rewrite Z.shiftl_mul_pow2 by lia.
    apply WordTime.integer_size_bound.
    rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    pose proof (size_upper b Hb).
    pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). nia.
  Qed.

  (** The setup and scan polynomials fit a common quotient-bit budget. *)
  Lemma alignment_cost_polynomial : forall a b d : N,
    (b <= a -> d <= a ->
      1 + (a + 4) + ((a + 1) + (b + 1) + (a + 1)) +
        (((d + 1) ^ 2 + 1) + ((b + 5) * d + 1)) +
        32 * (d + 2) * (3 * a + 2) <= 256 * (d + 2) * (a + 1))%N.
  Proof.
    intros a b d Hb Hd.
    assert (Hsquare : (d * d <= d * a)%N) by (apply N.mul_le_mono_l; exact Hd).
    assert (Hproduct : (b * d <= a * d)%N) by (apply N.mul_le_mono_r; exact Hb).
    nia.
  Qed.

  (** Division charges one dividend scan per quotient bit. *)
  Lemma T_div_aligned_le : forall a b, (0 <= a)%Z -> (0 < b)%Z ->
    (T_div_aligned a b <= k_div *
      N.of_nat ((Z.size_nat a - Z.size_nat b + 2) * (Z.size_nat a + 1)))%N.
  Proof.
    intros a b Ha Hb. destruct a as [|p|p], b as [|q|q]; try lia.
    - time_unfold T_div_aligned. cbn [Z.ltb Z.compare Z.size_nat].
      pose proof (Z.T_ltb_le 0 (Zpos q)).
      unfold k_div. time_cbn_all. lia.
    - pose proof (Z.T_ltb_le (Zpos p) (Zpos q)) as Hcompare.
      time_unfold T_div_aligned.
      destruct (Zpos p <? Zpos q) eqn:Hsmall.
      + unfold k_div. rewrite !Nat2N.inj_mul, !Nat2N.inj_add.
        time_cbn_all. nia.
      + apply Z.ltb_ge in Hsmall.
        pose proof (Z.size_nat_mono (Zpos q) (Zpos p) ltac:(lia)) as Hsizes.
        pose proof (aligned_size_bound (Zpos q)
          (Z.size_nat (Zpos p) - Z.size_nat (Zpos q)) ltac:(lia)) as Haligned.
        assert (Hnonnegative : 0 <= Z.shiftl (Zpos q)
          (Z.of_nat (Z.size_nat (Zpos p) - Z.size_nat (Zpos q)))).
        { rewrite Z.shiftl_mul_pow2 by lia.
          pose proof (Z.pow_pos_nonneg 2
            (Z.of_nat (Z.size_nat (Zpos p) - Z.size_nat (Zpos q)))
            ltac:(lia) ltac:(lia)). nia. }
        pose proof (div_scan_time_bound
          (S (Z.size_nat (Zpos p) - Z.size_nat (Zpos q)))
          (Z.shiftl (Zpos q) (Z.of_nat (Z.size_nat (Zpos p) - Z.size_nat (Zpos q))))
          (Zpos p) 0 (3 * Z.size_nat (Zpos p) + 1)
          Hnonnegative ltac:(lia) ltac:(lia)
          ltac:(change (Z.size_nat 0) with 0%nat; lia)) as Hscan.
        pose proof (integer_size_time_bound (Zpos p)) as Hsizea.
        pose proof (integer_size_time_bound (Zpos q)) as Hsizeb.
        pose proof (natural_subtract_time_bound
          (Z.size_nat (Zpos p)) (Z.size_nat (Zpos q))) as Hsubtract.
        pose proof (natural_integer_time_bound
          (Z.size_nat (Zpos p) - Z.size_nat (Zpos q))) as Hconvert.
        pose proof (Z.T_shiftl_le (Zpos q)
          (Z.of_nat (Z.size_nat (Zpos p) - Z.size_nat (Zpos q)))) as Hshift.
        rewrite <- Zabs_nat_N, Zabs2Nat.id in Hshift.
        assert (Hdifference : (Z.size_nat (Zpos p) - Z.size_nat (Zpos q) <=
          Z.size_nat (Zpos p))%nat) by lia.
        apply time_of_nat_le in Hsizes. apply time_of_nat_le in Hdifference.
        unfold k_div. rewrite !Nat2N.inj_mul, !Nat2N.inj_add, !Nat2N.inj_succ in *.
        clear Ha Hb Hsmall Haligned Hnonnegative.
        time_cbn_all.
        pose proof (alignment_cost_polynomial
          (N.of_nat (Pos.size_nat p)) (N.of_nat (Pos.size_nat q))
          (N.of_nat (Pos.size_nat p - Pos.size_nat q)) Hsizes Hdifference).
        lia.
  Qed.

  Definition next (s : congr_crt_state) : congr_crt_state :=
    let q := fst (div_aligned (crt_r2 s) (crt_r1 s)) in
    {| crt_r1 := crt_r2 s - q * crt_r1 s;
       crt_u1 := crt_u2 s - q * crt_u1 s;
       crt_v1 := crt_v2 s - q * crt_v1 s;
       crt_r2 := crt_r1 s;
       crt_u2 := crt_u1 s;
       crt_v2 := crt_v1 s |}.
  TimeFun next.

  Definition lt (s1 s : congr_crt_state) : Prop :=
    (Z.abs_N (crt_r1 s1) < Z.abs_N (crt_r1 s))%N.

  Definition nonnegative_remainders (s : congr_crt_state) : Prop :=
    (0 <= crt_r1 s /\ 0 <= crt_r2 s)%Z.

  (** The first next-state component is the standard Euclidean remainder. *)
  Lemma next_remainder : forall s,
    crt_r1 s <> 0 -> crt_r1 (next s) = crt_r2 s mod crt_r1 s.
  Proof.
    intros s Hnonzero. unfold next. cbn [crt_r1].
    rewrite div_aligned_all, div_eucl_pair.
    cbn [fst]. rewrite Z.mod_eq by exact Hnonzero. ring.
  Qed.


  (** Absolute-value initialization puts both remainders in the aligned division domain. *)
  Lemma initial_nonnegative : forall a b,
    nonnegative_remainders
      {| crt_r1 := Z.abs a; crt_u1 := Z.sgn a; crt_v1 := 0;
         crt_r2 := Z.abs b; crt_u2 := 0; crt_v2 := Z.sgn b |}.
  Proof.
    intros a b. split; apply Z.abs_nonneg.
  Qed.

  (** Every nonterminal reachable step keeps the remainders nonnegative. *)
  Lemma next_nonnegative : forall s, nonnegative_remainders s ->
    (crt_r1 s =? 0) = false -> nonnegative_remainders (next s).
  Proof.
    intros s [Hr1 Hr2] Hnonzero.
    apply Z.eqb_neq in Hnonzero.
    unfold nonnegative_remainders.
    rewrite next_remainder by exact Hnonzero.
    split.
    - pose proof (Z.mod_pos_bound (crt_r2 s) (crt_r1 s) ltac:(lia)). lia.
    - exact Hr1.
  Qed.

  (** The Euclidean remainder strictly reduces the absolute first remainder. *)
  Lemma next_decreases : forall s, (crt_r1 s =? 0) = false -> lt (next s) s.
  Proof.
    intros s Hnonzero. apply Z.eqb_neq in Hnonzero.
    unfold lt. apply N2Z.inj_lt.
    rewrite !N2Z.inj_abs_N, next_remainder by exact Hnonzero.
    apply Z.mod_bound_abs. exact Hnonzero.
  Qed.

  Definition step (s : congr_crt_state) :
      {s1 : congr_crt_state | lt s1 s} + (Z * Z * Z) :=
    (match crt_r1 s =? 0 as doneb return
        (crt_r1 s =? 0) = doneb -> {s1 : congr_crt_state | lt s1 s} + (Z * Z * Z) with
    | true => fun _ => inr (crt_u2 s, crt_v2 s, crt_r2 s)
    | false => fun Hnonzero => inl (exist _ (next s) (next_decreases s Hnonzero))
    end) eq_refl.
  TimeFun step.

  Definition extgcd (a b : Z) : Z * Z * Z :=
    let s := {| crt_r1 := Z.abs a; crt_u1 := Z.sgn a; crt_v1 := 0;
                crt_r2 := Z.abs b; crt_u2 := 0; crt_v2 := Z.sgn b |} in
    loop lt step s
      (Acc_intro_generator 32
        (wf_inverse_image congr_crt_state N N.lt
          (fun st => Z.abs_N (crt_r1 st)) N.lt_wf_0) s).
  TimeFun extgcd.


  Lemma integer_abs_size : forall z, Z.size_nat (Z.abs z) = Z.size_nat z.
  Proof.
    intros []; reflexivity.
  Qed.

  Lemma integer_abs_upper : forall z,
    - (2 ^ Z.of_nat (Z.size_nat z)) < z < 2 ^ Z.of_nat (Z.size_nat z).
  Proof.
    apply WordTime.integer_magnitude_bound.
  Qed.

  Lemma integer_multiply_size : forall x y,
    (Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y)%nat.
  Proof.
    apply WordTime.integer_mul_size.
  Qed.

  Lemma integer_subtract_size : forall x y,
    (Z.size_nat (x - y) <= Nat.max (Z.size_nat x) (Z.size_nat y) + 1)%nat.
  Proof.
    intros x y. apply WordTime.integer_abs_size_bound.
    rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    change (2 ^ Z.of_nat 1) with 2.
    pose proof (integer_abs_upper x) as Hx.
    pose proof (integer_abs_upper y) as Hy.
    pose proof (Z.pow_le_mono_r 2 (Z.of_nat (Z.size_nat x))
      (Z.of_nat (Nat.max (Z.size_nat x) (Z.size_nat y))) ltac:(lia)
      ltac:(apply Nat2Z.inj_le; apply Nat.le_max_l)) as Hpx.
    pose proof (Z.pow_le_mono_r 2 (Z.of_nat (Z.size_nat y))
      (Z.of_nat (Nat.max (Z.size_nat x) (Z.size_nat y))) ltac:(lia)
      ltac:(apply Nat2Z.inj_le; apply Nat.le_max_r)) as Hpy.
    lia.
  Qed.

  Lemma positive_integer_size : forall z, 0 < z -> (1 <= Z.size_nat z)%nat.
  Proof.
    intros [|p|p] Hz; try lia. apply Pos.size_nat_pos.
  Qed.

  Lemma quotient_size_bound : forall a b, 0 <= a -> 0 < b ->
    (Z.size_nat (a / b) <= S (Z.size_nat a - Z.size_nat b))%nat.
  Proof.
    intros a b Ha Hb. apply WordTime.integer_size_bound.
    pose proof (Z.div_pos a b Ha Hb) as Hq.
    pose proof (Z.div_mod a b ltac:(lia)) as Hdivision.
    pose proof (Z.mod_pos_bound a b Hb) as Hremainder.
    pose proof (alignment_bound a b Ha Hb) as Haligned. split; [exact Hq|nia].
  Qed.

  Lemma remainder_size_drop : forall a b, 0 < b <= a ->
    (Z.size_nat (a mod b) < Z.size_nat a)%nat.
  Proof.
    intros a b Hb. pose proof (Z.mod_pos_bound a b ltac:(lia)) as Hr.
    pose proof (Z.div_str_pos a b Hb) as Hq.
    pose proof (Z.div_mod a b ltac:(lia)) as Hdivision.
    pose proof (Z.size_nat_mono (2 * (a mod b)) a ltac:(nia)) as Hsize.
    destruct (a mod b) as [|p|p] eqn:Hremainder.
    - apply positive_integer_size. lia.
    - change (S (Pos.size_nat p) <= Z.size_nat a)%nat in Hsize. exact Hsize.
    - lia.
  Qed.

  Lemma division_bit_budget : forall a b, 0 <= a -> 0 < b ->
    let before := (Z.size_nat b + Z.size_nat a + if (a <? b)%Z then 1 else 0)%nat in
    let after := (Z.size_nat b + Z.size_nat (a mod b))%nat in
    (after < before /\
     Z.size_nat (a / b) <= 2 * (before - after) /\
     Z.size_nat a - Z.size_nat b + 2 <= 3 * (before - after))%nat.
  Proof.
    intros a b Ha Hb. cbn beta zeta. destruct (a <? b) eqn:Hsmall.
    - apply Z.ltb_lt in Hsmall. rewrite Z.mod_small, Z.div_small by lia.
      pose proof (Z.size_nat_mono a b ltac:(lia)) as Hsizes.
      change (Z.size_nat 0) with 0%nat. repeat split; lia.
    - apply Z.ltb_ge in Hsmall.
      pose proof (remainder_size_drop a b ltac:(lia)) as Hdrop.
      pose proof (Z.mod_pos_bound a b Hb) as Hremainder.
      pose proof (Z.size_nat_mono (a mod b) b ltac:(lia)) as Hrsize.
      pose proof (quotient_size_bound a b Ha Hb) as Hqsize.
      repeat split; lia.
  Qed.


  (** The flag pays for a possible initial zero-quotient swap. After every transition,
      the second remainder is at least the first, and the flag is zero. *)
  Definition remainder_bits s :=
    (Z.size_nat (crt_r1 s) + Z.size_nat (crt_r2 s) +
      if (crt_r2 s <? crt_r1 s)%Z then 1 else 0)%nat.

  Lemma next_remainder_bits : forall s, 0 < crt_r1 s ->
    remainder_bits (next s) = (Z.size_nat (crt_r1 s) +
      Z.size_nat (crt_r2 s mod crt_r1 s))%nat.
  Proof.
    intros s Hr1. unfold remainder_bits.
    rewrite next_remainder by lia.
    change (crt_r2 (next s)) with (crt_r1 s).
    pose proof (Z.mod_pos_bound (crt_r2 s) (crt_r1 s) Hr1) as Hremainder.
    rewrite (proj2 (Z.ltb_ge (crt_r1 s) (crt_r2 s mod crt_r1 s)) ltac:(lia)). lia.
  Qed.

  Lemma next_bit_budget : forall s, nonnegative_remainders s -> crt_r1 s <> 0 ->
    let delta := (remainder_bits s - remainder_bits (next s))%nat in
    (remainder_bits (next s) < remainder_bits s /\
     Z.size_nat (crt_r2 s / crt_r1 s) <= 2 * delta /\
     Z.size_nat (crt_r2 s) - Z.size_nat (crt_r1 s) + 2 <= 3 * delta)%nat.
  Proof.
    intros s [Hr1 Hr2] Hnonzero. cbn beta zeta.
    pose proof (division_bit_budget (crt_r2 s) (crt_r1 s) Hr2 ltac:(lia)) as Hbudget.
    cbn beta zeta in Hbudget.
    fold (remainder_bits s) in Hbudget.
    rewrite <- (next_remainder_bits s ltac:(lia)) in Hbudget. exact Hbudget.
  Qed.

  (** A decrease of delta remainder bits permits at most 3*delta coefficient bits. *)
  Lemma coefficient_budget : forall n before after q x y,
    (after <= before)%nat ->
    (Z.size_nat q + 1 <= 3 * (before - after))%nat ->
    (Z.size_nat x + 3 * before <= 3 * n + 1)%nat ->
    (Z.size_nat y + 3 * before <= 3 * n + 1)%nat ->
    (Z.size_nat (y - q * x) + 3 * after <= 3 * n + 1)%nat.
  Proof.
    intros n before after q x y Hafter Hq Hx Hy.
    pose proof (integer_multiply_size q x) as Hproduct.
    pose proof (integer_subtract_size y (q * x)) as Hsubtract.
    destruct (Nat.le_ge_cases (Z.size_nat y) (Z.size_nat (q * x))) as [Hle|Hge].
    - rewrite Nat.max_r in Hsubtract by exact Hle. lia.
    - rewrite Nat.max_l in Hsubtract by exact Hge. lia.
  Qed.

  Definition state_budget n s : Prop :=
    nonnegative_remainders s /\
    (remainder_bits s <= n /\
     Z.size_nat (crt_u1 s) + 3 * remainder_bits s <= 3 * n + 1 /\
     Z.size_nat (crt_v1 s) + 3 * remainder_bits s <= 3 * n + 1 /\
     Z.size_nat (crt_u2 s) + 3 * remainder_bits s <= 3 * n + 1 /\
     Z.size_nat (crt_v2 s) + 3 * remainder_bits s <= 3 * n + 1)%nat.

  Lemma next_state_budget : forall n s,
    state_budget n s -> crt_r1 s <> 0 -> state_budget n (next s).
  Proof.
    intros n s [Hnonnegative [Hmeasure [Hu1 [Hv1 [Hu2 Hv2]]]]] Hnonzero.
    destruct (next_bit_budget s Hnonnegative Hnonzero) as [Hdrop [Hq Halign]].
    assert (Hqcharge : (Z.size_nat (crt_r2 s / crt_r1 s) + 1 <=
      3 * (remainder_bits s - remainder_bits (next s)))%nat) by lia.
    unfold state_budget. split.
    - apply next_nonnegative; [exact Hnonnegative|now apply Z.eqb_neq].
    - split; [lia|]. repeat split.
      + change (Z.size_nat (crt_u2 s -
          fst (div_aligned (crt_r2 s) (crt_r1 s)) * crt_u1 s) +
          3 * remainder_bits (next s) <= 3 * n + 1)%nat.
        rewrite div_aligned_all, div_eucl_pair. cbn [fst].
        eapply (coefficient_budget n (remainder_bits s)); eassumption || lia.
      + change (Z.size_nat (crt_v2 s -
          fst (div_aligned (crt_r2 s) (crt_r1 s)) * crt_v1 s) +
          3 * remainder_bits (next s) <= 3 * n + 1)%nat.
        rewrite div_aligned_all, div_eucl_pair. cbn [fst].
        eapply (coefficient_budget n (remainder_bits s)); eassumption || lia.
      + change (Z.size_nat (crt_u1 s) + 3 * remainder_bits (next s) <= 3 * n + 1)%nat.
        lia.
      + change (Z.size_nat (crt_v1 s) + 3 * remainder_bits (next s) <= 3 * n + 1)%nat.
        lia.
  Qed.

  Lemma initial_state_budget : forall a b,
    state_budget (Z.size_nat a + Z.size_nat b + 1)
      {| crt_r1 := Z.abs a; crt_u1 := Z.sgn a; crt_v1 := 0;
         crt_r2 := Z.abs b; crt_u2 := 0; crt_v2 := Z.sgn b |}.
  Proof.
    intros a b. unfold state_budget. split; [apply initial_nonnegative|].
    unfold remainder_bits. cbn [crt_r1 crt_u1 crt_v1 crt_r2 crt_u2 crt_v2].
    rewrite !integer_abs_size.
    assert (Ha : (Z.size_nat (Z.sgn a) <= 1)%nat).
    { destruct a; cbn [Z.sgn Z.size_nat Pos.size_nat]; lia. }
    assert (Hb : (Z.size_nat (Z.sgn b) <= 1)%nat).
    { destruct b; cbn [Z.sgn Z.size_nat Pos.size_nat]; lia. }
    change (Z.size_nat 0) with 0%nat.
    destruct (Z.abs b <? Z.abs a); repeat split; lia.
  Qed.

  (** Each state component has a linear input-bit bound. *)
  Lemma state_component_sizes : forall n s, state_budget n s ->
    (Z.size_nat (crt_r1 s) <= n /\ Z.size_nat (crt_r2 s) <= n /\
     Z.size_nat (crt_u1 s) <= 3 * n + 1 /\ Z.size_nat (crt_v1 s) <= 3 * n + 1 /\
     Z.size_nat (crt_u2 s) <= 3 * n + 1 /\ Z.size_nat (crt_v2 s) <= 3 * n + 1)%nat.
  Proof.
    intros n s [_ [Hmeasure [Hu1 [Hv1 [Hu2 Hv2]]]]].
    unfold remainder_bits in Hmeasure.
    destruct (crt_r2 s <? crt_r1 s); repeat split; lia.
  Qed.

  (** Quotients stay on the left of multiplication, so quotient bits pay the repeated work. *)
  Lemma coefficient_multiply_time : forall n delta q x,
    (1 <= delta <= n)%nat -> (Z.size_nat q <= 2 * delta)%nat ->
    (Z.size_nat x <= 3 * n + 1)%nat ->
    (Z.T_mul q x <= 32 * N.of_nat (n + 1) * N.of_nat delta)%N.
  Proof.
    intros n delta q x [Hpositive Hdelta] Hq Hx.
    apply time_of_nat_le in Hpositive. apply time_of_nat_le in Hdelta.
    apply time_of_nat_le in Hq. apply time_of_nat_le in Hx.
    pose proof (Z.T_mul_le q x) as Hmultiply.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. time_cbn_all.
    eapply N.le_trans; [exact Hmultiply|].
    eapply N.le_trans with (m := ((3 * N.of_nat delta) * (8 * (N.of_nat n + 1)))%N).
    - apply N.mul_le_mono; lia.
    - nia.
  Qed.

  Lemma coefficient_subtract_time : forall n x y,
    (Z.size_nat x <= 3 * n + 1)%nat -> (Z.size_nat y <= 5 * n + 1)%nat ->
    (Z.T_sub x y <= 32 * N.of_nat (n + 1))%N.
  Proof.
    intros n x y Hx Hy. pose proof (Z.T_sub_le x y) as Hsubtract.
    apply time_of_nat_le in Hx. apply time_of_nat_le in Hy.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. time_cbn_all. lia.
  Qed.

  Lemma division_time_budget : forall n delta a b, 0 <= a -> 0 < b ->
    (Z.size_nat a <= n)%nat ->
    (Z.size_nat a - Z.size_nat b + 2 <= 3 * delta)%nat ->
    (T_div_aligned a b <= 768 * N.of_nat (n + 1) * N.of_nat delta)%N.
  Proof.
    intros n delta a b Ha Hb Hsize Halignment.
    pose proof (T_div_aligned_le a b Ha Hb) as Hdivision.
    apply time_of_nat_le in Hsize. apply time_of_nat_le in Halignment.
    unfold k_div in Hdivision.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. time_cbn_all.
    eapply N.le_trans; [exact Hdivision|].
    change (256 * ((N.of_nat (Z.size_nat a - Z.size_nat b) + 2) *
      (N.of_nat (Z.size_nat a) + 1)) <=
      768 * (N.of_nat n + 1) * N.of_nat delta)%N.
    replace (768 * (N.of_nat n + 1) * N.of_nat delta)%N with
      (256 * ((3 * N.of_nat delta) * (N.of_nat n + 1)))%N by nia.
    apply N.mul_le_mono_l. apply N.mul_le_mono; lia.
  Qed.

  (** The bit-length decrease pays the entire state transition. *)
  Lemma next_time_budget : forall n s, state_budget n s -> crt_r1 s <> 0 ->
    (T_next s <= 1024 * N.of_nat (n + 1) *
      N.of_nat (remainder_bits s - remainder_bits (next s)))%N.
  Proof.
    intros n s Hstate Hnonzero.
    destruct Hstate as [Hnonnegative Hrest].
    destruct Hrest as [Hmeasure Hcoefficients].
    destruct (next_bit_budget s Hnonnegative Hnonzero) as [Hdrop [Hquotient Halignment]].
    destruct (state_component_sizes n s (conj Hnonnegative (conj Hmeasure Hcoefficients)))
      as [Hr1 [Hr2 [Hu1 [Hv1 [Hu2 Hv2]]]]].
    set (delta := (remainder_bits s - remainder_bits (next s))%nat) in *.
    assert (Hdelta : (1 <= delta <= n)%nat) by (unfold delta; lia).
    destruct Hnonnegative as [Hnonnegative1 Hnonnegative2].
    pose proof (division_time_budget n delta (crt_r2 s) (crt_r1 s)
      Hnonnegative2 ltac:(lia) Hr2 Halignment) as Hdivision.
    pose proof (coefficient_multiply_time n delta (crt_r2 s / crt_r1 s)
      (crt_r1 s) Hdelta Hquotient ltac:(lia)) as Hmulr.
    pose proof (coefficient_multiply_time n delta (crt_r2 s / crt_r1 s)
      (crt_u1 s) Hdelta Hquotient Hu1) as Hmulu.
    pose proof (coefficient_multiply_time n delta (crt_r2 s / crt_r1 s)
      (crt_v1 s) Hdelta Hquotient Hv1) as Hmulv.
    pose proof (integer_multiply_size (crt_r2 s / crt_r1 s) (crt_r1 s)) as Hprodr.
    pose proof (integer_multiply_size (crt_r2 s / crt_r1 s) (crt_u1 s)) as Hprodu.
    pose proof (integer_multiply_size (crt_r2 s / crt_r1 s) (crt_v1 s)) as Hprodv.
    pose proof (coefficient_subtract_time n (crt_r2 s)
      ((crt_r2 s / crt_r1 s) * crt_r1 s) ltac:(lia) ltac:(lia)) as Hsubr.
    pose proof (coefficient_subtract_time n (crt_u2 s)
      ((crt_r2 s / crt_r1 s) * crt_u1 s) Hu2 ltac:(lia)) as Hsubu.
    pose proof (coefficient_subtract_time n (crt_v2 s)
      ((crt_r2 s / crt_r1 s) * crt_v1 s) Hv2 ltac:(lia)) as Hsubv.
    assert (Hpositive : (1 <= N.of_nat delta)%N).
    { change (N.of_nat 1 <= N.of_nat delta)%N. apply time_of_nat_le. lia. }
    assert (Hwidth : (1 <= N.of_nat (n + 1))%N).
    { rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. lia. }
    assert (Hunit : (N.of_nat (n + 1) <= N.of_nat (n + 1) * N.of_nat delta)%N) by nia.
    assert (Hproduct : (1 <= N.of_nat (n + 1) * N.of_nat delta)%N) by nia.
    time_unfold T_next. rewrite div_aligned_all, div_eucl_pair. cbn [fst].
    unfold T_crt_r1, T_crt_r2, T_crt_u1, T_crt_u2, T_crt_v1, T_crt_v2.
    unfold Datatypes.T_fst. lia.
  Qed.

  (** The proof argument of the dependent branch has no observable timing effect. *)
  Lemma nonzero_step_time : forall s, crt_r1 s <> 0 ->
    T_step s = (2 + Z.T_eqb (crt_r1 s) 0 + T_next s)%N.
  Proof.
    intros [r1 u1 v1 r2 u2 v2] Hnonzero. destruct r1; [contradiction| |];
      time_unfold T_step; cbn [crt_r1 Z.eqb]; unfold T_crt_r1; lia.
  Qed.

  Lemma step_time_budget : forall n s, state_budget n s -> crt_r1 s <> 0 ->
    (T_step s <= 2048 * N.of_nat (n + 1) *
      N.of_nat (remainder_bits s - remainder_bits (next s)))%N.
  Proof.
    intros n s Hstate Hnonzero. rewrite nonzero_step_time by exact Hnonzero.
    pose proof (next_time_budget n s Hstate Hnonzero) as Hnext.
    pose proof (Z.T_eqb_le (crt_r1 s) 0) as Hcompare.
    destruct (state_component_sizes n s Hstate) as [Hr1 Hrest].
    destruct Hstate as [Hnonnegative [Hmeasure Hcoefficients]].
    destruct (next_bit_budget s Hnonnegative Hnonzero) as [Hdrop Hbits].
    assert (Hpositive : (1 <= N.of_nat (remainder_bits s - remainder_bits (next s)))%N).
    { change (N.of_nat 1 <= N.of_nat (remainder_bits s - remainder_bits (next s)))%N.
      apply time_of_nat_le. lia. }
    apply time_of_nat_le in Hr1.
    assert (Hunit : (N.of_nat (n + 1) <= N.of_nat (n + 1) *
      N.of_nat (remainder_bits s - remainder_bits (next s)))%N) by nia.
    rewrite Nat2N.inj_add in *. change (N.of_nat 1) with 1%N in *. lia.
  Qed.

  Lemma zero_step_time : forall s, crt_r1 s = 0 -> (T_step s <= 6)%N.
  Proof.
    intros [r1 u1 v1 r2 u2 v2] Hzero. cbn [crt_r1] in Hzero. subst r1.
    pose proof (Z.T_eqb_le 0 0).
    time_unfold T_step. cbn [crt_r1 Z.eqb].
    unfold T_crt_r1, T_crt_u2, T_crt_v2, T_crt_r2.
    change (Z.size_nat 0) with 0%nat in *. time_cbn_all. lia.
  Qed.


  (** Continuing branches expose their next state without identifying proof fields. *)
  Lemma continuing_step : forall s s1 Hlt,
    step s = inl (exist _ s1 Hlt) -> crt_r1 s <> 0 /\ s1 = next s.
  Proof.
    intros [r1 u1 v1 r2 u2 v2] s1 Hlt Hstep. destruct r1;
      cbn [step crt_r1] in Hstep; [discriminate| |].
    - split; [discriminate|]. injection Hstep as Hpair.
      symmetry. exact Hpair.
    - split; [discriminate|]. injection Hstep as Hpair.
      symmetry. exact Hpair.
  Qed.

  Lemma stopping_step : forall s result, step s = inr result -> crt_r1 s = 0.
  Proof.
    intros [r1 u1 v1 r2 u2 v2] result Hstep. destruct r1;
      cbn [step crt_r1] in Hstep; [reflexivity|discriminate|discriminate].
  Qed.

  (** A linear input-bit factor times the remaining bit measure pays every loop step. *)
  Lemma loop_time_budget : forall n s (Hacc : Acc lt s), state_budget n s ->
    (T_loop lt step T_step s Hacc <=
      4096 * N.of_nat (n + 1) * N.of_nat (remainder_bits s) + 6 + 1)%N.
  Proof.
    intro n.
    apply (T_loop_le lt step T_step (state_budget n)
      (fun s => (4096 * N.of_nat (n + 1) * N.of_nat (remainder_bits s))%N) 6).
    - intros s s1 Hlt Hstate Hstep.
      destruct (continuing_step s s1 Hlt Hstep) as [Hnonzero ->].
      split; [now apply next_state_budget|].
      pose proof (step_time_budget n s Hstate Hnonzero) as Hcost.
      destruct (next_bit_budget s (proj1 Hstate) Hnonzero) as [Hdrop Hbits].
      assert (Hdecomposition : (N.of_nat (remainder_bits s) =
        N.of_nat (remainder_bits (next s)) +
        N.of_nat (remainder_bits s - remainder_bits (next s)))%N).
      { rewrite <- Nat2N.inj_add. f_equal. lia. }
      assert (Hpositive :
        (1 <= N.of_nat (remainder_bits s - remainder_bits (next s)))%N).
      { change (N.of_nat 1 <= N.of_nat (remainder_bits s - remainder_bits (next s)))%N.
        apply time_of_nat_le. lia. }
      assert (Hwidth : (1 <= N.of_nat (n + 1))%N).
      { rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. lia. }
      assert (Hsavings :
        (2048 * N.of_nat (n + 1) *
          N.of_nat (remainder_bits s - remainder_bits (next s)) <
         4096 * N.of_nat (n + 1) *
          N.of_nat (remainder_bits s - remainder_bits (next s)))%N).
      { clear - Hpositive Hwidth. nia. }
      rewrite Hdecomposition, N.mul_add_distr_l. lia.
    - intros s result Hstate Hstep. apply zero_step_time.
      now apply (stopping_step s result).
  Qed.

  Lemma sign_time_bound : forall z, (Z.T_sgn z <= 1)%N.
  Proof.
    intros []; time_unfold Z.T_sgn; reflexivity.
  Qed.

  Lemma extgcd_cost_polynomial : forall n m : N,
    (1 <= n -> m <= n -> 12 + 4096 * (n + 1) * m <= 32768 * n ^ 2)%N.
  Proof.
    intros n m Hpositive Hsize.
    assert (Hproduct : ((n + 1) * m <= (2 * n) * n)%N).
    { apply N.mul_le_mono; lia. }
    nia.
  Qed.


  (** The full Euclidean coefficient chain has quadratic input-bit work. *)
  Lemma T_extgcd_le : forall a b,
    (T_extgcd a b <= k_gcd *
      N.of_nat ((Z.size_nat a + Z.size_nat b + 1) ^ 2))%N.
  Proof.
    intros a b. set (n := (Z.size_nat a + Z.size_nat b + 1)%nat).
    pose proof (initial_state_budget a b) as Hstate. fold n in Hstate.
    pose proof (proj1 (proj2 Hstate)) as Hmeasure.
    pose proof (Z.T_abs_le a) as Habs_a.
    pose proof (Z.T_abs_le b) as Habs_b.
    pose proof (sign_time_bound a) as Hsign_a.
    pose proof (sign_time_bound b) as Hsign_b.
    time_unfold T_extgcd. cbn beta zeta.
    match goal with
    | |- context [@T_loop _ _ _ _ _ ?seed ?acc] =>
      pose proof (loop_time_budget n seed acc Hstate) as Hloop
    end.
    apply time_of_nat_le in Hmeasure.
    assert (Hpositive : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. apply time_of_nat_le. unfold n. lia. }
    pose proof (extgcd_cost_polynomial (N.of_nat n)
      (N.of_nat (remainder_bits
        {| crt_r1 := Z.abs a; crt_u1 := Z.sgn a; crt_v1 := 0;
           crt_r2 := Z.abs b; crt_u2 := 0; crt_v2 := Z.sgn b |}))
      Hpositive Hmeasure) as Hpolynomial.
    unfold k_gcd. fold n. rewrite Nat2N.inj_pow.
    rewrite Nat2N.inj_add in Hloop.
    change (N.of_nat 1) with 1%N in Hloop. change (N.of_nat 2) with 2%N.
    change (fun s => T_step s) with T_step.
    clear Hstate. lia.
  Qed.


  Definition graph := congr_crt_graph next.

  (** A fixed Euclid state has at most one terminal result. *)
  Lemma graph_deterministic : forall s left right,
    graph s left -> graph s right -> left = right.
  Proof.
    intros s left right Hleft. revert right.
    induction Hleft as [s Hzero | s result Hnonzero Htail IH]; intros right Hright.
    - inversion Hright as [s' Hzero' | s' result' Hnonzero' Htail']; subst.
      + reflexivity.
      + contradiction.
    - inversion Hright as [s' Hzero' | s' result' Hnonzero' Htail']; subst.
      + contradiction.
      + apply IH. exact Htail'.
  Qed.

  (** Every accessibility proof drives the released loop to a graph result. *)
  Lemma loop_graph : forall s (Hacc : Acc lt s),
    graph s (loop lt step s Hacc).
  Proof.
    intros s Hacc.
    induction Hacc as [s Hacc IH] using Acc_ind_dep.
    destruct s as [r1 u1 v1 r2 u2 v2].
    destruct r1 as [| p | p]; cbn [loop step crt_r1 crt_u2 crt_v2 crt_r2].
    - apply crt_graph_done. reflexivity.
    - apply crt_graph_next; [discriminate | apply IH].
    - apply crt_graph_next; [discriminate | apply IH].
  Qed.

  (** The terminal coefficients retain the linear bit bounds of the state invariant. *)
  Definition result_budget n result : Prop :=
    let '(u, v, d) := result in
    (Z.size_nat u <= 3 * n + 1 /\ Z.size_nat v <= 3 * n + 1 /\ Z.size_nat d <= n)%nat.

  Lemma graph_result_budget : forall n s result, graph s result ->
    state_budget n s -> result_budget n result.
  Proof.
    intros n s result Hgraph. induction Hgraph as [s Hzero|s result Hnonzero Htail IH];
      intro Hstate.
    - unfold result_budget.
      destruct (state_component_sizes n s Hstate) as [_ [Hd [_ [_ [Hu Hv]]]]].
      repeat split; assumption.
    - apply IH. now apply next_state_budget.
  Qed.

  Lemma extgcd_result_budget : forall a b,
    result_budget (Z.size_nat a + Z.size_nat b + 1) (extgcd a b).
  Proof.
    intros a b. unfold extgcd. eapply graph_result_budget.
    - apply loop_graph.
    - apply initial_state_budget.
  Qed.


  (** A well-founded fixpoint preserves any observation respected by its functional.
      The observation may project a dependent result; no proof-field equality is used. *)
  Lemma fix_f_preserves
      (A : Type) (R : A -> A -> Prop) (B : A -> Type)
      (F : forall x, (forall y, R y x -> B y) -> B x)
      (P : forall x, B x -> Prop)
      (Hstep : forall x rec,
        (forall y (Hlt : R y x), P y (rec y Hlt)) -> P x (F x rec)) :
    forall x (Hacc : Acc R x), P x (@Fix_F A R B F x Hacc).
  Proof.
    intros x Hacc.
    induction Hacc as [x Hacc IH] using Acc_ind_dep.
    cbn [Fix_F]. apply Hstep. exact IH.
  Qed.

  (** This is the unchanged invariant type carried by Stdlib's extgcd_rec. *)
  Definition standard_invariant a b r1 u1 v1 r2 u2 v2 :=
    True -> 0 <= r1 /\ 0 <= r2 /\
      r1 = u1 * a + v1 * b /\ r2 = u2 * a + v2 * b /\
      Z.gcd r1 r2 = Z.gcd a b.

  (** This is the unchanged result type returned by Stdlib's extgcd_rec. *)
  Definition standard_result a b :=
    { '(u, v, d) | True -> u * a + v * b = d /\ d = Z.gcd a b }.

  (** The Fix_F motive generalizes all changing coefficients and invariant witnesses. *)
  Definition standard_graph_property a b r1
      (rec : forall u1 v1 r2 u2 v2,
        standard_invariant a b r1 u1 v1 r2 u2 v2 ->
        standard_result a b) : Prop :=
    forall u1 v1 r2 u2 v2 Hinvariant,
      graph
        {| crt_r1 := r1; crt_u1 := u1; crt_v1 := v1;
           crt_r2 := r2; crt_u2 := u2; crt_v2 := v2 |}
        (proj1_sig (rec u1 v1 r2 u2 v2 Hinvariant)).

  (** Stdlib's recursion follows the same ordered state transitions. *)
  Lemma standard_extgcd_graph : forall a b,
    graph
      {| crt_r1 := Z.abs a; crt_u1 := Z.sgn a; crt_v1 := 0;
         crt_r2 := Z.abs b; crt_u2 := 0; crt_v2 := Z.sgn b |}
      (Z.extgcd a b).
  Proof.
    intros a b. unfold Z.extgcd, Zdivisibility.Z.extgcd_rec, Fix.
    (* Retain the invariant proof arguments without comparing their proof fields. *)
    match goal with
    | |- graph _
        (proj1_sig (@Fix_F ?A ?R ?B ?F ?r1 ?Hacc ?u1 ?v1 ?r2 ?u2 ?v2 ?Hinitial)) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : standard_graph_property a b r1
        (@Fix_F A R B F r1 Hacc));
      [ apply fix_f_preserves
      | exact (Hrun u1 v1 r2 u2 v2 Hinitial) ]
    end.
    intros r1 rec Hrec.
    unfold standard_graph_property in Hrec |- *.
    intros u1 v1 r2 u2 v2 Hinvariant.
    cbn beta iota zeta.
    destruct (Z.eq_dec r1 0) as [Hzero | Hnonzero].
    - cbn [proj1_sig]. apply crt_graph_done. exact Hzero.
    - apply crt_graph_next; [exact Hnonzero |].
      unfold next.
      cbn [crt_r1 crt_u1 crt_v1 crt_r2 crt_u2 crt_v2].
      rewrite div_aligned_all, div_eucl_pair.
      cbn [fst]. apply Hrec.
  Qed.


  (** The state loop returns the exact coefficients chosen by the standard library. *)
  Lemma extgcd_agrees : forall a b, extgcd a b = Z.extgcd a b.
  Proof.
    intros a b.
    eapply graph_deterministic.
    - unfold extgcd. apply loop_graph.
    - apply standard_extgcd_graph.
  Qed.

  Definition combinecong (m1 m2 r1 r2 : Z) : Z :=
    let '(u, v, d) := extgcd m1 m2 in
    if r1 mod d =? r2 mod d then
      if d =? 0 then r1
      else (v * m2 * r1 + u * m1 * r2) / d mod Z.abs (m1 * (m2 / d))
    else 0.
  TimeFun combinecong.

  (** The CRT helper keeps the standard library's exact residue, including zero moduli. *)
  Lemma combinecong_agrees : forall m1 m2 r1 r2,
    combinecong m1 m2 r1 r2 = Z.combinecong m1 m2 r1 r2.
  Proof.
    intros m1 m2 r1 r2.
    unfold combinecong, Z.combinecong. rewrite extgcd_agrees.
    destruct (Z.extgcd m1 m2) as [[u v] d].
    destruct (Z.eq_dec (r1 mod d) (r2 mod d)) as [Hequal | Hdifferent].
    - rewrite (proj2 (Z.eqb_eq _ _) Hequal).
      destruct (Z.eq_dec d 0) as [Hzero | Hnonzero].
      + rewrite (proj2 (Z.eqb_eq _ _) Hzero). reflexivity.
      + rewrite (proj2 (Z.eqb_neq _ _) Hnonzero). reflexivity.
    - rewrite (proj2 (Z.eqb_neq _ _) Hdifferent). reflexivity.
  Qed.
End CongruenceCRT.
Import CongruenceCRT.

(** Arithmetic bit and cost bounds shared by CRT and payload normalization. *)
Module CongruenceCost.
  Lemma integer_divide_size : forall a b,
    (Z.size_nat (a / b) <= Z.size_nat a)%nat.
  Proof.
    intros a b. destruct (Z.eq_dec b 0) as [->|Hnonzero].
    - rewrite Z.div_0_r. cbn [Z.size_nat]. lia.
    - pose proof (Z.div_mod a b Hnonzero) as Hdivision.
      pose proof (Z.mod_bound_abs a b Hnonzero) as Hremainder.
      pose proof (Z.abs_nonneg a) as Ha.
      pose proof (Z.abs_nonneg (a / b)) as Hq.
      assert (Hb : 0 < Z.abs b) by (apply Z.abs_pos; exact Hnonzero).
      assert (Htriangle : Z.abs b * Z.abs (a / b) <= Z.abs a + Z.abs (a mod b)).
      { rewrite <- Z.abs_mul.
        replace (b * (a / b)) with (a + - (a mod b)) by lia.
        pose proof (Z.abs_triangle a (- (a mod b))) as Hsum.
        now rewrite Z.abs_opp in Hsum. }
      assert (Hquotient : Z.abs (a / b) <= Z.abs a).
      { destruct (Z_le_gt_dec (Z.abs (a / b)) (Z.abs a)) as [Hle|Hgt]; [exact Hle|].
        assert (Hmultiply : Z.abs b * (Z.abs a + 1) <= Z.abs b * Z.abs (a / b)).
        { apply Z.mul_le_mono_nonneg_l; lia. }
        assert (Hlower : Z.abs a + Z.abs b <= Z.abs b * (Z.abs a + 1)) by nia.
        lia. }
      pose proof (Z.size_nat_mono (Z.abs (a / b)) (Z.abs a)
        (conj Hq Hquotient)) as Hsize.
      now rewrite !integer_abs_size in Hsize.
  Qed.

  Lemma integer_modulo_size : forall a b,
    (Z.size_nat (a mod b) <= Z.size_nat a + Z.size_nat b)%nat.
  Proof.
    intros a b. destruct (Z.eq_dec b 0) as [->|Hnonzero].
    - rewrite Z.mod_0_r. cbn [Z.size_nat]. lia.
    - pose proof (Z.mod_bound_abs a b Hnonzero) as Hremainder.
      pose proof (Z.abs_nonneg (a mod b)) as Hnonnegative.
      pose proof (Z.size_nat_mono (Z.abs (a mod b)) (Z.abs b) ltac:(lia)) as Hsize.
      rewrite !integer_abs_size in Hsize. lia.
  Qed.

  Lemma integer_gcd_size : forall a b,
    (Z.size_nat (Z.gcd a b) <= Z.size_nat a + Z.size_nat b)%nat.
  Proof.
    intros a b. destruct (Z.eq_dec a 0) as [->|Hnonzero].
    - rewrite Z.gcd_0_l, integer_abs_size. cbn [Z.size_nat]. lia.
    - assert (Ha : 0 < Z.abs a) by (apply Z.abs_pos; exact Hnonzero).
      pose proof (Z.gcd_divide_l (Z.abs a) b) as Hdivide.
      rewrite Z.gcd_abs_l in Hdivide.
      pose proof (Z.divide_pos_le (Z.gcd a b) (Z.abs a) Ha Hdivide) as Hbound.
      pose proof (Z.gcd_nonneg a b) as Hnonnegative.
      pose proof (Z.size_nat_mono (Z.gcd a b) (Z.abs a) ltac:(lia)) as Hsize.
      rewrite integer_abs_size in Hsize. lia.
  Qed.

  Lemma integer_lcm_size : forall a b,
    (Z.size_nat (Z.lcm a b) <= Z.size_nat a + Z.size_nat b)%nat.
  Proof.
    intros a b. unfold Z.lcm. rewrite integer_abs_size.
    pose proof (integer_multiply_size a (b / Z.gcd a b)).
    pose proof (integer_divide_size b (Z.gcd a b)). lia.
  Qed.

  Lemma square_scaled : forall bound scale n,
    (bound <= scale * n)%nat ->
    (N.of_nat (bound ^ 2) <= N.of_nat (scale ^ 2) * N.of_nat (n ^ 2))%N.
  Proof.
    intros bound scale n Hbound. rewrite <- Nat2N.inj_mul.
    apply time_of_nat_le. rewrite <- Nat.pow_mul_l.
    apply Nat.pow_le_mono_l. exact Hbound.
  Qed.

  Lemma eqb_time_budget : forall n x y,
    (Z.size_nat x + 1 <= n)%nat -> (Z.T_eqb x y <= N.of_nat n)%N.
  Proof.
    intros n x y Hsize. pose proof (Z.T_eqb_le x y).
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_add in Hsize.
    time_cbn_all. lia.
  Qed.

  Lemma add_time_budget : forall n x y,
    (Z.size_nat x + Z.size_nat y + 1 <= n)%nat ->
    (Z.T_add x y <= 3 * N.of_nat n)%N.
  Proof.
    intros n x y Hsize. pose proof (Z.T_add_le x y).
    apply time_of_nat_le in Hsize. rewrite !Nat2N.inj_add in *.
    time_cbn_all. lia.
  Qed.

  Lemma sub_time_budget : forall n x y,
    (Z.size_nat x + Z.size_nat y + 1 <= n)%nat ->
    (Z.T_sub x y <= 3 * N.of_nat n)%N.
  Proof.
    intros n x y Hsize. pose proof (Z.T_sub_le x y).
    apply time_of_nat_le in Hsize. rewrite !Nat2N.inj_add in *.
    time_cbn_all. lia.
  Qed.

  Lemma mul_time_budget : forall n x y,
    (Z.size_nat x + Z.size_nat y + 1 <= n)%nat ->
    (Z.T_mul x y <= 2 * N.of_nat (n ^ 2))%N.
  Proof.
    intros n x y Hsize. pose proof (Z.T_mul_le x y) as Hmultiply.
    apply time_of_nat_le in Hsize.
    rewrite !Nat2N.inj_pow, !Nat2N.inj_add in *. time_cbn_all.
    assert (Hproduct : ((N.of_nat (Z.size_nat x) + 1) *
      (N.of_nat (Z.size_nat x) + 2 * N.of_nat (Z.size_nat y) + 2) <=
      N.of_nat n * (2 * N.of_nat n))%N).
    { apply N.mul_le_mono; lia. }
    nia.
  Qed.

  Lemma div_time_budget : forall n x y,
    (Z.size_nat x + Z.size_nat y + 1 <= n)%nat ->
    (Z.T_div x y <= 64 * N.of_nat (n ^ 2))%N.
  Proof.
    intros n x y Hsize. pose proof (Z.T_div_le x y) as Hdivide.
    apply time_of_nat_le in Hsize.
    rewrite !Nat2N.inj_pow, !Nat2N.inj_add in *. time_cbn_all.
    assert (Hproduct : ((N.of_nat (Z.size_nat x) + 1) *
      (N.of_nat (Z.size_nat x) + N.of_nat (Z.size_nat y) + 2) <=
      N.of_nat n * (2 * N.of_nat n))%N).
    { apply N.mul_le_mono; lia. }
    nia.
  Qed.

  Lemma mod_time_budget : forall n x y,
    (Z.size_nat x + Z.size_nat y + 1 <= n)%nat ->
    (Z.T_modulo x y <= 64 * N.of_nat (n ^ 2))%N.
  Proof.
    intros n x y Hsize. pose proof (Z.T_modulo_le x y) as Hmodulo.
    apply time_of_nat_le in Hsize.
    rewrite !Nat2N.inj_pow, !Nat2N.inj_add in *. time_cbn_all.
    assert (Hproduct : ((N.of_nat (Z.size_nat x) + 1) *
      (N.of_nat (Z.size_nat x) + N.of_nat (Z.size_nat y) + 2) <=
      N.of_nat n * (2 * N.of_nat n))%N).
    { apply N.mul_le_mono; lia. }
    nia.
  Qed.

  Lemma gcd_time_budget : forall n x y,
    (Z.size_nat x + Z.size_nat y + 1 <= n)%nat ->
    (Z.T_gcd x y <= 8 * N.of_nat (n ^ 2))%N.
  Proof.
    intros n x y Hsize. pose proof (Z.T_gcd_le x y) as Hgcd.
    apply time_of_nat_le in Hsize.
    rewrite !Nat2N.inj_pow, !Nat2N.inj_add in *. time_cbn_all.
    assert (Hproduct : ((N.of_nat (Z.size_nat x) + N.of_nat (Z.size_nat y) + 2) *
      (2 * (N.of_nat (Z.size_nat x) + N.of_nat (Z.size_nat y)) + 3) <=
      (2 * N.of_nat n) * (3 * N.of_nat n))%N).
    { apply N.mul_le_mono; lia. }
    nia.
  Qed.
  (** Compute literal coefficients while keeping every symbolic budget folded. *)
  Ltac cost_literal n :=
    lazymatch n with
    | O => idtac
    | S ?rest => cost_literal rest
    end.

  Ltac cost_constants :=
    repeat match goal with
    | H : context [N.of_nat ((?k ^ 2)%nat)] |- _ =>
      cost_literal k;
      let value := eval vm_compute in (N.of_nat ((k ^ 2)%nat)) in
      progress change (N.of_nat ((k ^ 2)%nat)) with value in H
    | H : context [N.of_nat ?k] |- _ =>
      cost_literal k;
      let value := eval vm_compute in (N.of_nat k) in
      progress change (N.of_nat k) with value in H
    end.

  Lemma linear_le_square : forall n, (1 <= n)%nat ->
    (N.of_nat n <= N.of_nat (n ^ 2))%N.
  Proof.
    intros n Hpositive. apply time_of_nat_le. cbn [Nat.pow]. nia.
  Qed.

  (** The CRT expression uses only linearly sized coefficients and intermediate integers. *)
  Lemma combinecong_budget : forall n m1 m2 r1 r2,
    (Z.size_nat m1 + Z.size_nat m2 + Z.size_nat r1 + Z.size_nat r2 + 1 <= n)%nat ->
    (Z.size_nat (combinecong m1 m2 r1 r2) <= 15 * n)%nat /\
    (T_combinecong m1 m2 r1 r2 <= 131072 * N.of_nat (n ^ 2))%N.
  Proof.
    intros n m1 m2 r1 r2 Hinput.
    pose proof (extgcd_result_budget m1 m2) as Hresult.
    pose proof (T_extgcd_le m1 m2) as Hexttime.
    unfold k_gcd in Hexttime.
    destruct (extgcd m1 m2) as [[u v] d] eqn:Hext.
    cbn [result_budget] in Hresult. destruct Hresult as [Hu [Hv Hd]].
    assert (Hpositive : (1 <= n)%nat) by lia.
    assert (Hubits : (Z.size_nat u <= 4 * n)%nat) by lia.
    assert (Hvbits : (Z.size_nat v <= 4 * n)%nat) by lia.
    assert (Hdbits : (Z.size_nat d <= n)%nat) by lia.
    pose proof (integer_multiply_size v m2) as Hvm2.
    pose proof (integer_multiply_size (v * m2) r1) as Hleft.
    pose proof (integer_multiply_size u m1) as Hum1.
    pose proof (integer_multiply_size (u * m1) r2) as Hright.
    pose proof (WordTime.integer_add_size (v * m2 * r1) (u * m1 * r2)) as Hsum.
    assert (Hnumerator : (Z.size_nat (v * m2 * r1 + u * m1 * r2) <= 13 * n)%nat)
      by lia.
    pose proof (integer_divide_size (v * m2 * r1 + u * m1 * r2) d) as Hquotient.
    pose proof (integer_divide_size m2 d) as Hfactor.
    pose proof (integer_multiply_size m1 (m2 / d)) as Hproduct.
    assert (Hmodulus : (Z.size_nat (Z.abs (m1 * (m2 / d))) <= 2 * n)%nat).
    { rewrite integer_abs_size. lia. }
    pose proof (integer_modulo_size r1 d) as Hrem1.
    pose proof (integer_modulo_size r2 d) as Hrem2.
    pose proof (integer_modulo_size ((v * m2 * r1 + u * m1 * r2) / d)
      (Z.abs (m1 * (m2 / d)))) as Houtput.
    split.
    - unfold combinecong. rewrite Hext.
      destruct (r1 mod d =? r2 mod d), (d =? 0); cbn [Z.size_nat]; lia.
    - pose proof (mod_time_budget (3 * n) r1 d ltac:(lia)) as Hmod1.
      pose proof (mod_time_budget (3 * n) r2 d ltac:(lia)) as Hmod2.
      pose proof (eqb_time_budget (3 * n) (r1 mod d) (r2 mod d) ltac:(lia)) as Heq.
      pose proof (eqb_time_budget (2 * n) d 0 ltac:(lia)) as Hzero.
      pose proof (mul_time_budget (6 * n) v m2 ltac:(lia)) as Hmulv.
      pose proof (mul_time_budget (7 * n) (v * m2) r1 ltac:(lia)) as Hmull.
      pose proof (mul_time_budget (6 * n) u m1 ltac:(lia)) as Hmulu.
      pose proof (mul_time_budget (7 * n) (u * m1) r2 ltac:(lia)) as Hmulr.
      pose proof (add_time_budget (13 * n) (v * m2 * r1) (u * m1 * r2)
        ltac:(lia)) as Hadd.
      pose proof (div_time_budget (15 * n) (v * m2 * r1 + u * m1 * r2) d
        ltac:(lia)) as Hdivide.
      pose proof (div_time_budget (3 * n) m2 d ltac:(lia)) as Hdividefactor.
      pose proof (mul_time_budget (3 * n) m1 (m2 / d) ltac:(lia)) as Hmulmodulus.
      pose proof (Z.T_abs_le (m1 * (m2 / d))) as Habs.
      pose proof (mod_time_budget (16 * n) ((v * m2 * r1 + u * m1 * r2) / d)
        (Z.abs (m1 * (m2 / d))) ltac:(lia)) as Hmodulo.
      assert (Hextsquare :
        (N.of_nat ((Z.size_nat m1 + Z.size_nat m2 + 1) ^ 2) <=
          N.of_nat (n ^ 2))%N).
      { apply time_of_nat_le. apply Nat.pow_le_mono_l. lia. }
      pose proof (linear_le_square n Hpositive) as Hlinear.
      assert (Hone : (1 <= N.of_nat n)%N).
      { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
      time_unfold T_combinecong. rewrite Hext. cbn beta zeta.
      rewrite !Nat.pow_mul_l, !Nat2N.inj_mul in *.
      cost_constants.
      destruct (r1 mod d =? r2 mod d), (d =? 0); lia.
  Qed.
  Lemma lcm_time_budget : forall n a b,
    (Z.size_nat a + Z.size_nat b + 1 <= n)%nat ->
    (Z.T_lcm a b <= 512 * N.of_nat (n ^ 2))%N.
  Proof.
    intros n a b Hinput.
    pose proof (integer_gcd_size a b) as Hgsize.
    pose proof (integer_divide_size b (Z.gcd a b)) as Hqsize.
    pose proof (gcd_time_budget n a b Hinput) as Hgcd.
    pose proof (div_time_budget (2 * n) b (Z.gcd a b) ltac:(lia)) as Hdivide.
    pose proof (mul_time_budget n a (b / Z.gcd a b) ltac:(lia)) as Hmultiply.
    pose proof (Z.T_abs_le (a * (b / Z.gcd a b))) as Habs.
    assert (Hpositive : (1 <= n)%nat) by lia.
    pose proof (linear_le_square n Hpositive) as Hlinear.
    assert (Hone : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
    rewrite Nat.pow_mul_l, Nat2N.inj_mul in Hdivide.
    time_unfold Z.T_lcm. cost_constants. lia.
  Qed.
End CongruenceCost.
Import CongruenceCost.

(** Raw integer shifting agrees with the bounded word shift on normalized inputs. *)
Lemma normalized_wshl : forall w x y, is_word w x -> is_word w y ->
  wrap w (Z.shiftl x y) = wshl w x y.
Proof.
  intros w x y Hx Hy.
  rewrite Z.shiftl_mul_pow2 by (destruct Hy; lia).
  unfold wshl. rewrite (wrap_id w x Hx), (wrap_id w y Hy).
  destruct (Zpos w <=? y) eqn:Hlarge; [| reflexivity].
  apply Z.leb_le in Hlarge.
  replace y with (Zpos w + (y - Zpos w)) by lia.
  rewrite Z.pow_add_r by lia. rewrite wrap_mod.
  replace (x * (2 ^ Zpos w * 2 ^ (y - Zpos w))) with
    ((x * 2 ^ (y - Zpos w)) * modulus w) by (unfold modulus; ring).
  apply Z.mod_mul. apply modulus_nonzero.
Qed.

(** Raw integer remainder agrees with unsigned word remainder on normalized inputs. *)
Lemma normalized_wurem : forall w x y, is_word w x -> is_word w y ->
  wrap w (x mod y) = wurem w x y.
Proof.
  intros w x y Hx Hy.
  rewrite wurem_mod, (wrap_id w x Hx), (wrap_id w y Hy).
  apply wrap_id. destruct (Z.eq_dec y 0) as [-> | Hnonzero].
  - now rewrite Z.mod_0_r.
  - destruct Hy as [Hy Hbound].
    pose proof (Z.mod_pos_bound x y ltac:(lia)) as Hremainder.
    unfold is_word. lia.
Qed.


Local Lemma lowbit_odd : forall a, Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  intros a. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_opp by exact Hi.
  replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec i 0) as [->|Hnz].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite Z.pow2_bits_false with (n := 0) by lia.
    destruct (Z.testbit a (i - 1)); reflexivity.
Qed.

Local Lemma lowbit_double : forall a,
  Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (-a).
Proof.
  intros a. replace (- (2 * a)) with (2 * (-a)) by ring.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hnz].
  - now rewrite !Z.testbit_even_0.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

(** Every positive integer is an odd multiple of its least set bit. *)
Lemma positive_lowbit_factor : forall p, exists k q,
  0 <= k /\ Z.land (Zpos p) (- Zpos p) = 2 ^ k /\
  Zpos p = 2 ^ k * (2 * q + 1).
Proof.
  intro p. induction p as [p IH | p IH |].
  - exists 0, (Zpos p). split; [lia |]. split.
    + change (Z.land (2 * Zpos p + 1) (- (2 * Zpos p + 1)) = 1).
      apply lowbit_odd.
    + change (2 * Zpos p + 1 = 1 * (2 * Zpos p + 1)). ring.
  - destruct IH as [k [q [Hk [Hlow Hfactor]]]]. exists (Z.succ k), q.
    split; [lia |]. split.
    + change (Z.land (2 * Zpos p) (- (2 * Zpos p)) = 2 ^ Z.succ k).
      rewrite lowbit_double, Hlow, Z.pow_succ_r by exact Hk. reflexivity.
    + change (2 * Zpos p = 2 ^ Z.succ k * (2 * q + 1)).
      rewrite Z.pow_succ_r by exact Hk. rewrite Hfactor. ring.
  - exists 0, 0. split; [lia |]. split; reflexivity.
Qed.

(** Odd integers are coprime to powers of two with nonnegative exponents. *)
Lemma odd_pow2_gcd : forall q k, 0 <= k -> Z.gcd (2 * q + 1) (2 ^ k) = 1.
Proof.
  intros q k Hk. apply Z.coprime_pow_r; [exact Hk |].
  unfold Z.coprime. rewrite Z.gcd_comm.
  replace (2 * q + 1) with (1 + q * 2) by ring.
  rewrite Z.gcd_add_mult_diag_r. apply Z.gcd_1_r.
Qed.

(** Factoring a power of two exposes the smaller of two binary valuations. *)
Lemma gcd_odd_pow2 : forall k h q,
  0 <= k -> 0 <= h ->
  Z.gcd (2 ^ k * (2 * q + 1)) (2 ^ h) = 2 ^ Z.min k h.
Proof.
  intros k h q Hk Hh.
  destruct (Z_le_dec k h) as [Hkh | Hkh].
  - rewrite Z.min_l by exact Hkh.
    replace h with (k + (h - k)) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.gcd_mul_mono_l_nonneg by (apply Z.pow_nonneg; lia).
    rewrite odd_pow2_gcd by lia. ring.
  - rewrite Z.min_r by lia.
    replace k with (h + (k - h)) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    replace (2 ^ h * 2 ^ (k - h) * (2 * q + 1)) with
      (2 ^ h * (2 ^ (k - h) * (2 * q + 1))) by ring.
    rewrite Z.gcd_comm, Z.gcd_mul_diag_l by (apply Z.pow_nonneg; lia).
    reflexivity.
Qed.

(** Powers of two preserve the minimum of nonnegative exponents. *)
Lemma pow2_min : forall k h,
  0 <= k -> 0 <= h -> 2 ^ Z.min k h = Z.min (2 ^ k) (2 ^ h).
Proof.
  intros k h Hk Hh. destruct (Z_le_dec k h) as [Hkh | Hkh].
  - rewrite Z.min_l by exact Hkh.
    rewrite Z.min_l; [reflexivity |]. apply Z.pow_le_mono_r; lia.
  - rewrite Z.min_r by lia.
    rewrite Z.min_r; [reflexivity |]. apply Z.pow_le_mono_r; lia.
Qed.

Definition pow2_gcd (w : positive) (m : Z) : Z :=
  if m =? 0 then modulus w else Z.min (Z.land m (-m)) (modulus w).

(** Taking the least set bit computes gcd with the word modulus. *)
Lemma pow2_gcd_spec : forall w m, pow2_gcd w m = Z.gcd m (modulus w).
Proof.
  intros w m. destruct m as [|p|p].
  - change (modulus w = Z.gcd 0 (modulus w)).
    symmetry. apply Z.gcd_0_l_nonneg. pose proof (modulus_pos w). lia.
  - destruct (positive_lowbit_factor p) as [k [q [Hk [Hlow Hfactor]]]].
    unfold pow2_gcd. cbn [Z.eqb]. rewrite Hlow. unfold modulus.
    rewrite <- pow2_min by lia. rewrite Hfactor, gcd_odd_pow2 by lia. reflexivity.
  - change (pow2_gcd w (- Zpos p) = Z.gcd (- Zpos p) (modulus w)).
    rewrite Z.gcd_opp_l.
    destruct (positive_lowbit_factor p) as [k [q [Hk [Hlow Hfactor]]]].
    unfold pow2_gcd.
    rewrite (proj2 (Z.eqb_neq (- Zpos p) 0)) by lia.
    rewrite Z.opp_involutive, Z.land_comm, Hlow.
    unfold modulus. rewrite <- pow2_min by lia.
    rewrite Hfactor, gcd_odd_pow2 by lia. reflexivity.
Qed.

(** Every nonzero integer has a positive power of two as its least set bit. *)
Lemma nonzero_lowbit_power : forall m, m <> 0 ->
  exists k, 0 <= k /\ Z.land m (-m) = 2 ^ k.
Proof.
  intros m Hm. destruct m as [|p|p]; [contradiction | |].
  - destruct (positive_lowbit_factor p) as [k [q [Hk [Hlow Hfactor]]]].
    exists k. auto.
  - destruct (positive_lowbit_factor p) as [k [q [Hk [Hlow Hfactor]]]].
    exists k. split; [exact Hk |].
    change (Z.land (- Zpos p) (Zpos p) = 2 ^ k).
    now rewrite Z.land_comm.
Qed.

(** The masked gcd is a power of two whose exponent fits the word width. *)
Lemma pow2_gcd_power : forall w m, exists k,
  0 <= k <= Zpos w /\ pow2_gcd w m = 2 ^ k.
Proof.
  intros w m. unfold pow2_gcd. destruct (m =? 0) eqn:Hm.
  - exists (Zpos w). split; [lia | reflexivity].
  - apply Z.eqb_neq in Hm.
    destruct (nonzero_lowbit_power m Hm) as [k [Hk Hlow]].
    exists (Z.min k (Zpos w)). split.
    + split; [apply Z.min_glb; lia | apply Z.le_min_r].
    + rewrite Hlow. unfold modulus. symmetry. apply pow2_min; lia.
Qed.

(** The masked gcd is positive and does not exceed the word modulus. *)
Lemma pow2_gcd_bounds : forall w m, 0 < pow2_gcd w m <= modulus w.
Proof.
  intros w m. destruct (pow2_gcd_power w m) as [k [Hk ->]].
  split; [apply Z.pow_pos_nonneg; lia |].
  unfold modulus. apply Z.pow_le_mono_r; lia.
Qed.

(** The gcd of two nonnegative powers of two is their minimum. *)
Lemma gcd_pow2_min : forall k h,
  0 <= k -> 0 <= h -> Z.gcd (2 ^ k) (2 ^ h) = Z.min (2 ^ k) (2 ^ h).
Proof.
  intros k h Hk Hh. rewrite <- pow2_min by assumption.
  replace (2 ^ k) with (2 ^ k * (2 * 0 + 1)) at 1 by ring.
  apply gcd_odd_pow2; assumption.
Qed.

(** Intersecting both gcd operands with the same modulus commutes with gcd. *)
Lemma gcd_intersect_modulus : forall m n M,
  Z.gcd (Z.gcd m n) M = Z.gcd (Z.gcd m M) (Z.gcd n M).
Proof.
  intros m n M. apply Z.gcd_unique_alt; [apply Z.gcd_nonneg |].
  intros q. rewrite !Z.gcd_divide_iff. tauto.
Qed.

(** Gcd between classes reduces to a minimum after masking to one width. *)
Lemma pow2_gcd_min : forall w m n,
  Z.gcd (Z.gcd m n) (modulus w) = Z.min (pow2_gcd w m) (pow2_gcd w n).
Proof.
  intros w m n. rewrite gcd_intersect_modulus, <- !pow2_gcd_spec.
  destruct (pow2_gcd_power w m) as [k [Hk ->]].
  destruct (pow2_gcd_power w n) as [h [Hh ->]].
  apply gcd_pow2_min; lia.
Qed.

(** Masking with a nonnegative power of two minus one computes remainder. *)
Lemma power_mask_mod : forall k r, 0 <= k ->
  Z.land r (2 ^ k - 1) = r mod 2 ^ k.
Proof.
  intros k r Hk.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  apply Z.land_ones. exact Hk.
Qed.

(** A least-set-bit mask uses no more bits than its input. *)
Lemma lowbit_size : forall m,
  (Z.size_nat (Z.land m (-m)) <= Z.size_nat m)%nat.
Proof.
  assert (Hpositive : forall p,
    (Z.size_nat (Z.land (Zpos p) (- Zpos p)) <= Z.size_nat (Zpos p))%nat).
  { intros p. destruct (positive_lowbit_factor p) as [k [q [Hk [Hlow Hfactor]]]].
    rewrite Hlow. apply Z.size_nat_mono.
    pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Hpower.
    assert (Hodd : 0 < 2 * q + 1) by nia. nia. }
  intros [|p|p]; [reflexivity | apply Hpositive |].
  change (Z.size_nat (Z.land (- Zpos p) (Zpos p)) <= Z.size_nat (Zpos p))%nat.
  rewrite Z.land_comm. apply Hpositive.
Qed.

(** The masked gcd fits the bit width of the word modulus. *)
Lemma pow2_gcd_size : forall w m,
  (Z.size_nat (pow2_gcd w m) <= Pos.to_nat w + 1)%nat.
Proof.
  intros w m. pose proof (pow2_gcd_bounds w m) as Hrange.
  eapply Nat.le_trans with (m := Z.size_nat (modulus w));
    [apply Z.size_nat_mono; lia | apply modulus_size_le].
Qed.

TimeFun pow2_gcd.

(** The least-set-bit gcd runs in linear input and width work. *)
Lemma pow2_gcd_time : forall w m,
  (T_pow2_gcd w m <= 64 * N.of_nat (Pos.to_nat w + Z.size_nat m + 1))%N.
Proof.
  intros w m.
  pose proof (Z.T_eqb_le m 0) as Hzero.
  pose proof (modulus_time_le w) as Hmodulus.
  pose proof (Z.T_opp_le m) as Hopp.
  pose proof (Z.T_land_le m (-m)) as Hland.
  pose proof (Z.T_min_le (Z.land m (-m)) (modulus w)) as Hmin.
  pose proof (lowbit_size m) as Hlow.
  assert (Hoppbits : Z.size_nat (-m) = Z.size_nat m) by (destruct m; reflexivity).
  rewrite Hoppbits in Hland. apply time_of_nat_le in Hlow.
  rewrite !Nat2N.inj_add in *.
  time_unfold T_pow2_gcd. destruct (m =? 0); time_cbn_all; lia.
Qed.

(** Intersecting a gcd with the word modulus takes the minimum of its masked operands. *)
Lemma pow2_gcd_gcd : forall w m n,
  pow2_gcd w (Z.gcd m n) = Z.min (pow2_gcd w m) (pow2_gcd w n).
Proof.
  intros w m n. rewrite pow2_gcd_spec. apply pow2_gcd_min.
Qed.

(** Reusing a constructed modulus removes repeated power construction. *)
Definition pow2_gcd_at (M m : Z) : Z :=
  if m =? 0 then M else Z.min (Z.land m (-m)) M.
TimeFun pow2_gcd_at.

(** The shared-modulus gcd has the same value as the width-indexed gcd. *)
Lemma pow2_gcd_at_eq : forall w m,
  pow2_gcd_at (modulus w) m = pow2_gcd w m.
Proof.
  intros w m. reflexivity.
Qed.

(** Comparing against a supplied modulus charges only the input's bit length. *)
Lemma pow2_gcd_at_time : forall M m,
  (T_pow2_gcd_at M m <= 32 * N.of_nat (Z.size_nat m + 1))%N.
Proof.
  intros M m.
  pose proof (Z.T_eqb_le m 0) as Hzero.
  pose proof (Z.T_opp_le m) as Hopp.
  pose proof (Z.T_land_le m (-m)) as Hland.
  pose proof (Z.T_min_le (Z.land m (-m)) M) as Hmin.
  pose proof (lowbit_size m) as Hlow.
  rewrite WordTime.integer_opp_size in Hland.
  apply time_of_nat_le in Hlow. rewrite !Nat2N.inj_add in *.
  time_unfold T_pow2_gcd_at. destruct (m =? 0); time_cbn_all; lia.
Qed.

(** A nonnegative left shift consists of constant-cost doubling steps. *)
Lemma congruence_shiftl_time : forall z k, 0 <= k ->
  (Std.Z.T_shiftl z k <= 8 * N.of_nat (Z.to_nat k + 1))%N.
Proof.
  intros z [| p | p] Hk; [| | lia].
  - time_unfold Std.Z.T_shiftl. time_cbn. nia.
  - pose proof (Std.Pos.T_iter_le (Z.mul 2) (fun x => Std.Z.T_mul 2 x) (fun _ => True)
      3 z p (fun _ _ => I) (fun x _ => Std.Z.T_mul_two_le x) I) as Hiter.
    time_unfold Std.Z.T_shiftl. time_cbn. cbn [Z.to_nat].
    rewrite Nat2N.inj_add.
    change (N.of_nat (Pos.to_nat p)) with (N.of_nat (N.to_nat (N.pos p))).
    rewrite N2Nat.id. nia.
Qed.

(** Masking a class can reuse the modulus that selected its gcd. *)
Definition wrap_class_at (M g r : Z) : congr :=
  if M <=? g then C 0 (Z.land r (M - 1)) else C g (Z.land r (g - 1)).
TimeFun wrap_class_at.

(** Class masking with a supplied modulus charges only the three integer sizes. *)
Lemma wrap_class_at_time : forall M g r,
  (T_wrap_class_at M g r <=
    64 * N.of_nat (Z.size_nat M + Z.size_nat g + Z.size_nat r + 1))%N.
Proof.
  intros M g r.
  pose proof (Z.T_leb_le M g) as Hlarge.
  pose proof (Z.T_sub_le M 1) as Hwordpred.
  pose proof (Z.T_sub_le g 1) as Hclasspred.
  pose proof (Z.T_land_le r (M - 1)) as Hwordmask.
  pose proof (Z.T_land_le r (g - 1)) as Hclassmask.
  pose proof (WordTime.integer_sub_size M 1) as Hwordsize.
  pose proof (WordTime.integer_sub_size g 1) as Hclasssize.
  apply time_of_nat_le in Hwordsize.
  apply time_of_nat_le in Hclasssize.
  rewrite !Nat2N.inj_add in *.
  time_unfold T_wrap_class_at.
  destruct (M <=? g); time_cbn_all; lia.
Qed.

Module CongruenceCode (L : WORD_LANGUAGE_OPS) <: CONGRUENCE_OPS L.
  Definition p := congr.
  Definition wordb w z := (0 <=? z) && (z <? modulus w).
  Definition congr_norm_ref w c :=
    match c with
    | CBot => CBot
    | C m r =>
      let m' := Z.abs m in
      if m' =? 0 then if wordb w r then C 0 r else CBot else
        let r' := r mod m' in
        if modulus w <=? m' then if wordb w r' then C 0 r' else CBot
        else C m' r'
    end.
  Definition congr_norm w c :=
    match c with
    | CBot => CBot
    | C m r =>
      let m' := Z.abs m in
      if m' =? 0 then if wordb w r then C 0 r else CBot else
        let r' := if 0 <=? r then if r <? m' then r else r mod m' else r mod m' in
        if modulus w <=? m' then if wordb w r' then C 0 r' else CBot
        else C m' r'
    end.
  Definition raw_leb a b :=
    match a, b with
    | CBot, _ => true
    | _, CBot => false
    | C m r, C n s => (m mod n =? 0) && ((r - s) mod n =? 0)
    end.
  Definition pleb w a b := raw_leb (congr_norm w a) (congr_norm w b).
  Definition pjoin w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, c => c
    | c, CBot => c
    | C m r, C n s => congr_norm w (C (Z.gcd (Z.gcd m n) (r - s)) r)
    end.
  Definition join_norm w na nb :=
    match na, nb with
    | CBot, c => c
    | c, CBot => c
    | C m r, C n s => congr_norm w (C (Z.gcd (Z.gcd m n) (r - s)) r)
    end.
  Definition pmeet w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C n s =>
      if r mod Z.gcd m n =? s mod Z.gcd m n then
        congr_norm w (C (Z.lcm m n) (CongruenceCRT.combinecong m n r s))
      else CBot
    end.
  Definition pbot (_ : positive) := CBot.
  Definition ptop (_ : positive) := C 1 0.
  Definition pis_bot w a := match congr_norm w a with CBot => true | _ => false end.
  Definition pconst w z := C 0 (Word.wrap w z).
  Definition ppoint w a :=
    match congr_norm w a with C 0 r => Some r | _ => None end.
  Definition pwparam := unit.
  Definition pwiden_ref (_ : pwparam) w a b :=
    if pleb w b a then a else pjoin w a b.
  Definition pwiden (_ : pwparam) w a b :=
    let na := congr_norm w a in
    let nb := congr_norm w b in
    if raw_leb nb na then a else join_norm w na nb.
  Definition pnarrow w a b := pmeet w a b.
  Definition wrap_class_ref w m r := congr_norm w (C (Z.gcd m (modulus w)) r).
  Definition wrap_class_g w g r := wrap_class_at (modulus w) g r.
  Definition wrap_class w m r :=
    let M := modulus w in wrap_class_at M (pow2_gcd_at M m) r.
  Definition congr_neg w a :=
    match congr_norm w a with CBot => CBot | C m r => wrap_class w m (-r) end.
  Definition congr_neg_ref w a :=
    match congr_norm w a with CBot => CBot | C m r => wrap_class_ref w m (-r) end.
  Definition congr_add_ref w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class_ref w (Z.gcd m n) (r + s)
    | _, _ => CBot
    end.
  Definition congr_add w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s =>
      let M := modulus w in
      wrap_class_at M (Z.min (pow2_gcd_at M m) (pow2_gcd_at M n)) (r + s)
    | _, _ => CBot
    end.
  Definition congr_sub_ref w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class_ref w (Z.gcd m n) (r - s)
    | _, _ => CBot
    end.
  Definition congr_sub w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s =>
      let M := modulus w in
      wrap_class_at M (Z.min (pow2_gcd_at M m) (pow2_gcd_at M n)) (r - s)
    | _, _ => CBot
    end.
  Definition congr_mul w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd (m * n) (Z.gcd (m * s) (n * r))) (r * s)
    | _, _ => CBot
    end.
  Definition congr_project source target a :=
    match congr_norm source a with CBot => CBot | C m r => wrap_class target m r end.
  Definition congr_project_ref source target a :=
    match congr_norm source a with CBot => CBot | C m r => wrap_class_ref target m r end.
  Definition congr_shl_ref w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C 0 k =>
      if Zpos w <=? k then C 0 0 else wrap_class_ref w (m * 2 ^ k) (r * 2 ^ k)
    | _, _ => C 1 0
    end.
  Definition congr_shl w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C 0 k =>
      if Zpos w <=? k then C 0 0 else wrap_class w (Z.shiftl m k) (Z.shiftl r k)
    | _, _ => C 1 0
    end.
  Definition congr_urem w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C 0 c => congr_norm w (C (Z.gcd m c) r)
    | _, _ => C 1 0
    end.
End CongruenceCode.

Module CongruenceTableCode (L : WORD_LANGUAGE_OPS) (D : CONGRUENCE_OPS L)
    <: WORD_TABLE_OPS L D.
  Definition wfwd o rw (xs : list (positive * D.p)) : option D.p :=
    match o, xs with
    | bvneg, [(w, a)] =>
      Some (if Pos.eqb w rw then D.congr_neg rw a else D.ptop rw)
    | bvzext _, [(w, a)] =>
      Some (if Pos.leb w rw then D.congr_norm rw a else D.ptop rw)
    | bvtrunc _, [(w, a)] => Some (D.congr_project w rw a)
    | (bvadd | bvsub | bvmul | bvshl | bvurem), [(wa, a); (wb, b)] =>
      Some (if Pos.eqb wa rw && Pos.eqb wb rw then
        match o with
        | bvadd => D.congr_add rw a b
        | bvsub => D.congr_sub rw a b
        | bvmul => D.congr_mul rw a b
        | bvshl => D.congr_shl rw a b
        | _ => D.congr_urem rw a b
        end else D.ptop rw)
    | bvite, [_; (wa, a); (wb, b)] =>
      Some (if Pos.eqb wa rw && Pos.eqb wb rw then D.pjoin rw a b else D.ptop rw)
    | _, _ => None
    end.
  Definition wbwd (_ : L.op) (_ : positive) (_ : D.p)
      (_ : list (positive * D.p)) : option (list D.p) := None.
End CongruenceTableCode.

Module Congruence (L : WORD_LANGUAGE) <: CONGRUENCE L.
  Include CongruenceCode L.
  Include CONGRUENCE_SPEC L.
  Definition pgamma := congr_gamma.
  Definition pwrank (_ : pwparam) (w : positive) (a : p) : nat := congr_wrank w a.
  Definition gamma_mod (w : width) (c : congr) (z : Z) : Prop :=
    match c with
    | CBot => False
    | C m r => is_word w z /\ (z - r) mod m = 0
    end.

  (** Normal residues skip division without changing any normalization result. *)
  Lemma congr_norm_eq : forall w c, congr_norm w c = congr_norm_ref w c.
  Proof.
    intros w [| m r]; [reflexivity |].
    unfold congr_norm, congr_norm_ref.
    destruct (Z.abs m =? 0); [reflexivity |].
    destruct (0 <=? r) eqn:Hnonnegative; [| reflexivity].
    destruct (r <? Z.abs m) eqn:Hsmall; [| reflexivity].
    apply Z.leb_le in Hnonnegative. apply Z.ltb_lt in Hsmall.
    rewrite Z.mod_small by lia. reflexivity.
  Qed.

  (** A power-of-two class is normalized by a mask at its modulus. *)
  Lemma wrap_class_g_eq : forall w k r,
    0 <= k <= Zpos w ->
    wrap_class_g w (2 ^ k) r = congr_norm_ref w (C (2 ^ k) r).
  Proof.
    intros w k r Hk.
    assert (Hpos : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (Hle : 2 ^ k <= modulus w).
    { unfold modulus. apply Z.pow_le_mono_r; lia. }
    unfold wrap_class_g, wrap_class_at, congr_norm_ref.
    rewrite Z.abs_eq by lia.
    rewrite (proj2 (Z.eqb_neq (2 ^ k) 0)) by lia.
    destruct (modulus w <=? 2 ^ k) eqn:Hlarge.
    - apply Z.leb_le in Hlarge.
      assert (Heq : 2 ^ k = modulus w) by lia.
      rewrite Heq.
      assert (Hmask : Z.land r (modulus w - 1) = r mod modulus w).
      { unfold modulus. apply power_mask_mod. lia. }
      rewrite Hmask.
      unfold wordb. destruct (Z.mod_pos_bound r (modulus w) (modulus_pos w)) as [Hlo Hhi].
      rewrite (proj2 (Z.leb_le 0 (r mod modulus w))) by exact Hlo.
      rewrite (proj2 (Z.ltb_lt (r mod modulus w) (modulus w))) by exact Hhi.
      reflexivity.
    - rewrite power_mask_mod by lia. reflexivity.
  Qed.

  (** The fast wrapping class agrees with gcd and Euclidean remainder. *)
  Lemma wrap_class_fast_eq : forall w m r,
    wrap_class_g w (pow2_gcd w m) r =
    congr_norm_ref w (C (Z.gcd m (modulus w)) r).
  Proof.
    intros w m r. rewrite <- pow2_gcd_spec.
    destruct (pow2_gcd_power w m) as [k [Hk ->]].
    apply wrap_class_g_eq. exact Hk.
  Qed.

  (** Shared-modulus masking preserves the reference gcd-based class. *)
  Lemma wrap_class_eq : forall w m r, wrap_class w m r = wrap_class_ref w m r.
  Proof.
    intros w m r. unfold wrap_class_ref. rewrite congr_norm_eq.
    change (wrap_class_g w (pow2_gcd w m) r =
      congr_norm_ref w (C (Z.gcd m (modulus w)) r)).
    apply wrap_class_fast_eq.
  Qed.

  (** Negation preserves the reference gcd-based wrapping operation. *)
  Lemma congr_neg_eq : forall w a, congr_neg w a = congr_neg_ref w a.
  Proof.
    intros w a. unfold congr_neg, congr_neg_ref.
    destruct (congr_norm w a); [reflexivity | apply wrap_class_eq].
  Qed.

  (** Projection preserves the reference gcd-based wrapping operation. *)
  Lemma congr_project_eq : forall source target a,
    congr_project source target a = congr_project_ref source target a.
  Proof.
    intros source target a. unfold congr_project, congr_project_ref.
    destruct (congr_norm source a); [reflexivity | apply wrap_class_eq].
  Qed.

  (** Addition uses the minimum of the two masked moduli. *)
  Lemma congr_add_eq : forall w a b, congr_add w a b = congr_add_ref w a b.
  Proof.
    intros w a b. unfold congr_add, congr_add_ref.
    destruct (congr_norm w a) as [| m r], (congr_norm w b) as [| n s];
      try reflexivity.
    change (wrap_class_g w (Z.min (pow2_gcd w m) (pow2_gcd w n)) (r + s) =
      wrap_class_ref w (Z.gcd m n) (r + s)).
    rewrite <- pow2_gcd_gcd. apply wrap_class_eq.
  Qed.

  (** Subtraction uses the minimum of the two masked moduli. *)
  Lemma congr_sub_eq : forall w a b, congr_sub w a b = congr_sub_ref w a b.
  Proof.
    intros w a b. unfold congr_sub, congr_sub_ref.
    destruct (congr_norm w a) as [| m r], (congr_norm w b) as [| n s];
      try reflexivity.
    change (wrap_class_g w (Z.min (pow2_gcd w m) (pow2_gcd w n)) (r - s) =
      wrap_class_ref w (Z.gcd m n) (r - s)).
    rewrite <- pow2_gcd_gcd. apply wrap_class_eq.
  Qed.

  (** Widening reuses the normalized operands without changing the result. *)
  Lemma pwiden_eq : forall q w a b, pwiden q w a b = pwiden_ref q w a b.
  Proof.
    intros q w a b. unfold pwiden, pwiden_ref, pleb, pjoin, join_norm.
    destruct (congr_norm w a), (congr_norm w b); reflexivity.
  Qed.

  Local Lemma cong_wordb_spec w z : wordb w z = true <-> is_word w z.
  Proof.
    unfold wordb. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. reflexivity.
  Qed.


  Local Lemma cong_mod_divide a m : a mod m = 0 <-> (m | a).
  Proof.
    destruct (Z.eq_dec m 0) as [->|Hnonzero].
    - rewrite Z.mod_0_r. split.
      + intro Hzero. subst a. exists 0. reflexivity.
      + intros [k Hk]. lia.
    - apply Z.mod_divide. exact Hnonzero.
  Qed.

  Local Lemma cong_mod_abs a m : a mod (Z.abs m) = 0 <-> a mod m = 0.
  Proof.
    rewrite !cong_mod_divide.
    split; [apply Z.divide_abs_l|intro H; now apply Z.divide_abs_l].
  Qed.

  Local Lemma cong_mod_residue z m r : 0 < m ->
    (z - r mod m) mod m = 0 <-> (z - r) mod m = 0.
  Proof.
    intro Hm. rewrite (Zminus_mod z (r mod m) m), Z.mod_mod by lia.
    rewrite (Zminus_mod z r m). reflexivity.
  Qed.

  Local Lemma cong_large_modulus w m r z : modulus w <= m ->
    0 <= r < m -> is_word w z -> ((z - r) mod m = 0 <-> z = r).
  Proof.
    intros Hlarge Hr [Hlo Hhi]. pose proof (modulus_pos w).
    rewrite cong_mod_divide. split.
    - intros [k Hk]. assert (k = 0) by nia. nia.
    - intro Heq. subst z. exists 0. ring.
  Qed.

  (** Normalization preserves the word meaning of raw classes, including negative moduli. *)
  Theorem cong_norm_gamma w c z : gamma_mod w (congr_norm w c) z <-> gamma_mod w c z.
  Proof.
    destruct c as [|m r]; [reflexivity|].
    rewrite !congr_norm_eq; unfold congr_norm_ref. destruct (Z.abs m =? 0) eqn:Hm.
    - apply Z.eqb_eq in Hm.
      assert (m = 0) by (destruct m; cbn in Hm; congruence). subst m.
      destruct (wordb w r) eqn:Hr; cbn [gamma_mod]; rewrite Z.mod_0_r.
      + reflexivity.
      + split; [contradiction|]. intros [Hword Hzero].
        assert (z = r) by lia. subst z.
        pose proof (proj2 (cong_wordb_spec w r) Hword). congruence.
    - apply Z.eqb_neq in Hm.
      assert (Hpositive : 0 < Z.abs m) by (pose proof (Z.abs_nonneg m); lia).
      destruct (modulus w <=? Z.abs m) eqn:Hlarge.
      + apply Z.leb_le in Hlarge.
        pose proof (Z.mod_pos_bound r (Z.abs m) Hpositive) as Hr.
        destruct (wordb w (r mod Z.abs m)) eqn:Hwordr; cbn [gamma_mod].
        * rewrite Z.mod_0_r. split; intros [Hword Hz]; split; [exact Hword| |exact Hword|].
          -- apply (proj1 (cong_mod_abs (z - r) m)).
             apply (proj1 (cong_mod_residue z (Z.abs m) r Hpositive)).
             rewrite Hz. apply Z.mod_0_l. lia.
          -- apply (proj2 (cong_mod_abs (z - r) m)) in Hz.
             apply (proj2 (cong_mod_residue z (Z.abs m) r Hpositive)) in Hz.
             apply (proj1 (cong_large_modulus w _ _ _ Hlarge Hr Hword)) in Hz. lia.
        * split; [contradiction|]. intros [Hword Hz].
          apply (proj2 (cong_mod_abs (z - r) m)) in Hz.
          apply (proj2 (cong_mod_residue z (Z.abs m) r Hpositive)) in Hz.
          apply (proj1 (cong_large_modulus w _ _ _ Hlarge Hr Hword)) in Hz. subst z.
          pose proof (proj2 (cong_wordb_spec w _) Hword). congruence.
      + cbn [gamma_mod]. split; intros [Hword Hz]; split; [exact Hword| |exact Hword|].
        * apply (proj1 (cong_mod_abs (z - r) m)).
          apply (proj1 (cong_mod_residue _ _ _ Hpositive)). exact Hz.
        * apply (proj2 (cong_mod_residue _ _ _ Hpositive)).
          now apply (proj2 (cong_mod_abs (z - r) m)).
  Qed.

  Definition strong_canonical w c : Prop :=
    match c with
    | CBot => True
    | C m r => (m = 0 /\ is_word w r) \/ (0 < m < modulus w /\ 0 <= r < m)
    end.

  Local Lemma cong_norm_canonical w c : strong_canonical w (congr_norm w c).
  Proof.
    destruct c as [|m r]; [exact I|]. rewrite !congr_norm_eq; unfold congr_norm_ref.
    destruct (Z.abs m =? 0) eqn:Hm.
    - destruct (wordb w r) eqn:Hr; cbn; [left; split|exact I];
        [reflexivity|now apply cong_wordb_spec].
    - apply Z.eqb_neq in Hm. pose proof (Z.abs_nonneg m).
      destruct (modulus w <=? Z.abs m) eqn:Hlarge.
      + destruct (wordb w (r mod Z.abs m)) eqn:Hr; cbn;
          [left; split|exact I]; [reflexivity|now apply cong_wordb_spec].
      + apply Z.leb_gt in Hlarge. right. split; [lia|apply Z.mod_pos_bound; lia].
  Qed.

  (** Normalized exact shift counts are nonnegative, so shifting replaces multiplication. *)
  Lemma congr_shl_eq : forall w a b, congr_shl w a b = congr_shl_ref w a b.
  Proof.
    intros w a b. unfold congr_shl, congr_shl_ref.
    destruct (congr_norm w a) as [| m r]; [reflexivity |].
    destruct (congr_norm w b) as [| n k] eqn:Hb; [reflexivity |].
    destruct n as [| n | n]; try reflexivity.
    destruct (Zpos w <=? k); [reflexivity |].
    pose proof (cong_norm_canonical w b) as Hcanonical. rewrite Hb in Hcanonical.
    destruct Hcanonical as [[Hzero Hword] | [Hm Hr]]; [| lia].
    destruct Hword as [Hk Hupper].
    rewrite wrap_class_eq, !Z.shiftl_mul_pow2 by exact Hk. reflexivity.
  Qed.

  Local Lemma cong_canonical_fixed w c : strong_canonical w c -> congr_norm w c = c.
  Proof.
    destruct c as [|m r]; [reflexivity|].
    intros [[-> Hword]|[[Hpositive Hsmall] Hr]]; rewrite !congr_norm_eq; unfold congr_norm_ref.
    - cbn. now rewrite (proj2 (cong_wordb_spec w r) Hword).
    - rewrite Z.abs_eq by lia. rewrite (proj2 (Z.eqb_neq m 0)) by lia.
      rewrite Z.mod_small by exact Hr.
      rewrite (proj2 (Z.leb_gt (modulus w) m)) by lia. reflexivity.
  Qed.

  (** Normalization is idempotent on every raw payload. *)
  Theorem cong_norm_idempotent w c : congr_norm w (congr_norm w c) = congr_norm w c.
  Proof.
    apply cong_canonical_fixed. apply cong_norm_canonical.
  Qed.

  Local Lemma cong_raw_leb_spec m r n s :
    raw_leb (C m r) (C n s) = true <-> (n | m) /\ (n | r - s).
  Proof.
    unfold raw_leb. rewrite andb_true_iff, !Z.eqb_eq, !cong_mod_divide. reflexivity.
  Qed.

  Local Lemma cong_raw_leb_refl c : raw_leb c c = true.
  Proof.
    destruct c as [|m r]; [reflexivity|]. apply cong_raw_leb_spec.
    split; [exists 1|exists 0]; ring.
  Qed.

  Local Lemma cong_raw_leb_trans a b c :
    raw_leb a b = true -> raw_leb b c = true -> raw_leb a c = true.
  Proof.
    destruct a as [|m r], b as [|n s], c as [|p t]; intros Hab Hbc;
      try discriminate; try reflexivity.
    apply cong_raw_leb_spec in Hab as [Hnm Hrs].
    apply cong_raw_leb_spec in Hbc as [Hpn Hst]. apply cong_raw_leb_spec. split.
    - destruct Hnm as [k Hk], Hpn as [j Hj]. exists (k * j). nia.
    - destruct Hrs as [k Hk], Hpn as [j Hj], Hst as [l Hl]. exists (k * j + l). nia.
  Qed.

  Local Lemma cong_raw_leb_gamma w a b z :
    raw_leb a b = true -> gamma_mod w a z -> gamma_mod w b z.
  Proof.
    destruct a as [|m r], b as [|n s]; intros Hle Ha; try contradiction; try discriminate.
    destruct Ha as [Hword Hz]. split; [exact Hword|].
    apply cong_raw_leb_spec in Hle as [Hnm Hrs]. apply cong_mod_divide in Hz.
    apply cong_mod_divide. destruct Hnm as [k Hk], Hrs as [j Hj], Hz as [l Hl].
    exists (l * k + j). nia.
  Qed.

  (** Normalized comparison preserves every word admitted by the left operand. *)
  Theorem cong_gamma_monotone w a b z :
    pleb w a b = true -> gamma_mod w a z -> gamma_mod w b z.
  Proof.
    intros Hle Ha. apply (proj1 (cong_norm_gamma w b z)).
    eapply cong_raw_leb_gamma; [exact Hle|]. now apply (proj2 (cong_norm_gamma w a z)).
  Qed.

  Local Lemma cong_divide_trans a b c : (a | b) -> (b | c) -> (a | c).
  Proof.
    intros [k Hk] [j Hj]. exists (j * k). nia.
  Qed.

  Local Lemma cong_residue_difference m r : (m | r - r mod m).
  Proof.
    destruct (Z.eq_dec m 0) as [->|Hnonzero].
    - rewrite Z.mod_0_r. exists 0. ring.
    - exists (r / m). pose proof (Z.div_mod r m Hnonzero). nia.
  Qed.

  Local Lemma cong_small_norm_equivalent w m r :
    0 <= m < modulus w -> is_word w r ->
    raw_leb (C m r) (congr_norm w (C m r)) = true /\
    raw_leb (congr_norm w (C m r)) (C m r) = true.
  Proof.
    intros Hm Hword. rewrite !congr_norm_eq; unfold congr_norm_ref. rewrite Z.abs_eq by lia.
    destruct (m =? 0) eqn:Hzero.
    - apply Z.eqb_eq in Hzero. subst m.
      rewrite (proj2 (cong_wordb_spec w r) Hword). split; apply cong_raw_leb_refl.
    - rewrite (proj2 (Z.leb_gt (modulus w) m)) by lia.
      split; apply cong_raw_leb_spec; split; try (exists 1; ring).
      + apply cong_residue_difference.
      + destruct (cong_residue_difference m r) as [k Hk]. exists (-k). nia.
  Qed.

  Local Lemma cong_divisor_bound a d : 0 < a -> 0 <= d -> (d | a) -> d <= a.
  Proof.
    intros Ha Hd [k Hk]. destruct (Z.eq_dec d 0) as [->|Hnonzero]; [lia|].
    assert (0 < k) by nia. nia.
  Qed.

  Local Lemma cong_join_modulus_bound w m r n s :
    strong_canonical w (C m r) -> strong_canonical w (C n s) ->
    0 <= Z.gcd (Z.gcd m n) (r - s) < modulus w.
  Proof.
    intros Ha Hb. pose proof (Z.gcd_nonneg (Z.gcd m n) (r - s)) as Hnonnegative.
    assert (Hdm : (Z.gcd (Z.gcd m n) (r - s) | m)).
    { eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_l]. }
    assert (Hdn : (Z.gcd (Z.gcd m n) (r - s) | n)).
    { eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_r]. }
    destruct Ha as [[-> Hr]|[[Hm Hsmall] Hr]].
    - destruct Hb as [[-> Hs]|[[Hn Hsmall] Hs]].
      + change (0 <= Z.abs (r - s) < modulus w).
        destruct Hr, Hs. split; [apply Z.abs_nonneg|apply Z.abs_lt; lia].
      + pose proof (cong_divisor_bound _ _ Hn Hnonnegative Hdn). lia.
    - pose proof (cong_divisor_bound _ _ Hm Hnonnegative Hdm). lia.
  Qed.

  Local Lemma cong_canonical_word_residue w m r :
    strong_canonical w (C m r) -> is_word w r.
  Proof.
    intros [[_ Hword]|[[Hm Hsmall] Hr]]; [exact Hword|]. split; lia.
  Qed.

  Local Lemma cong_raw_join_upper m r n s :
    let c := C (Z.gcd (Z.gcd m n) (r - s)) r in
    raw_leb (C m r) c = true /\ raw_leb (C n s) c = true.
  Proof.
    cbn zeta. split; apply cong_raw_leb_spec; split.
    - eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_l].
    - exists 0. ring.
    - eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_r].
    - destruct (Z.gcd_divide_r (Z.gcd m n) (r - s)) as [k Hk]. exists (-k). nia.
  Qed.

  Local Lemma cong_join_upper w a b :
    pleb w a (pjoin w a b) = true /\ pleb w b (pjoin w a b) = true.
  Proof.
    pose proof (cong_norm_canonical w a) as Ha. pose proof (cong_norm_canonical w b) as Hb.
    unfold pleb, pjoin.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s].
    - split; reflexivity.
    - rewrite (cong_canonical_fixed w _ Hb). split; [reflexivity|apply cong_raw_leb_refl].
    - rewrite (cong_canonical_fixed w _ Ha). split; [apply cong_raw_leb_refl|reflexivity].
    - rewrite cong_norm_idempotent.
      destruct (cong_small_norm_equivalent w _ r (cong_join_modulus_bound w _ _ _ _ Ha Hb)
        (cong_canonical_word_residue w _ _ Ha)) as [Hnorm _].
      destruct (cong_raw_join_upper m r n s) as [Hleft Hright].
      split; eapply cong_raw_leb_trans; eassumption.
  Qed.

  (** Normalized comparison and gcd joins satisfy the lattice laws. *)

  Local Lemma cong_abs_multiple m : (m | Z.abs m).
  Proof.
    destruct m as [|p|p]; [exists 0|exists 1|exists (-1)]; cbn; ring.
  Qed.

  Local Lemma cong_norm_raw_lower w c : raw_leb (congr_norm w c) c = true.
  Proof.
    destruct c as [|m r]; [reflexivity|]. rewrite !congr_norm_eq; unfold congr_norm_ref.
    assert (Hresidue : (m | r mod Z.abs m - r)).
    { eapply cong_divide_trans; [apply cong_abs_multiple|].
      destruct (cong_residue_difference (Z.abs m) r) as [k Hk]. exists (-k). nia. }
    destruct (Z.abs m =? 0) eqn:Hm.
    - apply Z.eqb_eq in Hm. assert (m = 0) by (destruct m; cbn in Hm; congruence).
      subst m. destruct (wordb w r); [apply cong_raw_leb_refl|reflexivity].
    - destruct (modulus w <=? Z.abs m).
      + destruct (wordb w (r mod Z.abs m)); [|reflexivity].
        apply cong_raw_leb_spec. split; [exists 0; ring|exact Hresidue].
      + apply cong_raw_leb_spec. split; [apply cong_abs_multiple|exact Hresidue].
  Qed.


  (** The old remainder formulation is equivalent even at modulus zero. *)
  Lemma gamma_mod_agrees : forall w a z, gamma_mod w a z <-> pgamma w a z.
  Proof.
    intros w [| m r] z; [reflexivity |].
    cbn [gamma_mod pgamma congr_gamma].
    rewrite cong_mod_divide. reflexivity.
  Qed.

  (** Normalization is closed without using a public admission. *)
  Lemma norm_gamma_aux : forall w a z,
    pgamma w (congr_norm w a) z <-> pgamma w a z.
  Proof.
    intros w a z. rewrite <- !gamma_mod_agrees. apply cong_norm_gamma.
  Qed.


  (** Top is fixed by normalization at every positive width. *)
  Lemma cong_top_fixed w : congr_norm w (C 1 0) = C 1 0.
  Proof.
    apply cong_canonical_fixed. right.
    pose proof (one_is_word w) as Hword. unfold is_word in Hword. split; lia.
  Qed.

  Local Lemma cong_modulus_log_bound w m : 0 < m < modulus w ->
    0 <= Z.log2 m < Zpos w.
  Proof.
    intros [Hpositive Hsmall]. split; [apply Z.log2_nonneg|].
    apply (proj1 (Z.log2_lt_pow2 m (Zpos w) Hpositive)). exact Hsmall.
  Qed.

  Local Lemma cong_proper_divisor_log m n :
    0 < m -> 0 < n -> (n | m) -> m <> n -> Z.log2 n < Z.log2 m.
  Proof.
    intros Hm Hn [k Hk] Hdifferent.
    assert (Hpositive : 0 < k) by nia.
    assert (Hnotone : k <> 1) by (intro Heq; subst k; nia).
    assert (Hfactor : 2 <= k) by lia.
    assert (Hdouble : 2 * n <= m) by nia.
    pose proof (Z.log2_le_mono (2 * n) m Hdouble).
    rewrite Z.log2_double in * by exact Hn. lia.
  Qed.

  Local Lemma cong_same_modulus_reverse m r s :
    raw_leb (C m r) (C m s) = true ->
    raw_leb (C m s) (C m r) = true.
  Proof.
    intros Hle. apply cong_raw_leb_spec in Hle as [Hm [k Hk]].
    apply cong_raw_leb_spec. split; [exact Hm|exists (-k); nia].
  Qed.


  (** Raw rank is the decreasing dual of the old increasing height. *)
  Definition raw_wrank (w : positive) (a : congr) : nat :=
    match a with
    | CBot => Pos.to_nat w + 2
    | C m _ => if m =? 0 then Pos.to_nat w + 1 else Z.to_nat (Z.log2 m)
    end.

  (** Every strongly canonical rank fits the requested bound. *)
  Lemma raw_wrank_bound : forall w a, strong_canonical w a ->
    (raw_wrank w a <= Pos.to_nat w + 2)%nat.
  Proof.
    intros w [| m r] Ha; [reflexivity |].
    destruct Ha as [[-> Hr] | [Hm Hr]]; cbn [raw_wrank].
    - change (Pos.to_nat w + 1 <= Pos.to_nat w + 2)%nat. lia.
    - rewrite (proj2 (Z.eqb_neq m 0)) by lia.
      pose proof (cong_modulus_log_bound w m Hm) as Hlog.
      assert (Hwidth : (Z.to_nat (Z.log2 m) < Z.to_nat (Zpos w))%nat).
      { apply Z2Nat.inj_lt; lia. }
      rewrite Z2Nat.inj_pos in Hwidth. lia.
  Qed.

  (** Nonbottom canonical ranks are strictly below the bottom rank. *)
  Lemma raw_wrank_nonbottom : forall w m r, strong_canonical w (C m r) ->
    (raw_wrank w (C m r) < Pos.to_nat w + 2)%nat.
  Proof.
    intros w m r Hcanonical.
    destruct Hcanonical as [[-> Hr] | [Hm Hr]]; cbn [raw_wrank].
    - change (Pos.to_nat w + 1 < Pos.to_nat w + 2)%nat. lia.
    - rewrite (proj2 (Z.eqb_neq m 0)) by lia.
      pose proof (cong_modulus_log_bound w m Hm) as Hlog.
      assert (Hwidth : (Z.to_nat (Z.log2 m) < Z.to_nat (Zpos w))%nat).
      { apply Z2Nat.inj_lt; lia. }
      rewrite Z2Nat.inj_pos in Hwidth. lia.
  Qed.

  (** A proper raw enlargement strictly decreases the normalized rank. *)
  Lemma raw_wrank_strict : forall w a b,
    strong_canonical w a -> strong_canonical w b ->
    raw_leb a b = true -> raw_leb b a = false ->
    (raw_wrank w b < raw_wrank w a)%nat.
  Proof.
    intros w [| m r] [| n s] Ha Hb Hle Hstrict; try discriminate.
    - apply raw_wrank_nonbottom. exact Hb.
    - pose proof Hle as Horder.
      apply cong_raw_leb_spec in Hle as [Hdivisor Hresidue].
      destruct Ha as [[-> Hr] | [Hm Hr]], Hb as [[-> Hs] | [Hn Hs]];
        cbn [raw_wrank]; rewrite ?Z.eqb_refl.
      + pose proof (cong_same_modulus_reverse 0 r s Horder). congruence.
      + rewrite (proj2 (Z.eqb_neq n 0)) by lia.
        pose proof (cong_modulus_log_bound w n Hn) as Hlog.
        assert (Hwidth : (Z.to_nat (Z.log2 n) < Z.to_nat (Zpos w))%nat).
        { apply Z2Nat.inj_lt; lia. }
        rewrite Z2Nat.inj_pos in Hwidth. lia.
      + destruct Hdivisor as [k Hk]. nia.
      + rewrite (proj2 (Z.eqb_neq m 0)), (proj2 (Z.eqb_neq n 0)) by lia.
        assert (Hdifferent : m <> n).
        { intro Hequal. subst n.
          pose proof (cong_same_modulus_reverse m r s Horder). congruence. }
        apply Z2Nat.inj_lt; [apply Z.log2_nonneg | apply Z.log2_nonneg |].
        apply cong_proper_divisor_log; try lia. exact Hdivisor.
  Qed.


  (** A canonical residue is already normalized modulo its own modulus. *)
  Lemma canonical_residue_mod : forall w m r, strong_canonical w (C m r) ->
    r mod m = r.
  Proof.
    intros w m r [[-> Hword] | [Hm Hr]].
    - apply Z.mod_0_r.
    - apply Z.mod_small. exact Hr.
  Qed.

  (** Ordered meet absorbs the narrower normalized input. *)
  Lemma meet_absorbs : forall w a b, pleb w b a = true ->
    pmeet w a b = congr_norm w b.
  Proof.
    intros w a b Horder.
    pose proof (cong_norm_canonical w a) as Ha.
    pose proof (cong_norm_canonical w b) as Hb.
    unfold pleb in Horder. unfold pmeet.
    destruct (congr_norm w a) as [| m r], (congr_norm w b) as [| n s];
      try discriminate; try reflexivity.
    apply cong_raw_leb_spec in Horder as [Hmn Hresidue].
    assert (Hn : 0 <= n) by (destruct Hb as [[-> _] | [Hn _]]; lia).
    assert (Hlcm : Z.lcm m n = n) by (apply Z.divide_lcm_eq_r; assumption).
    assert (Hsm : s mod m = r mod m).
    { apply Z.cong_iff_0. apply cong_mod_divide. exact Hresidue. }
    assert (Hsn : s mod n = s mod n) by reflexivity.
    pose proof (Z.combinecong_complete' s m n r s Hsm Hsn) as Hcompatible.
    rewrite (proj2 (Z.eqb_eq _ _) Hcompatible), CongruenceCRT.combinecong_agrees.
    pose proof (Z.combinecong_complete s m n r s Hsm Hsn) as Hcrt.
    rewrite Hlcm, (canonical_residue_mod w n s Hb) in Hcrt.
    rewrite <- Hcrt, Hlcm. apply cong_canonical_fixed. exact Hb.
  Qed.


  Local Lemma cong_top_sound w z : is_word w z -> gamma_mod w (C 1 0) z.
  Proof.
    intro Hword. split; [exact Hword|apply Z.mod_1_r].
  Qed.

  (** Wrapping retains only a divisor of the word modulus. *)

  Local Lemma cong_wrap_class_sound w m r z : (z - r) mod m = 0 ->
    gamma_mod w (wrap_class w m r) (wrap w z).
  Proof.
    intro Hz. rewrite wrap_class_eq. unfold wrap_class_ref.
    apply (proj2 (cong_norm_gamma w _ _)).
    split; [apply wrap_is_word|]. apply cong_mod_divide. apply cong_mod_divide in Hz.
    pose proof (cong_residue_difference (modulus w) z) as Hwrap.
    rewrite <- wrap_mod in Hwrap.
    destruct (Z.gcd_divide_l m (modulus w)) as [k Hk].
    destruct (Z.gcd_divide_r m (modulus w)) as [j Hj].
    destruct Hz as [l Hl], Hwrap as [n Hn]. exists (l * k - n * j). nia.
  Qed.



  (** Every represented integer is a normalized word. *)
  Lemma gamma_word : forall w a z, pgamma w a z -> is_word w z.
  Proof.
    intros w [| m r] z Ha; [contradiction | exact (proj1 Ha)].
  Qed.

  (** Widening contains both payloads. *)
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof.
    intros q w a b. rewrite pwiden_eq. unfold pwiden_ref. destruct (pleb w b a).
    - apply cong_raw_leb_refl.
    - exact (proj1 (cong_join_upper w a b)).
  Qed.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof.
    intros q w a b. rewrite pwiden_eq. unfold pwiden_ref. destruct (pleb w b a) eqn:Horder.
    - exact Horder.
    - exact (proj2 (cong_join_upper w a b)).
  Qed.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof.
    intros q w a b Hstable. rewrite pwiden_eq. unfold pwiden_ref. now rewrite Hstable.
  Qed.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof.
    intros q w a b Hnonbottom Hunstable.
    rewrite pwiden_eq. unfold pwiden_ref. rewrite Hunstable.
    assert (Hreverse : pleb w (pjoin w a b) a = false).
    { destruct (pleb w (pjoin w a b) a) eqn:Hreverse; [| reflexivity].
      assert (Horder : pleb w b a = true).
      { eapply cong_raw_leb_trans;
          [exact (proj2 (cong_join_upper w a b)) | exact Hreverse]. }
      congruence. }
    change (raw_wrank w (congr_norm w (pjoin w a b)) <
      raw_wrank w (congr_norm w a))%nat.
    apply raw_wrank_strict; try apply cong_norm_canonical.
    - exact (proj1 (cong_join_upper w a b)).
    - exact Hreverse.
  Qed.
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof.
    intros q w a b Hnonbottom.
    destruct (pleb w b a) eqn:Hstable.
    - rewrite pwiden_eq. unfold pwiden_ref. rewrite Hstable. reflexivity.
    - pose proof (pwrank_widen q w a b Hnonbottom Hstable). lia.
  Qed.
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof.
    intros w a b Horder. unfold pnarrow. rewrite meet_absorbs by exact Horder.
    unfold pleb. rewrite cong_norm_idempotent.
    split; [apply cong_raw_leb_refl | exact Horder].
  Qed.
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof.
    intros w a. apply cong_raw_leb_refl.
  Qed.
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof.
    intros w a b c. apply cong_raw_leb_trans.
  Qed.
  (** Bottom is below every payload. *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof.
    intro w. intro a. reflexivity.
  Qed.
  (** Top is above every payload. *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof.
    intros w a. unfold pleb, ptop. rewrite cong_top_fixed.
    destruct (congr_norm w a); [reflexivity |].
    cbn [raw_leb]. rewrite !Z.mod_1_r. reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof.
    intro w. reflexivity.
  Qed.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof.
    intros w a b Hbot. unfold pleb, pis_bot in *.
    destruct (congr_norm w a); [reflexivity | discriminate].
  Qed.
  (** Join contains the left payload. *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof.
    intros w a b. exact (proj1 (cong_join_upper w a b)).
  Qed.
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof.
    intros w a b. exact (proj2 (cong_join_upper w a b)).
  Qed.
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof.
    intros w a b.
    unfold pleb, pmeet.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s]; try reflexivity.
    destruct (r mod Z.gcd m n =? s mod Z.gcd m n) eqn:Hcompatible; [|reflexivity].
    rewrite CongruenceCRT.combinecong_agrees, cong_norm_idempotent.
    eapply cong_raw_leb_trans; [apply cong_norm_raw_lower|].
    apply cong_raw_leb_spec. split; [apply Z.divide_lcm_l|].
    apply cong_mod_divide. apply Z.cong_iff_0.
    exact (proj1 (Z.combinecong_sound m n r s (proj1 (Z.eqb_eq _ _) Hcompatible))).
  Qed.
  (** Meet refines the right payload. *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof.
    intros w a b.
    unfold pleb, pmeet.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s]; try reflexivity.
    destruct (r mod Z.gcd m n =? s mod Z.gcd m n) eqn:Hcompatible; [|reflexivity].
    rewrite CongruenceCRT.combinecong_agrees, cong_norm_idempotent.
    eapply cong_raw_leb_trans; [apply cong_norm_raw_lower|].
    apply cong_raw_leb_spec. split; [apply Z.divide_lcm_r|].
    apply cong_mod_divide. apply Z.cong_iff_0.
    exact (proj2 (Z.combinecong_sound m n r s (proj1 (Z.eqb_eq _ _) Hcompatible))).
  Qed.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof.
    intros w a b z Hle Ha. rewrite <- !gamma_mod_agrees in *.
    eapply cong_gamma_monotone; eassumption.
  Qed.
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof.
    intros w z H. exact H.
  Qed.
  (** Top contains every normalized integer at its width. *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof.
    intros w z Hword. split; [exact Hword |]. exists z. ring.
  Qed.
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof.
    intros w a b z Ha Hb. rewrite <- !gamma_mod_agrees in *.
    apply (proj2 (cong_norm_gamma w a z)) in Ha.
    apply (proj2 (cong_norm_gamma w b z)) in Hb. unfold pmeet.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s]; try contradiction.
    destruct Ha as [Hword Hr], Hb as [_ Hs].
    apply <- Z.cong_iff_0 in Hr. apply <- Z.cong_iff_0 in Hs.
    pose proof (Z.combinecong_complete' z m n r s Hr Hs) as Hcompatible.
    rewrite (proj2 (Z.eqb_eq _ _) Hcompatible).
    rewrite CongruenceCRT.combinecong_agrees.
    apply (proj2 (cong_norm_gamma w _ z)). split; [exact Hword|].
    apply Z.cong_iff_0. rewrite Z.mod_combinecong_lcm. now apply Z.combinecong_complete.
  Qed.
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof.
    intros w a z Hbot Ha. apply (proj2 (norm_gamma_aux w a z)) in Ha.
    unfold pis_bot in Hbot. destruct (congr_norm w a); [exact Ha | discriminate].
  Qed.
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof.
    intros w a b Horder Hbot. unfold pleb, pis_bot in *.
    destruct (congr_norm w a), (congr_norm w b); try reflexivity; discriminate.
  Qed.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof.
    intros. split; [apply wrap_is_word|]. rewrite Z.sub_diag. reflexivity.
  Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof.
    intros w a z v Hpoint Hword Ha. apply (proj2 (norm_gamma_aux w a z)) in Ha.
    unfold ppoint in Hpoint. destruct (congr_norm w a) as [| [| m | m] r];
      try discriminate.
    injection Hpoint as <-. destruct Ha as [_ [k Hk]]. lia.
  Qed.
  (** Payload concretization agrees with residue-class membership. *)
  Lemma gamma_def : forall w a z, pgamma w a z <-> congr_gamma w a z.
  Proof.
    intros w a z. reflexivity.
  Qed.
  (** Normalization keeps precisely the same represented integers. *)
  Lemma norm_gamma : forall w a z,
    pgamma w (congr_norm w a) z <-> pgamma w a z.
  Proof.
    apply norm_gamma_aux.
  Qed.
  (** Negation retains wrapped concrete negation. *)
  Lemma congr_neg_sound : forall w a x,
    pgamma w a x -> pgamma w (congr_neg w a) (L.wrap w (- x)).
  Proof.
    intros w a x Ha. rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a x)) in Ha.
    unfold congr_neg. destruct (congr_norm w a) as [|m r]; [contradiction|].
    destruct Ha as [_ Hresidue]. apply cong_wrap_class_sound.
    apply cong_mod_divide. apply cong_mod_divide in Hresidue.
    destruct Hresidue as [k Hk]. exists (-k). nia.
  Qed.
  (** Addition retains wrapped concrete addition. *)
  Lemma congr_add_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_add w a b) (L.wrap w (x + y)).
  Proof.
    intros w a b x y Ha Hb. rewrite <- !gamma_mod_agrees in *.
    apply (proj2 (cong_norm_gamma w a x)) in Ha.
    apply (proj2 (cong_norm_gamma w b y)) in Hb.
    rewrite congr_add_eq. unfold congr_add_ref.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s]; try contradiction.
    destruct Ha as [_ Hx], Hb as [_ Hy]. rewrite <- wrap_class_eq.
    apply cong_wrap_class_sound.
    apply cong_mod_divide. apply cong_mod_divide in Hx. apply cong_mod_divide in Hy.
    destruct Hx as [i Hi], Hy as [j Hj].
    destruct (Z.gcd_divide_l m n) as [k Hk], (Z.gcd_divide_r m n) as [l Hl].
    exists (i * k + j * l). nia.
  Qed.
  (** Subtraction retains wrapped concrete subtraction. *)
  Lemma congr_sub_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_sub w a b) (L.wrap w (x - y)).
  Proof.
    intros w a b x y Ha Hb. rewrite <- !gamma_mod_agrees in *.
    apply (proj2 (cong_norm_gamma w a x)) in Ha.
    apply (proj2 (cong_norm_gamma w b y)) in Hb.
    rewrite congr_sub_eq. unfold congr_sub_ref.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s]; try contradiction.
    destruct Ha as [_ Hx], Hb as [_ Hy]. rewrite <- wrap_class_eq.
    apply cong_wrap_class_sound.
    apply cong_mod_divide. apply cong_mod_divide in Hx. apply cong_mod_divide in Hy.
    destruct Hx as [i Hi], Hy as [j Hj].
    destruct (Z.gcd_divide_l m n) as [k Hk], (Z.gcd_divide_r m n) as [l Hl].
    exists (i * k - j * l). nia.
  Qed.
  (** Multiplication retains wrapped concrete multiplication. *)
  Lemma congr_mul_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_mul w a b) (L.wrap w (x * y)).
  Proof.
    intros w a b x y Ha Hb. rewrite <- !gamma_mod_agrees in *.
    apply (proj2 (cong_norm_gamma w a x)) in Ha.
    apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold congr_mul.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s]; try contradiction.
    destruct Ha as [_ Hx], Hb as [_ Hy]. apply cong_wrap_class_sound.
    apply cong_mod_divide. apply cong_mod_divide in Hx. apply cong_mod_divide in Hy.
    destruct Hx as [i Hi], Hy as [j Hj].
    pose (g := Z.gcd (m * n) (Z.gcd (m * s) (n * r))).
    assert (Hmn : (g | m * n)) by apply Z.gcd_divide_l.
    assert (Hms : (g | m * s)).
    { eapply cong_divide_trans; [apply Z.gcd_divide_r|apply Z.gcd_divide_l]. }
    assert (Hnr : (g | n * r)).
    { eapply cong_divide_trans; [apply Z.gcd_divide_r|apply Z.gcd_divide_r]. }
    destruct Hmn as [k Hk], Hms as [l Hl], Hnr as [p Hp].
    exists (i * j * k + i * l + j * p).
    replace (x * y - r * s) with (i * j * (m * n) + i * (m * s) + j * (n * r)) by nia.
    fold g. rewrite Hk, Hl, Hp. ring.
  Qed.
  (** Projection retains truncations to smaller widths. *)
  Lemma congr_project_sound : forall source target a x,
    (target <= source)%positive -> pgamma source a x ->
    pgamma target (congr_project source target a) (L.wrap target x).
  Proof.
    intros source target a x Hwidth Ha. rewrite <- !gamma_mod_agrees in *.
    apply (proj2 (cong_norm_gamma source a x)) in Ha.
    unfold congr_project. destruct (congr_norm source a) as [|m r]; [contradiction|].
    apply cong_wrap_class_sound. exact (proj2 Ha).
  Qed.
  (** Shift transfer retains the wrapped concrete shift. *)
  Lemma congr_shl_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y ->
    pgamma w (congr_shl w a b) (L.wrap w (Z.shiftl x y)).
  Proof.
    intros w a b x y Ha Hb.
    rewrite normalized_wshl by (eapply gamma_word; eassumption).
    rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a x)) in Ha.
    apply (proj2 (cong_norm_gamma w b y)) in Hb.
    rewrite congr_shl_eq. unfold congr_shl_ref.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n k]; try contradiction.
    destruct n as [|n|n]; try (apply cong_top_sound; apply wshl_is_word).
    destruct Ha as [Hwordx Hx], Hb as [Hwordy Hy].
    rewrite Z.mod_0_r in Hy. assert (y = k) by lia. subst y.
    rewrite wshl_value, (wrap_id w k Hwordy), (wrap_id w x Hwordx).
    destruct (Zpos w <=? k).
    - split; [apply zero_is_word|reflexivity].
    - rewrite <- wrap_class_eq. apply cong_wrap_class_sound.
      apply cong_mod_divide. apply cong_mod_divide in Hx.
      destruct Hx as [i Hi]. exists i. nia.
  Qed.
  (** Remainder transfer retains unsigned remainder, including a zero divisor. *)
  Lemma congr_urem_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y ->
    pgamma w (congr_urem w a b) (L.wrap w (Z.modulo x y)).
  Proof.
    intros w a b x y Ha Hb.
    rewrite normalized_wurem by (eapply gamma_word; eassumption).
    rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a x)) in Ha.
    apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold congr_urem.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n c]; try contradiction.
    destruct n as [|n|n]; try (apply cong_top_sound; apply wurem_is_word).
    destruct Ha as [Hwordx Hx], Hb as [Hwordy Hy].
    rewrite Z.mod_0_r in Hy. assert (y = c) by lia. subst y.
    apply (proj2 (cong_norm_gamma w _ _)). split; [apply wurem_is_word|].
    rewrite wurem_mod, (wrap_id w c Hwordy), (wrap_id w x Hwordx).
    apply cong_mod_divide in Hx. apply cong_mod_divide.
    destruct (Z.gcd_divide_l m c) as [k Hk], (Z.gcd_divide_r m c) as [j Hj].
    destruct Hx as [i Hi]. destruct (Z.eq_dec c 0) as [->|Hnonzero].
    - rewrite Z.mod_0_r. exists (i * k). nia.
    - destruct (cong_residue_difference c x) as [l Hl]. exists (i * k - l * j). nia.
  Qed.
End Congruence.

Module CongruenceTable (L : WORD_LANGUAGE) (W : CONGRUENCE L) <: CONGRUENCE_TABLE L W.
  Include CongruenceTableCode L W.

  (** Widening the word range preserves the same residue membership. *)
  Local Lemma zext_sound : forall source target a x,
    (source <= target)%positive -> W.pgamma source a x ->
    W.pgamma target (W.congr_norm target a) x.
  Proof.
    intros source target a x Hwidth Ha.
    apply (proj2 (W.norm_gamma target a x)).
    apply (proj2 (W.gamma_def target a x)).
    apply (proj1 (W.gamma_def source a x)) in Ha.
    destruct a as [| m r]; [contradiction |].
    destruct Ha as [Hword Hresidue]. split; [| exact Hresidue].
    eapply word_widen; eassumption.
  Qed.

  (** Unary entries preserve normalized negation, extension and truncation. *)
  Local Lemma unary_sound : forall o rw w a cs z r,
    wfwd o rw [(w, a)] = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) [(w, a)] cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros o rw w a cs z r Hf Hcs Heval.
    inversion Hcs as [| ? [v x] ? ? Hhead Hnil]; subst.
    inversion Hnil; subst. destruct Hhead as [Hv [Hx Ha]].
    cbn [fst snd] in Hv, Hx, Ha. subst v.
    change (eval_op o [(w, x)] = Some (rw, z)) in Heval.
    destruct o; cbn [wfwd] in Hf; try discriminate.
    - pose proof (eq_trans
        (eq_sym (eval_op_fun1 bvneg w x UNeg eq_refl)) Heval) as Hresult.
      inversion Hresult; subst rw z. rewrite Pos.eqb_refl in Hf.
      injection Hf as <-. cbn [eval_unary_tag]. rewrite wneg_value.
      now apply W.congr_neg_sound.
    - rewrite eval_zext_value in Heval. inversion Heval; subst rw z.
      rewrite (proj2 (Pos.leb_le _ _)) in Hf by apply width_add_le.
      injection Hf as <-. rewrite (wrap_id w x Hx).
      eapply zext_sound; [apply width_add_le | exact Ha].
    - rewrite eval_op_trunc in Heval.
      match type of Heval with
      | context [if Pos.leb ?target w then _ else _] =>
        destruct (Pos.leb target w) eqn:Hwidth
      end; [| discriminate].
      inversion Heval; subst rw z. injection Hf as <-.
      rewrite (wrap_id w x Hx). apply W.congr_project_sound.
      + now apply Pos.leb_le.
      + exact Ha.
  Qed.

  (** Binary entries preserve each supported arithmetic operator. *)
  Local Lemma binary_sound : forall o rw wa a wb b cs z r,
    wfwd o rw [(wa, a); (wb, b)] = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) [(wa, a); (wb, b)] cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros o rw wa a wb b cs z r Hf Hcs Heval.
    inversion Hcs as [| ? [wx x] ? ? Hhead Htail]; subst.
    inversion Htail as [| ? [wy y] ? ? Hhead' Hnil]; subst.
    inversion Hnil; subst.
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hwy [Hy Hb]].
    cbn [fst snd] in Hwx, Hwy, Hx, Hy, Ha, Hb. subst wx wy.
    change (eval_op o [(wa, x); (wb, y)] = Some (rw, z)) in Heval.
    destruct o; cbn [wfwd] in Hf; try discriminate.
    all: match type of Heval with
    | eval_op ?operation _ = _ =>
      assert (Hwidth : wa = wb) by
        (eapply (eval_op_fun2_width operation); [reflexivity | exact Heval]);
      subst wb;
      pose proof (eq_trans
        (eq_sym (eval_op_fun2 operation wa x y _ eq_refl)) Heval) as Hresult;
      inversion Hresult; subst rw z;
      rewrite !Pos.eqb_refl in Hf; injection Hf as <-;
      cbn [eval_binary_tag]
    end.
    - rewrite wadd_value. now apply W.congr_add_sound.
    - rewrite wsub_value. now apply W.congr_sub_sound.
    - rewrite wmul_value. now apply W.congr_mul_sound.
    - rewrite <- (normalized_wurem wa x y Hx Hy). now apply W.congr_urem_sound.
    - rewrite <- (normalized_wshl wa x y Hx Hy). now apply W.congr_shl_sound.
  Qed.

  (** Selection retains the chosen branch through the branch join. *)
  Local Lemma select_sound : forall o rw wc a wa b wb c cs z r,
    wfwd o rw [(wc, a); (wa, b); (wb, c)] = Some r ->
    Forall2 (fun wp v => fst wp = fst v /\ L.is_word (fst v) (snd v) /\
      W.pgamma (fst wp) (snd wp) (snd v)) [(wc, a); (wa, b); (wb, c)] cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros o rw wc a wa b wb c cs z r Hf Hcs Heval.
    destruct o; cbn [wfwd] in Hf; try discriminate.
    inversion Hcs as [| ? [wx x] ? ? Hhead Htail]; subst.
    inversion Htail as [| ? [wy y] ? ? Hhead' Htail']; subst.
    inversion Htail' as [| ? [wt t] ? ? Hhead'' Hnil]; subst.
    inversion Hnil; subst.
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hwy [Hy Hb]],
      Hhead'' as [Hwt [Ht Hc]].
    cbn [fst snd] in Hwx, Hwy, Hwt, Hx, Hy, Ht, Ha, Hb, Hc. subst wx wy wt.
    change (eval_op bvite [(wc, x); (wa, y); (wb, t)] = Some (rw, z)) in Heval.
    destruct (eval_op_ite_width wc wa wb x y t (rw, z) Heval) as [Hwc Hab].
    subst wc wb. rewrite eval_op_ite in Heval.
    destruct (wrap 1%positive x =? 1); inversion Heval; subst rw z;
      rewrite !Pos.eqb_refl in Hf; injection Hf as <-.
    - rewrite (wrap_id wa y Hy).
      eapply W.pgamma_mono; [apply W.pjoin_ub_l | exact Hb].
    - rewrite (wrap_id wa t Ht).
      eapply W.pgamma_mono; [apply W.pjoin_ub_r | exact Hc].
  Qed.

  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros o rw wps cs z r Hf Hcs Heval.
    destruct wps as [| [w a] [| [v b] [| [u c] [| wp rest]]]].
    - destruct o; discriminate Hf.
    - eapply unary_sound; eassumption.
    - eapply binary_sound; eassumption.
    - eapply select_sound; eassumption.
    - destruct o; discriminate Hf.
  Qed.
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. intros o rw q wps ys cs z Hf. discriminate Hf. Qed.
End CongruenceTable.

Module CongruenceT (L : WORD_LANGUAGE_T) <: CONGRUENCE_ALL L.
  Include Congruence L.
  Definition div_aligned := CongruenceCRT.div_aligned.
  Definition extgcd := CongruenceCRT.extgcd.
  Definition T_div_aligned := CongruenceCRT.T_div_aligned.
  Definition T_extgcd := CongruenceCRT.T_extgcd.
  Definition k_div := CongruenceCRT.k_div.
  Definition k_gcd := CongruenceCRT.k_gcd.
  Definition div_aligned_def := CongruenceCRT.div_aligned_def.
  Definition extgcd_agrees := CongruenceCRT.extgcd_agrees.
  Definition T_div_aligned_le := CongruenceCRT.T_div_aligned_le.
  Definition T_extgcd_le := CongruenceCRT.T_extgcd_le.
  TimeFun wordb.
  TimeFun congr_norm.
  TimeFun raw_leb.
  TimeFun pleb.
  TimeFun pjoin.
  TimeFun join_norm.
  TimeFun pmeet.
  TimeFun pbot.
  TimeFun ptop.
  TimeFun pis_bot.
  TimeFun pconst.
  TimeFun ppoint.
  TimeFun pwiden.
  TimeFun pnarrow.
  TimeFun wrap_class.
  TimeFun congr_neg.
  TimeFun congr_add.
  TimeFun congr_sub.
  TimeFun congr_mul.
  TimeFun congr_project.
  TimeFun congr_shl.
  TimeFun congr_urem.
  Definition psize (w : positive) (a : p) : nat :=
    (Pos.to_nat w + congr_bits a + 1) ^ 2.
  Definition pwsize (_ : pwparam) : nat := 0.
  Definition c_payload : N := 1073741824%N.
  Definition c_congruence : N := 1048576%N.
  Definition k_congr_gcd : N := 1048576%N.
  Definition k_congr_crt : N := 268435456%N.
  Definition k_congr_transfer : N := 1048576%N.

  (** Word recognition charges a modulus construction and a linear comparison. *)
  Lemma wordb_time_budget : forall w z n,
    (Pos.to_nat w + Z.size_nat z + 1 <= n)%nat ->
    (T_wordb w z <= 32 * N.of_nat n)%N.
  Proof.
    intros w z n Hsize.
    pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
    pose proof (Z.T_leb_le 0 z) as Hnonnegative.
    pose proof (Z.T_ltb_le z (modulus w)) as Hupper.
    pose proof (Datatypes.T_andb_le (0 <=? z) (z <? modulus w)) as Hboth.
    apply time_of_nat_le in Hsize. rewrite !Nat2N.inj_add in *.
    time_unfold T_wordb. time_cbn_all. lia.
  Qed.

  (** A shared bit budget bounds every arithmetic call made by normalization. *)
  Lemma normalization_time_budget : forall w a n,
    (Pos.to_nat w + congr_bits a + 1 <= n)%nat ->
    (T_congr_norm w a <= 128 * N.of_nat (n ^ 2))%N.
  Proof.
    intros w [|m r] n Hsize.
    - assert (Hpositive : (1 <= n)%nat) by (cbn [congr_bits] in Hsize; lia).
      pose proof (linear_le_square n Hpositive) as Hlinear.
      assert (Hone : (1 <= N.of_nat n)%N).
      { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
      time_unfold T_congr_norm. lia.
    - cbn [congr_bits] in Hsize.
      assert (Hpositive : (1 <= n)%nat) by lia.
      pose proof (linear_le_square n Hpositive) as Hlinear.
      assert (Hone : (1 <= N.of_nat n)%N).
      { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
      pose proof (Z.T_abs_le m) as Habs.
      pose proof (eqb_time_budget n (Z.abs m) 0
        ltac:(rewrite CongruenceCRT.integer_abs_size; lia)) as Hzero.
      pose proof (mod_time_budget n r (Z.abs m)
        ltac:(rewrite CongruenceCRT.integer_abs_size; lia)) as Hremainder.
      pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
      pose proof (WordTime.word_modulus_size_bound w) as Hmodsize.
      apply time_of_nat_le in Hmodsize.
      pose proof (Z.T_leb_le (modulus w) (Z.abs m)) as Hlarge.
      pose proof (wordb_time_budget w r n ltac:(lia)) as Hword.
      pose proof (integer_modulo_size r (Z.abs m)) as Hrembits.
      rewrite CongruenceCRT.integer_abs_size in Hrembits.
      pose proof (wordb_time_budget w (r mod Z.abs m) n ltac:(lia)) as Hremword.
      pose proof (Z.T_leb_le 0 r) as Hnonnegative.
      pose proof (Z.T_ltb_le r (Z.abs m)) as Hsmall.
      assert (Hrsize : (N.of_nat (Z.size_nat r + 1) <= N.of_nat n)%N).
      { apply time_of_nat_le. lia. }
      assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= N.of_nat n)%N).
      { apply time_of_nat_le. lia. }
      time_unfold T_congr_norm. cbn beta zeta.
      destruct (Z.abs m =? 0), (0 <=? r), (r <? Z.abs m),
        (modulus w <=? Z.abs m); cbn beta iota zeta;
        rewrite ?Nat2N.inj_add in Hrsize; time_cbn_all; lia.
  Qed.

  (** Canonical inputs take only comparisons and the word test during normalization. *)
  Lemma normalization_time_linear : forall w a,
    canonical w a ->
    (T_congr_norm w a <=
      128 * N.of_nat (Pos.to_nat w + congr_bits a + 1))%N.
  Proof.
    intros w [| m r] Hcanonical.
    - time_unfold T_congr_norm. cbn [congr_bits].
      rewrite Nat2N.inj_add. cbn [N.of_nat]. lia.
    - cbn [canonical congr_bits] in *.
      remember (Pos.to_nat w + (Z.size_nat m + Z.size_nat r) + 1)%nat as n eqn:Hn.
      pose proof (Z.T_abs_le m) as Habs.
      pose proof (eqb_time_budget n (Z.abs m) 0
        ltac:(rewrite CongruenceCRT.integer_abs_size; lia)) as Hzero.
      pose proof (Z.T_leb_le 0 r) as Hnonnegative.
      pose proof (Z.T_ltb_le r (Z.abs m)) as Hsmall.
      pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
      pose proof (WordTime.word_modulus_size_bound w) as Hmodsize.
      pose proof (Z.T_leb_le (modulus w) (Z.abs m)) as Hlarge.
      pose proof (wordb_time_budget w r n ltac:(lia)) as Hword.
      assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= N.of_nat n)%N).
      { apply time_of_nat_le. lia. }
      assert (Hrsize : (N.of_nat (Z.size_nat r + 1) <= N.of_nat n)%N).
      { apply time_of_nat_le. lia. }
      apply time_of_nat_le in Hmodsize.
      rewrite !Nat2N.inj_add in *.
      time_unfold T_congr_norm. cbn beta zeta.
      destruct Hcanonical as [[-> Hr] | [Hm Hr]].
      + cbn [Z.abs Z.eqb] in *. time_cbn_all. lia.
      + rewrite Z.abs_eq in * by lia.
        rewrite (proj2 (Z.eqb_neq m 0) ltac:(lia)).
        rewrite (proj2 (Z.leb_le 0 r) ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt r m) ltac:(lia)).
        destruct (modulus w <=? m); time_cbn_all; lia.
  Qed.

  (** A shared modulus and two masks give a linear wrapping budget. *)
  Lemma wrap_class_time_linear : forall w m r n,
    (Pos.to_nat w + Z.size_nat m + Z.size_nat r + 1 <= n)%nat ->
    (T_wrap_class w m r <= 512 * N.of_nat n)%N.
  Proof.
    intros w m r n Hinput.
    pose proof (WordTime.word_modulus_size_bound w) as Hmodsize.
    pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
    pose proof (pow2_gcd_size w m) as Hgsize.
    rewrite <- pow2_gcd_at_eq in Hgsize.
    pose proof (pow2_gcd_at_time (modulus w) m) as Hgcd.
    pose proof (wrap_class_at_time (modulus w) (pow2_gcd_at (modulus w) m) r)
      as Hwrap.
    assert (Hmasksize :
      (Z.size_nat (modulus w) + Z.size_nat (pow2_gcd_at (modulus w) m) +
        Z.size_nat r + 1 <= 3 * n)%nat) by lia.
    assert (Hinputsize : (Z.size_nat m + 1 <= n)%nat) by lia.
    assert (Hwidth : (Pos.to_nat w + 1 <= n)%nat) by lia.
    apply time_of_nat_le in Hmasksize, Hinputsize, Hwidth.
    rewrite Nat2N.inj_mul in Hmasksize. change (N.of_nat 3) with 3%N in Hmasksize.
    time_unfold T_wrap_class. lia.
  Qed.

  (** The linear masking budget also meets the existing quadratic wrapping contract. *)
  Lemma wrap_class_time_budget : forall w m r n,
    (Pos.to_nat w + Z.size_nat m + Z.size_nat r + 1 <= n)%nat ->
    (T_wrap_class w m r <= 1024 * N.of_nat (n ^ 2))%N.
  Proof.
    intros w m r n Hinput.
    pose proof (wrap_class_time_linear w m r n Hinput) as Hwrap.
    pose proof (linear_le_square n ltac:(lia)) as Hlinear. lia.
  Qed.

  (** Two class moduli share one word modulus and one final residue mask. *)
  Lemma masked_pair_time_budget : forall w m p r n,
    (Pos.to_nat w + Z.size_nat m + Z.size_nat p + Z.size_nat r + 1 <= n)%nat ->
    (Word.T_modulus w + T_pow2_gcd_at (modulus w) m +
      T_pow2_gcd_at (modulus w) p +
      Z.T_min (pow2_gcd_at (modulus w) m) (pow2_gcd_at (modulus w) p) +
      T_wrap_class_at (modulus w)
        (Z.min (pow2_gcd_at (modulus w) m) (pow2_gcd_at (modulus w) p)) r <=
      512 * N.of_nat n)%N.
  Proof.
    intros w m p r n Hinput.
    pose proof (WordTime.word_modulus_time_bound w) as Hmodulus.
    pose proof (WordTime.word_modulus_size_bound w) as Hmodsize.
    pose proof (pow2_gcd_size w m) as Hmbits.
    pose proof (pow2_gcd_size w (Z.gcd m p)) as Hminbits.
    rewrite pow2_gcd_gcd in Hminbits.
    change (Z.size_nat (pow2_gcd_at (modulus w) m) <= Pos.to_nat w + 1)%nat in Hmbits.
    change (Z.size_nat (Z.min (pow2_gcd_at (modulus w) m)
      (pow2_gcd_at (modulus w) p)) <= Pos.to_nat w + 1)%nat in Hminbits.
    pose proof (pow2_gcd_at_time (modulus w) m) as Hm.
    pose proof (pow2_gcd_at_time (modulus w) p) as Hp.
    pose proof (Z.T_min_le (pow2_gcd_at (modulus w) m)
      (pow2_gcd_at (modulus w) p)) as Hmin.
    pose proof (wrap_class_at_time (modulus w)
      (Z.min (pow2_gcd_at (modulus w) m) (pow2_gcd_at (modulus w) p)) r) as Hwrap.
    assert (Hmasksize :
      (Z.size_nat (modulus w) +
        Z.size_nat (Z.min (pow2_gcd_at (modulus w) m) (pow2_gcd_at (modulus w) p)) +
        Z.size_nat r + 1 <= 3 * n)%nat) by lia.
    apply time_of_nat_le in Hinput, Hmbits, Hmasksize.
    rewrite !Nat2N.inj_add, ?Nat2N.inj_mul in *.
    change (N.of_nat 3) with 3%N in Hmasksize. time_cbn_all. lia.
  Qed.

  (** Strong canonicality bounds both stored integers by the word width. *)
  Lemma canonical_bits : forall w a, strong_canonical w a ->
    (congr_bits a <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w [|m r] Hcanonical; [cbn [congr_bits]; lia|].
    destruct Hcanonical as [[-> Hr]|[Hm Hr]].
    - pose proof (WordTime.word_size_bound w r Hr).
      cbn [congr_bits Z.size_nat]. lia.
    - assert (Hmw : is_word w m) by (unfold is_word; lia).
      assert (Hrw : is_word w r) by (unfold is_word; lia).
      pose proof (WordTime.word_size_bound w m Hmw).
      pose proof (WordTime.word_size_bound w r Hrw).
      cbn [congr_bits]. lia.
  Qed.

  (** Every normalization result satisfies the stronger representation invariant. *)
  Lemma normalized_bits : forall w a,
    (congr_bits (congr_norm w a) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a. apply canonical_bits, cong_norm_canonical.
  Qed.

  (** A join either reuses a normalized operand or normalizes its gcd class. *)
  Lemma join_bits : forall w a b,
    (congr_bits (pjoin w a b) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a b. unfold pjoin.
    pose proof (normalized_bits w a) as Ha.
    pose proof (normalized_bits w b) as Hb.
    destruct (congr_norm w a), (congr_norm w b); try assumption.
    apply normalized_bits.
  Qed.

  (** Successful CRT meets are normalized before being returned. *)
  Lemma meet_bits : forall w a b,
    (congr_bits (pmeet w a b) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a b. unfold pmeet.
    destruct (congr_norm w a), (congr_norm w b); cbn [congr_bits]; try lia.
    destruct (r mod Z.gcd m m0 =? r0 mod Z.gcd m m0).
    - apply normalized_bits.
    - cbn [congr_bits]. lia.
  Qed.

  (** Two width-bounded integers give a quadratic payload-size bound. *)
  Lemma bounded_payload_size : forall w a,
    (congr_bits a <= 2 * Pos.to_nat w)%nat ->
    (psize w a <= 9 * (Pos.to_nat w + 1) ^ 2)%nat.
  Proof.
    intros w a Hbits. unfold psize.
    replace (9 * (Pos.to_nat w + 1) ^ 2)%nat with
      ((3 * (Pos.to_nat w + 1)) ^ 2)%nat by (rewrite Nat.pow_mul_l; reflexivity).
    apply Nat.pow_le_mono_l. lia.
  Qed.

  (** Every payload budget includes the width contribution. *)
  Lemma payload_width_size : forall w a,
    ((Pos.to_nat w + 1) ^ 2 <= psize w a)%nat.
  Proof.
    intros w a. unfold psize. apply Nat.pow_le_mono_l. lia.
  Qed.

  (** A common raw bit budget pays both input normalizations and the inclusion test. *)
  Lemma inclusion_time_budget : forall w a b n,
    (Pos.to_nat w + congr_bits a + congr_bits b + 1 <= n)%nat ->
    (T_pleb w a b <= 8192 * N.of_nat (n ^ 2))%N.
  Proof.
    intros w a b n Hinput.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Hnorma.
    pose proof (normalization_time_budget w b n ltac:(lia)) as Hnormb.
    assert (Hpositive : (1 <= n)%nat) by lia.
    pose proof (linear_le_square n Hpositive) as Hlinear.
    assert (Hone : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
    time_unfold T_pleb.
    destruct (congr_norm w a) as [|m r] eqn:Haform;
      destruct (congr_norm w b) as [|p s] eqn:Hbform;
      time_unfold T_raw_leb; cbn beta iota zeta; try lia.
    pose proof (normalized_bits w a) as Ha. rewrite Haform in Ha.
    pose proof (normalized_bits w b) as Hb. rewrite Hbform in Hb.
    cbn [congr_bits] in Ha, Hb.
    pose proof (WordTime.integer_sub_size r s) as Hdifference.
    pose proof (integer_modulo_size m p) as Hmodulus.
    pose proof (integer_modulo_size (r - s) p) as Hresidue.
    pose proof (sub_time_budget (4 * n) r s ltac:(lia)) as Hsubtract.
    pose proof (mod_time_budget (4 * n) m p ltac:(lia)) as Hmodm.
    pose proof (mod_time_budget (6 * n) (r - s) p ltac:(lia)) as Hmodr.
    pose proof (eqb_time_budget (5 * n) (m mod p) 0 ltac:(lia)) as Heqm.
    pose proof (eqb_time_budget (6 * n) ((r - s) mod p) 0 ltac:(lia)) as Heqr.
    pose proof (Datatypes.T_andb_le (m mod p =? 0) ((r - s) mod p =? 0)) as Hboth.
    rewrite !Nat.pow_mul_l, !Nat2N.inj_mul in *. cost_constants. lia.
  Qed.

  (** Joining normalizes a gcd class built from bounded canonical operands. *)
  Lemma join_time_budget : forall w a b n,
    (Pos.to_nat w + congr_bits a + congr_bits b + 1 <= n)%nat ->
    (T_pjoin w a b <= 32768 * N.of_nat (n ^ 2))%N.
  Proof.
    intros w a b n Hinput.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Hnorma.
    pose proof (normalization_time_budget w b n ltac:(lia)) as Hnormb.
    assert (Hpositive : (1 <= n)%nat) by lia.
    pose proof (linear_le_square n Hpositive) as Hlinear.
    assert (Hone : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
    time_unfold T_pjoin.
    destruct (congr_norm w a) as [|m r] eqn:Haform;
      destruct (congr_norm w b) as [|p s] eqn:Hbform; cbn beta iota zeta; try lia.
    pose proof (normalized_bits w a) as Ha. rewrite Haform in Ha.
    pose proof (normalized_bits w b) as Hb. rewrite Hbform in Hb.
    cbn [congr_bits] in Ha, Hb.
    pose proof (WordTime.integer_sub_size r s) as Hdifference.
    pose proof (integer_gcd_size m p) as Hgcd1.
    pose proof (integer_gcd_size (Z.gcd m p) (r - s)) as Hgcd2.
    pose proof (sub_time_budget (4 * n) r s ltac:(lia)) as Hsubtract.
    pose proof (gcd_time_budget (4 * n) m p ltac:(lia)) as Hgcdtime1.
    pose proof (gcd_time_budget (8 * n) (Z.gcd m p) (r - s) ltac:(lia)) as Hgcdtime2.
    pose proof (normalization_time_budget w (C (Z.gcd (Z.gcd m p) (r - s)) r)
      (11 * n) ltac:(cbn [congr_bits]; lia)) as Hnormalize.
    rewrite !Nat.pow_mul_l, !Nat2N.inj_mul in *. cost_constants. lia.
  Qed.

  (** The CRT coefficient-chain bound and bounded normalization compose quadratically. *)
  Lemma meet_time_budget : forall w a b n,
    (Pos.to_nat w + congr_bits a + congr_bits b + 1 <= n)%nat ->
    (T_pmeet w a b <= 4194304 * N.of_nat (n ^ 2))%N.
  Proof.
    intros w a b n Hinput.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Hnorma.
    pose proof (normalization_time_budget w b n ltac:(lia)) as Hnormb.
    assert (Hpositive : (1 <= n)%nat) by lia.
    pose proof (linear_le_square n Hpositive) as Hlinear.
    assert (Hone : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
    time_unfold T_pmeet.
    destruct (congr_norm w a) as [|m r] eqn:Haform;
      destruct (congr_norm w b) as [|p s] eqn:Hbform; cbn beta iota zeta; try lia.
    pose proof (normalized_bits w a) as Ha. rewrite Haform in Ha.
    pose proof (normalized_bits w b) as Hb. rewrite Hbform in Hb.
    cbn [congr_bits] in Ha, Hb.
    pose proof (integer_gcd_size m p) as Hgcdbits.
    pose proof (integer_modulo_size r (Z.gcd m p)) as Hrembits.
    pose proof (integer_lcm_size m p) as Hlcmbits.
    destruct (combinecong_budget (4 * n) m p r s ltac:(lia)) as [Hcrtbits Hcrttime].
    pose proof (gcd_time_budget (4 * n) m p ltac:(lia)) as Hgcd.
    pose proof (mod_time_budget (6 * n) r (Z.gcd m p) ltac:(lia)) as Hrem1.
    pose proof (mod_time_budget (6 * n) s (Z.gcd m p) ltac:(lia)) as Hrem2.
    pose proof (eqb_time_budget (7 * n) (r mod Z.gcd m p) (s mod Z.gcd m p)
      ltac:(lia)) as Hcompatible.
    pose proof (lcm_time_budget (4 * n) m p ltac:(lia)) as Hlcm.
    pose proof (normalization_time_budget w
      (C (Z.lcm m p) (CongruenceCRT.combinecong m p r s))
      (65 * n) ltac:(cbn [congr_bits]; lia)) as Hnormalize.
    rewrite !Nat.pow_mul_l, !Nat2N.inj_mul in *. cost_constants.
    destruct (r mod Z.gcd m p =? s mod Z.gcd m p); lia.
  Qed.

  (** Two separately squared payload sizes dominate the common binary-operation budget. *)
  Lemma combined_payload_square : forall w a b,
    ((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2 <=
      4 * (psize w a + psize w b + 1))%nat.
  Proof.
    intros w a b. unfold psize.
    destruct (Nat.le_ge_cases (congr_bits a) (congr_bits b)) as [Hle|Hge].
    - eapply Nat.le_trans with (m := ((2 * (Pos.to_nat w + congr_bits b + 1)) ^ 2)%nat).
      + apply Nat.pow_le_mono_l. lia.
      + rewrite Nat.pow_mul_l. change ((2 ^ 2)%nat) with 4%nat. lia.
    - eapply Nat.le_trans with (m := ((2 * (Pos.to_nat w + congr_bits a + 1)) ^ 2)%nat).
      + apply Nat.pow_le_mono_l. lia.
      + rewrite Nat.pow_mul_l. change ((2 ^ 2)%nat) with 4%nat. lia.
  Qed.

  (** Joined payloads fit within the combined operand sizes. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (bounded_payload_size w (pjoin w a b) (join_bits w a b)).
    assert (Hsize : (psize w (pjoin w a b) <= 9 * (psize w a + psize w b + 1))%nat).
    { pose proof (payload_width_size w a). lia. }
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize.
    unfold c_payload. change (N.of_nat 9) with 9%N in Hsize. nia.
  Qed.
  (** Met payloads fit within the combined operand sizes. *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b. pose proof (bounded_payload_size w (pmeet w a b) (meet_bits w a b)).
    assert (Hsize : (psize w (pmeet w a b) <= 9 * (psize w a + psize w b + 1))%nat).
    { pose proof (payload_width_size w a). lia. }
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize.
    unfold c_payload. change (N.of_nat 9) with 9%N in Hsize. nia.
  Qed.
  (** Widened payloads fit within the operand and parameter sizes. *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b. rewrite pwiden_eq. unfold pwiden_ref, pwsize.
    destruct (pleb w b a).
    - unfold c_payload. rewrite !Nat2N.inj_add. nia.
    - pose proof (pjoin_size w a b). rewrite Nat.add_0_r. exact H.
  Qed.
  (** Narrowed payloads fit within the combined operand sizes. *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    apply pmeet_size.
  Qed.
  (** Payload widening charges both operands and its parameters. *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof.
    intros q w a b.
    pose proof (inclusion_time_budget w b a
      (Pos.to_nat w + congr_bits a + congr_bits b + 1) ltac:(lia)) as Hinclusion.
    pose proof (join_time_budget w a b
      (Pos.to_nat w + congr_bits a + congr_bits b + 1) ltac:(lia)) as Hjoin.
    pose proof (combined_payload_square w a b) as Hsize.
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize. cost_constants.
    assert (Hpositive : (1 <= N.of_nat (psize w a + psize w b + 1))%N).
    { change (N.of_nat 1 <= N.of_nat (psize w a + psize w b + 1))%N.
      apply time_of_nat_le. lia. }
    unfold pwsize, c_payload. rewrite Nat.add_0_r.
    unfold T_pleb in Hinclusion. unfold T_pjoin in Hjoin.
    time_unfold T_pwiden. unfold T_join_norm. cbn beta iota zeta in *.
    destruct (raw_leb (congr_norm w b) (congr_norm w a));
      destruct (congr_norm w a), (congr_norm w b); cbn beta iota zeta in *; lia.
  Qed.
  (** Payload narrowing charges both payload sizes. *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof.
    intros w a b.
    pose proof (meet_time_budget w a b
      (Pos.to_nat w + congr_bits a + congr_bits b + 1) ltac:(lia)) as Hmeet.
    pose proof (combined_payload_square w a b) as Hsize.
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize. cost_constants.
    assert (Hpositive : (1 <= N.of_nat (psize w a + psize w b + 1))%N).
    { change (N.of_nat 1 <= N.of_nat (psize w a + psize w b + 1))%N.
      apply time_of_nat_le. lia. }
    time_unfold T_pnarrow. unfold c_payload. lia.
  Qed.
  (** Payload inclusion charges the two payload sizes. *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof.
    intros w a b.
    pose proof (inclusion_time_budget w a b
      (Pos.to_nat w + congr_bits a + congr_bits b + 1) ltac:(lia)) as Htime.
    pose proof (combined_payload_square w a b) as Hsize.
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize. cost_constants.
    unfold c_payload. lia.
  Qed.
  (** Payload join charges the two payload sizes. *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof.
    intros w a b.
    pose proof (join_time_budget w a b
      (Pos.to_nat w + congr_bits a + congr_bits b + 1) ltac:(lia)) as Htime.
    pose proof (combined_payload_square w a b) as Hsize.
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize. cost_constants.
    unfold c_payload. lia.
  Qed.
  (** Payload meet charges the two payload sizes. *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof.
    intros w a b.
    pose proof (meet_time_budget w a b
      (Pos.to_nat w + congr_bits a + congr_bits b + 1) ltac:(lia)) as Htime.
    pose proof (combined_payload_square w a b) as Hsize.
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize. cost_constants.
    unfold c_payload. lia.
  Qed.
  (** Bottom recognition charges the payload size. *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat ((psize w a + 1)%nat))%N.
  Proof.
    intros w a.
    pose proof (normalization_time_budget w a
      (Pos.to_nat w + congr_bits a + 1) ltac:(lia)) as Hnorm.
    time_unfold T_pis_bot. unfold psize, c_payload. rewrite Nat2N.inj_add.
    change (N.of_nat 1) with 1%N. destruct (congr_norm w a); lia.
  Qed.
  (** Point recognition charges the payload size. *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat ((psize w a + 1)%nat))%N.
  Proof.
    intros w a.
    pose proof (normalization_time_budget w a
      (Pos.to_nat w + congr_bits a + 1) ltac:(lia)) as Hnorm.
    time_unfold T_ppoint. unfold psize, c_payload. rewrite Nat2N.inj_add.
    change (N.of_nat 1) with 1%N. destruct (congr_norm w a); [lia|].
    destruct m; lia.
  Qed.
  (** Constant abstraction charges the width and literal bit size. *)
  Lemma T_pconst_le : forall w z, (T_pconst w z <=
    c_payload * N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat))%N.
  Proof.
    intros w z. pose proof (WordTime.word_wrap_time_bound w z).
    time_unfold T_pconst. unfold c_payload.
    rewrite !Nat2N.inj_pow, !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.
  (** Payload size uses the tagged width. *)
  Lemma psize_congr : forall w a, psize w a = ((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat.
  Proof.
    reflexivity.
  Qed.
  (** Normalized payloads fit two words of the width. *)
  Lemma congr_norm_bits : forall w a,
    (congr_bits (congr_norm w a) <= 2 * Pos.to_nat w)%nat.
  Proof.
    apply normalized_bits.
  Qed.
  (** Negation results fit two words of the width. *)
  Lemma congr_neg_bits : forall w a,
    (congr_bits (congr_neg w a) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a. unfold congr_neg. destruct (congr_norm w a).
    - cbn [congr_bits]. lia.
    - rewrite wrap_class_eq. apply normalized_bits.
  Qed.
  (** Binary transfer results fit two words of the width. *)
  Lemma congr_binary_bits : forall w a b,
    (congr_bits (congr_add w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_sub w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_mul w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_shl w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_urem w a b) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros w a b.
    pose proof (Pos2Nat.is_pos w) as Hwidth.
    rewrite congr_add_eq, congr_sub_eq, congr_shl_eq.
    unfold congr_add_ref, congr_sub_ref, congr_mul, congr_shl_ref, congr_urem.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s];
      cbn [congr_bits]; try (repeat split; lia).
    repeat split; try rewrite wrap_class_eq; try apply normalized_bits.
    - destruct n; try (cbn [congr_bits Z.size_nat Pos.size_nat]; lia).
      destruct (Zpos w <=? s); [cbn [congr_bits Z.size_nat]; lia |].
      apply normalized_bits.
    - destruct n; [apply normalized_bits| |]; cbn [congr_bits Z.size_nat Pos.size_nat]; lia.
  Qed.
  (** Projection results fit two words of the target width. *)
  Lemma congr_project_bits : forall source target a,
    (congr_bits (congr_project source target a) <= 2 * Pos.to_nat target)%nat.
  Proof.
    intros source target a. unfold congr_project. destruct (congr_norm source a).
    - cbn [congr_bits]. lia.
    - rewrite wrap_class_eq. apply normalized_bits.
  Qed.
  (** Negation adds linear work after its input normalization. *)
  Lemma congr_neg_time_tail : forall w a,
    (T_congr_neg w a <= T_congr_norm w a + 4096 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    intros w a. time_unfold T_congr_neg.
    destruct (congr_norm w a) as [| m r] eqn:Hform; cbn beta iota zeta.
    - rewrite Nat2N.inj_add. cbn [N.of_nat]. lia.
    - pose proof (normalized_bits w a) as Hbits. rewrite Hform in Hbits.
      cbn [congr_bits] in Hbits.
      pose proof (Z.T_opp_le r) as Hopp.
      pose proof (wrap_class_time_linear w m (-r) (3 * (Pos.to_nat w + 1))
        ltac:(rewrite WordTime.integer_opp_size; lia)) as Hwrap.
      rewrite Nat2N.inj_mul in Hwrap. change (N.of_nat 3) with 3%N in Hwrap.
      lia.
  Qed.

  (** Addition adds linear work after normalizing the two operands. *)
  Lemma congr_add_time_tail : forall w a b,
    (T_congr_add w a b <= T_congr_norm w a + T_congr_norm w b +
      4096 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    intros w a b. time_unfold T_congr_add.
    destruct (congr_norm w a) as [| m r] eqn:Haform;
      destruct (congr_norm w b) as [| p s] eqn:Hbform; cbn beta iota zeta;
      try (rewrite Nat2N.inj_add; cbn [N.of_nat]; lia).
    pose proof (normalized_bits w a) as Ha. rewrite Haform in Ha.
    pose proof (normalized_bits w b) as Hb. rewrite Hbform in Hb.
    cbn [congr_bits] in Ha, Hb.
    pose proof (WordTime.integer_add_size r s) as Hsum.
    pose proof (masked_pair_time_budget w m p (r + s) (6 * (Pos.to_nat w + 1))
      ltac:(lia)) as Hmask.
    pose proof (add_time_budget (4 * (Pos.to_nat w + 1)) r s ltac:(lia)) as Hadd.
    rewrite !Nat2N.inj_mul in Hmask, Hadd.
    change (N.of_nat 6) with 6%N in Hmask.
    change (N.of_nat 4) with 4%N in Hadd. lia.
  Qed.

  (** Subtraction adds linear work after normalizing the two operands. *)
  Lemma congr_sub_time_tail : forall w a b,
    (T_congr_sub w a b <= T_congr_norm w a + T_congr_norm w b +
      4096 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    intros w a b. time_unfold T_congr_sub.
    destruct (congr_norm w a) as [| m r] eqn:Haform;
      destruct (congr_norm w b) as [| p s] eqn:Hbform; cbn beta iota zeta;
      try (rewrite Nat2N.inj_add; cbn [N.of_nat]; lia).
    pose proof (normalized_bits w a) as Ha. rewrite Haform in Ha.
    pose proof (normalized_bits w b) as Hb. rewrite Hbform in Hb.
    cbn [congr_bits] in Ha, Hb.
    pose proof (WordTime.integer_sub_size r s) as Hdifference.
    pose proof (masked_pair_time_budget w m p (r - s) (6 * (Pos.to_nat w + 1))
      ltac:(lia)) as Hmask.
    pose proof (sub_time_budget (4 * (Pos.to_nat w + 1)) r s ltac:(lia)) as Hsubtract.
    rewrite !Nat2N.inj_mul in Hmask, Hsubtract.
    change (N.of_nat 6) with 6%N in Hmask.
    change (N.of_nat 4) with 4%N in Hsubtract. lia.
  Qed.

  (** Shifting adds linear work after normalizing the operands. *)
  Lemma congr_shl_time_tail : forall w a b,
    (T_congr_shl w a b <= T_congr_norm w a + T_congr_norm w b +
      4096 * N.of_nat (Pos.to_nat w + 1))%N.
  Proof.
    intros w a b. time_unfold T_congr_shl.
    destruct (congr_norm w a) as [| m r] eqn:Haform;
      destruct (congr_norm w b) as [| p s] eqn:Hbform; cbn beta iota zeta;
      try (rewrite Nat2N.inj_add; cbn [N.of_nat]; lia).
    destruct p; cbn beta iota zeta;
      try (rewrite Nat2N.inj_add; cbn [N.of_nat]; lia).
    pose proof (Z.T_leb_le (Zpos w) s) as Hcompare.
    assert (Hwidthbits :
      (N.of_nat (Z.size_nat (Zpos w)) <= N.of_nat (Pos.to_nat w + 1))%N).
    { apply time_of_nat_le. change (Z.size_nat (Zpos w)) with (Pos.size_nat w).
      pose proof (WordTime.positive_size_value w). lia. }
    destruct (Zpos w <=? s) eqn:Hlarge.
    - rewrite Nat2N.inj_add in *. cbn [N.of_nat] in *. lia.
    - apply Z.leb_gt in Hlarge.
      pose proof (cong_norm_canonical w b) as Hcanonical. rewrite Hbform in Hcanonical.
      destruct Hcanonical as [[Hzero Hword] | [Hm Hr]]; [| lia].
      destruct Hword as [Hs Hbound].
      pose proof (normalized_bits w a) as Habits. rewrite Haform in Habits.
      cbn [congr_bits] in Habits.
      assert (Hpowerword : is_word w (2 ^ s)).
      { unfold is_word, modulus. split.
        - apply Z.pow_nonneg. lia.
        - apply Z.pow_lt_mono_r; lia. }
      pose proof (WordTime.word_size_bound w (2 ^ s) Hpowerword) as Hpowerbits.
      pose proof (WordTime.integer_mul_size m (2 ^ s)) as Hmbits.
      pose proof (WordTime.integer_mul_size r (2 ^ s)) as Hrbits.
      rewrite <- Z.shiftl_mul_pow2 in Hmbits, Hrbits by exact Hs.
      pose proof (congruence_shiftl_time m s Hs) as Hshiftm.
      pose proof (congruence_shiftl_time r s Hs) as Hshiftr.
      pose proof (wrap_class_time_linear w (Z.shiftl m s) (Z.shiftl r s)
        (5 * (Pos.to_nat w + 1)) ltac:(lia)) as Hwrap.
      assert (Hcount : (Z.to_nat s + 1 <= Pos.to_nat w + 1)%nat).
      { apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add, Z2Nat.id by exact Hs.
        rewrite positive_nat_Z. lia. }
      apply time_of_nat_le in Hcount.
      rewrite Nat2N.inj_mul in Hwrap. change (N.of_nat 5) with 5%N in Hwrap. lia.
  Qed.

  (** Projection adds work linear in the source and target widths. *)
  Lemma congr_project_time_tail : forall source target a,
    (T_congr_project source target a <= T_congr_norm source a +
      4096 * N.of_nat (Pos.to_nat source + Pos.to_nat target + 1))%N.
  Proof.
    intros source target a. time_unfold T_congr_project.
    destruct (congr_norm source a) as [| m r] eqn:Hform; cbn beta iota zeta.
    - rewrite !Nat2N.inj_add. cbn [N.of_nat]. lia.
    - pose proof (normalized_bits source a) as Hbits. rewrite Hform in Hbits.
      cbn [congr_bits] in Hbits.
      pose proof (wrap_class_time_linear target m r
        (2 * (Pos.to_nat source + Pos.to_nat target + 1)) ltac:(lia)) as Hwrap.
      rewrite Nat2N.inj_mul in Hwrap. change (N.of_nat 2) with 2%N in Hwrap. lia.
  Qed.

  (** Normalization has the published quadratic arithmetic bound. *)
  Lemma T_congr_norm_le : forall w a,
    (T_congr_norm w a <= c_congruence * N.of_nat (((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat))%N.
  Proof.
    intros w a.
    pose proof (normalization_time_budget w a (Pos.to_nat w + congr_bits a + 1)
      ltac:(lia)) as Hnorm.
    unfold c_congruence. lia.
  Qed.
  (** Negation has the published quadratic arithmetic bound. *)
  Lemma T_congr_neg_le : forall w a,
    (T_congr_neg w a <= c_congruence * N.of_nat (((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat))%N.
  Proof.
    intros w a. remember (Pos.to_nat w + congr_bits a + 1)%nat as n eqn:Hn.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Hnormalize.
    assert (Hpositive : (1 <= n)%nat) by lia.
    pose proof (linear_le_square n Hpositive) as Hlinear.
    assert (Hone : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
    unfold c_congruence. time_unfold T_congr_neg.
    destruct (congr_norm w a) as [|m r] eqn:Hform; cbn beta iota zeta; [lia|].
    pose proof (normalized_bits w a) as Hbits. rewrite Hform in Hbits.
    cbn [congr_bits] in Hbits.
    pose proof (Z.T_opp_le r) as Hopp.
    pose proof (wrap_class_time_budget w m (-r) (3 * n)
      ltac:(rewrite WordTime.integer_opp_size; lia)) as Hwrap.
    rewrite Nat.pow_mul_l, Nat2N.inj_mul in Hwrap. cost_constants. lia.
  Qed.
  (** Addition has the published quadratic arithmetic bound. *)
  Lemma T_congr_add_le : forall w a b,
    (T_congr_add w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof.
    intros w a b.
    remember (Pos.to_nat w + congr_bits a + congr_bits b + 1)%nat as n eqn:Hn.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Ha.
    pose proof (normalization_time_budget w b n ltac:(lia)) as Hb.
    pose proof (congr_add_time_tail w a b) as Htail.
    pose proof (linear_le_square n ltac:(lia)) as Hlinear.
    assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= N.of_nat n)%N).
    { apply time_of_nat_le. lia. }
    unfold c_congruence. lia.
  Qed.
  (** Subtraction has the published quadratic arithmetic bound. *)
  Lemma T_congr_sub_le : forall w a b,
    (T_congr_sub w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof.
    intros w a b.
    remember (Pos.to_nat w + congr_bits a + congr_bits b + 1)%nat as n eqn:Hn.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Ha.
    pose proof (normalization_time_budget w b n ltac:(lia)) as Hb.
    pose proof (congr_sub_time_tail w a b) as Htail.
    pose proof (linear_le_square n ltac:(lia)) as Hlinear.
    assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= N.of_nat n)%N).
    { apply time_of_nat_le. lia. }
    unfold c_congruence. lia.
  Qed.
  (** Multiplication has the published quadratic arithmetic bound. *)
  Lemma T_congr_mul_le : forall w a b,
    (T_congr_mul w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof.
    intros w a b.
    remember (Pos.to_nat w + congr_bits a + congr_bits b + 1)%nat as n eqn:Hn.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Hnorma.
    pose proof (normalization_time_budget w b n ltac:(lia)) as Hnormb.
    assert (Hpositive : (1 <= n)%nat) by lia.
    pose proof (linear_le_square n Hpositive) as Hlinear.
    assert (Hone : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
    unfold c_congruence. time_unfold T_congr_mul.
    destruct (congr_norm w a) as [|m r] eqn:Haform;
      destruct (congr_norm w b) as [|p s] eqn:Hbform; cbn beta iota zeta; try lia.
    pose proof (normalized_bits w a) as Ha. rewrite Haform in Ha.
    pose proof (normalized_bits w b) as Hb. rewrite Hbform in Hb.
    cbn [congr_bits] in Ha, Hb.
    pose proof (WordTime.integer_mul_size m p) as Hmp.
    pose proof (WordTime.integer_mul_size m s) as Hms.
    pose proof (WordTime.integer_mul_size p r) as Hpr.
    pose proof (WordTime.integer_mul_size r s) as Hrs.
    pose proof (integer_gcd_size (m * s) (p * r)) as Hgcdinner.
    pose proof (integer_gcd_size (m * p) (Z.gcd (m * s) (p * r))) as Hgcdouter.
    pose proof (mul_time_budget (4 * n) m p ltac:(lia)) as T_mp.
    pose proof (mul_time_budget (4 * n) m s ltac:(lia)) as T_ms.
    pose proof (mul_time_budget (4 * n) p r ltac:(lia)) as T_pr.
    pose proof (mul_time_budget (4 * n) r s ltac:(lia)) as T_rs.
    pose proof (gcd_time_budget (4 * n) (m * s) (p * r) ltac:(lia)) as Tgcdinner.
    pose proof (gcd_time_budget (8 * n) (m * p) (Z.gcd (m * s) (p * r))
      ltac:(lia)) as Tgcdouter.
    pose proof (wrap_class_time_budget w (Z.gcd (m * p) (Z.gcd (m * s) (p * r)))
      (r * s) (9 * n) ltac:(lia)) as Hwrap.
    rewrite !Nat.pow_mul_l, !Nat2N.inj_mul in *. cost_constants. lia.
  Qed.
  (** Shift transfer has the published quadratic arithmetic bound. *)
  Lemma T_congr_shl_le : forall w a b,
    (T_congr_shl w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof.
    intros w a b.
    remember (Pos.to_nat w + congr_bits a + congr_bits b + 1)%nat as n eqn:Hn.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Ha.
    pose proof (normalization_time_budget w b n ltac:(lia)) as Hb.
    pose proof (congr_shl_time_tail w a b) as Htail.
    pose proof (linear_le_square n ltac:(lia)) as Hlinear.
    assert (Hwidth : (N.of_nat (Pos.to_nat w + 1) <= N.of_nat n)%N).
    { apply time_of_nat_le. lia. }
    unfold c_congruence. lia.
  Qed.
  (** Remainder transfer has the published quadratic arithmetic bound. *)
  Lemma T_congr_urem_le : forall w a b,
    (T_congr_urem w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof.
    intros w a b.
    remember (Pos.to_nat w + congr_bits a + congr_bits b + 1)%nat as n eqn:Hn.
    pose proof (normalization_time_budget w a n ltac:(lia)) as Hnorma.
    pose proof (normalization_time_budget w b n ltac:(lia)) as Hnormb.
    assert (Hpositive : (1 <= n)%nat) by lia.
    pose proof (linear_le_square n Hpositive) as Hlinear.
    assert (Hone : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
    unfold c_congruence. time_unfold T_congr_urem.
    destruct (congr_norm w a) as [|m r] eqn:Haform;
      destruct (congr_norm w b) as [|p s] eqn:Hbform; cbn beta iota zeta; try lia.
    destruct p; cbn beta iota zeta; try lia.
    pose proof (normalized_bits w a) as Ha. rewrite Haform in Ha.
    pose proof (normalized_bits w b) as Hb. rewrite Hbform in Hb.
    cbn [congr_bits Z.size_nat] in Ha, Hb.
    pose proof (integer_gcd_size m s) as Hgcdbits.
    pose proof (gcd_time_budget (4 * n) m s ltac:(lia)) as Hgcd.
    pose proof (normalization_time_budget w (C (Z.gcd m s) r) (5 * n)
      ltac:(cbn [congr_bits]; lia)) as Hnormalize.
    rewrite !Nat.pow_mul_l, !Nat2N.inj_mul in *. cost_constants. lia.
  Qed.
  (** Projection charges both source and target widths. *)
  Lemma T_congr_project_le : forall source target a,
    (T_congr_project source target a <=
    c_congruence * N.of_nat
      (((Pos.to_nat source + Pos.to_nat target + congr_bits a + 1) ^ 2)%nat))%N.
  Proof.
    intros source target a.
    remember (Pos.to_nat source + Pos.to_nat target + congr_bits a + 1)%nat as n eqn:Hn.
    pose proof (normalization_time_budget source a n ltac:(lia)) as Hnormalize.
    assert (Hpositive : (1 <= n)%nat) by lia.
    pose proof (linear_le_square n Hpositive) as Hlinear.
    assert (Hone : (1 <= N.of_nat n)%N).
    { change (N.of_nat 1 <= N.of_nat n)%N. now apply time_of_nat_le. }
    unfold c_congruence. time_unfold T_congr_project.
    destruct (congr_norm source a) as [|m r] eqn:Hform; cbn beta iota zeta; [lia|].
    pose proof (normalized_bits source a) as Hbits. rewrite Hform in Hbits.
    cbn [congr_bits] in Hbits.
    pose proof (wrap_class_time_budget target m r (2 * n) ltac:(lia)) as Hwrap.
    rewrite Nat.pow_mul_l, Nat2N.inj_mul in Hwrap. cost_constants. lia.
  Qed.
  (** Congruence multiplication has the published quadratic width bound. *)
  Lemma mul_complexity : (bigO (fun _ => True)
    (fun x : positive * (congr * congr) => N.of_nat
      (((Pos.to_nat (fst x) + congr_bits (fst (snd x)) + congr_bits (snd (snd x)) + 1) ^ 2)%nat))
    (fun x => T_congr_mul (fst x) (fst (snd x)) (snd (snd x))))%N.
  Proof.
    exists c_congruence. intros [w [a b]] _. cbn [fst snd].
    pose proof (T_congr_mul_le w a b). nia.
  Qed.
  (** Remainder has the published quadratic class, because it takes a gcd. *)
  Lemma congr_urem_complexity : bigO (X := positive * (congr * congr)) (fun _ => True)
    (fun x => N.of_nat
      (((Pos.to_nat (fst x) + congr_bits (fst (snd x)) + congr_bits (snd (snd x)) + 1) ^ 2)%nat))
    (fun x => T_congr_urem (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists c_congruence. intros [w [a b]] _. cbn [fst snd].
    pose proof (T_congr_urem_le w a b). nia.
  Qed.
  (** Canonical payloads normalize in linear time. *)
  Lemma congr_norm_lin_complexity : bigO (X := positive * congr)
    (fun x => canonical (fst x) (snd x))
    (fun x => N.of_nat (Pos.to_nat (fst x) + congr_bits (snd x) + 1))
    (fun x => T_congr_norm (fst x) (snd x)).
  Proof.
    exists 128%N. intros [w a] Hcanonical. cbn [fst snd] in *.
    pose proof (normalization_time_linear w a Hcanonical). nia.
  Qed.
  (** Negation of a canonical payload is linear. *)
  Lemma congr_neg_lin_complexity : bigO (X := positive * congr)
    (fun x => canonical (fst x) (snd x))
    (fun x => N.of_nat (Pos.to_nat (fst x) + congr_bits (snd x) + 1))
    (fun x => T_congr_neg (fst x) (snd x)).
  Proof.
    exists 8192%N. intros [w a] Ha. cbn [fst snd] in *.
    pose proof (normalization_time_linear w a Ha) as Hnorm.
    pose proof (congr_neg_time_tail w a) as Htail.
    rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.
  (** Addition of canonical payloads is linear. *)
  Lemma congr_add_lin_complexity : bigO (X := positive * (congr * congr))
    (fun x => canonical (fst x) (fst (snd x)) /\ canonical (fst x) (snd (snd x)))
    (fun x => N.of_nat
      (Pos.to_nat (fst x) + congr_bits (fst (snd x)) + congr_bits (snd (snd x)) + 1))
    (fun x => T_congr_add (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists 8192%N. intros [w [a b]] [Ha Hb]. cbn [fst snd] in *.
    pose proof (normalization_time_linear w a Ha) as Hnorma.
    pose proof (normalization_time_linear w b Hb) as Hnormb.
    pose proof (congr_add_time_tail w a b) as Htail.
    rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.
  (** Subtraction of canonical payloads is linear. *)
  Lemma congr_sub_lin_complexity : bigO (X := positive * (congr * congr))
    (fun x => canonical (fst x) (fst (snd x)) /\ canonical (fst x) (snd (snd x)))
    (fun x => N.of_nat
      (Pos.to_nat (fst x) + congr_bits (fst (snd x)) + congr_bits (snd (snd x)) + 1))
    (fun x => T_congr_sub (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists 8192%N. intros [w [a b]] [Ha Hb]. cbn [fst snd] in *.
    pose proof (normalization_time_linear w a Ha) as Hnorma.
    pose proof (normalization_time_linear w b Hb) as Hnormb.
    pose proof (congr_sub_time_tail w a b) as Htail.
    rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.
  (** Shifting a canonical payload by a canonical amount is linear. *)
  Lemma congr_shl_lin_complexity : bigO (X := positive * (congr * congr))
    (fun x => canonical (fst x) (fst (snd x)) /\ canonical (fst x) (snd (snd x)))
    (fun x => N.of_nat
      (Pos.to_nat (fst x) + congr_bits (fst (snd x)) + congr_bits (snd (snd x)) + 1))
    (fun x => T_congr_shl (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists 8192%N. intros [w [a b]] [Ha Hb]. cbn [fst snd] in *.
    pose proof (normalization_time_linear w a Ha) as Hnorma.
    pose proof (normalization_time_linear w b Hb) as Hnormb.
    pose proof (congr_shl_time_tail w a b) as Htail.
    rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.
  (** Projection of a canonical payload is linear in both widths. *)
  Lemma congr_project_lin_complexity : bigO (X := positive * (positive * congr))
    (fun x => (fst (snd x) <= fst x)%positive /\ canonical (fst x) (snd (snd x)))
    (fun x => N.of_nat
      (Pos.to_nat (fst x) + Pos.to_nat (fst (snd x)) + congr_bits (snd (snd x)) + 1))
    (fun x => T_congr_project (fst x) (fst (snd x)) (snd (snd x))).
  Proof.
    exists 8192%N. intros [source [target a]] [Hwidth Ha]. cbn [fst snd] in *.
    pose proof (normalization_time_linear source a Ha) as Hnorm.
    pose proof (congr_project_time_tail source target a) as Htail.
    rewrite !Nat2N.inj_add in *. time_cbn_all. lia.
  Qed.
  (** Normalization produces a canonical representation. *)
  Lemma norm_canonical : forall w a, canonical w (congr_norm w a).
  Proof.
    intros w a. pose proof (cong_norm_canonical w a) as Hcanonical.
    destruct (congr_norm w a) as [| m r]; [exact I |].
    destruct Hcanonical as [[Hm Hr] | [Hm Hr]].
    - left. split; assumption.
    - right. split; [lia | exact Hr].
  Qed.
  (** Normalization is idempotent. *)
  Lemma norm_idempotent : forall w a,
    congr_norm w (congr_norm w a) = congr_norm w a.
  Proof.
    apply cong_norm_idempotent.
  Qed.
  (** Chinese remainder meet retains each shared integer. *)
  Lemma crt_meet_sound : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof.
    apply pgamma_meet.
  Qed.
  (** The requested congruence rank is bounded by width plus two. *)
  Lemma congr_wrank_le : forall w a, (congr_wrank w a <= Pos.to_nat w + 2)%nat.
  Proof.
    intros w a. change (raw_wrank w (congr_norm w a) <= Pos.to_nat w + 2)%nat.
    apply raw_wrank_bound. apply cong_norm_canonical.
  Qed.
  (** Payload widening uses the normalized congruence rank. *)
  Lemma pwrank_def : forall q w a, pwrank q w a = congr_wrank w a.
  Proof.
    intros q w a. reflexivity.
  Qed.
  (** Gcd-based joining has the published quadratic arithmetic bound. *)
  Lemma T_pjoin_plan_le : forall w a b,
    (T_pjoin w a b <= k_congr_gcd *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof.
    intros w a b.
    pose proof (join_time_budget w a b
      (Pos.to_nat w + congr_bits a + congr_bits b + 1) ltac:(lia)) as Htime.
    unfold k_congr_gcd. lia.
  Qed.
  (** Chinese remainder meet has the published quadratic arithmetic bound. *)
  Lemma T_pmeet_plan_le : forall w a b,
    (T_pmeet w a b <= k_congr_crt *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof.
    intros w a b.
    pose proof (meet_time_budget w a b
      (Pos.to_nat w + congr_bits a + congr_bits b + 1) ltac:(lia)) as Htime.
    unfold k_congr_crt. lia.
  Qed.

  (** The result stays within its declared work budget. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. time_unfold T_ptop. unfold c_payload.
    rewrite Nat2N.inj_pow, Nat2N.inj_add. time_cbn_all. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. time_unfold T_pbot. unfold c_payload.
    rewrite Nat2N.inj_pow, Nat2N.inj_add. time_cbn_all. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w.
    assert (Hsize : (psize w (ptop w) <= 4 * (Pos.to_nat w + 1) ^ 2)%nat).
    { unfold psize. cbn [ptop congr_bits Z.size_nat Pos.size_nat].
      replace (4 * (Pos.to_nat w + 1) ^ 2)%nat with
        ((2 * (Pos.to_nat w + 1)) ^ 2)%nat by (rewrite Nat.pow_mul_l; reflexivity).
      apply Nat.pow_le_mono_l. lia. }
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize.
    unfold c_payload. change (N.of_nat 4) with 4%N in Hsize. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof.
    intro w. unfold psize, pbot, congr_bits, c_payload.
    rewrite Nat.add_0_r. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof.
    intros w z. pose proof (WordTime.word_wrap_size_bound w z).
    assert (Hsize : (psize w (pconst w z) <=
      4 * (Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat).
    { unfold psize. cbn [pconst congr_bits Z.size_nat].
      replace (4 * (Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat with
        ((2 * (Pos.to_nat w + Z.size_nat z + 1)) ^ 2)%nat
        by (rewrite Nat.pow_mul_l; reflexivity).
      apply Nat.pow_le_mono_l. lia. }
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize.
    unfold c_payload. change (N.of_nat 4) with 4%N in Hsize. nia.
  Qed.
End CongruenceT.

Module CongruenceTableT (L : WORD_LANGUAGE_T) (D : CONGRUENCE_T L)
    <: CONGRUENCE_TABLE_T L D.
  Include CongruenceTable L D.
  TimeFun wfwd.
  TimeFun wbwd.
  Definition c_word_table : N := (4096 * (D.c_congruence + D.c_payload + 1))%N.

  (** The table budget includes all declared widths and every raw payload size. *)
  Definition table_budget rw (xs : list (positive * D.p)) : nat :=
    ((Pos.to_nat rw +
      fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
    fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat.

  (** Every table budget pays for the constant dispatch cost. *)
  Lemma table_budget_positive : forall rw xs, (1 <= table_budget rw xs)%nat.
  Proof.
    intros rw xs. unfold table_budget.
    remember (Pos.to_nat rw +
      fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1)%nat as n eqn:Hn.
    assert (Hsquare : (1 <= n ^ 2)%nat).
    { change ((1 ^ 2) <= n ^ 2)%nat. apply Nat.pow_le_mono_l. lia. }
    lia.
  Qed.
  (** Each member contributes at most the sum of nonnegative member costs. *)
  Lemma member_sum_bound {A : Type} (f : A -> nat) : forall xs x,
    In x xs -> (f x <= fold_right Nat.add 0%nat (map f xs))%nat.
  Proof.
    induction xs as [|head xs IH]; intros x Hmember; cbn [In] in Hmember.
    - contradiction.
    - destruct Hmember as [->|Htail]; cbn [map fold_right].
      + lia.
      + pose proof (IH x Htail). lia.
  Qed.

  (** Squaring a positive natural number does not decrease it. *)
  Lemma natural_le_square : forall n, (1 <= n -> n <= n ^ 2)%nat.
  Proof.
    intros n Hpositive. cbn [Nat.pow]. nia.
  Qed.

  (** A squared two-term sum is bounded by a constant times the component squares. *)
  Lemma sum_square_bound : forall x y k,
    (k <= x + y -> k ^ 2 <= 4 * (x ^ 2 + y ^ 2))%nat.
  Proof.
    intros x y k Hsum. destruct (Nat.le_ge_cases x y) as [Hle|Hge].
    - eapply Nat.le_trans with (m := ((2 * y) ^ 2)%nat).
      + apply Nat.pow_le_mono_l. lia.
      + rewrite Nat.pow_mul_l. change ((2 ^ 2)%nat) with 4%nat. lia.
    - eapply Nat.le_trans with (m := ((2 * x) ^ 2)%nat).
      + apply Nat.pow_le_mono_l. lia.
      + rewrite Nat.pow_mul_l. change ((2 ^ 2)%nat) with 4%nat. lia.
  Qed.

  (** A squared three-term sum is bounded by a constant times the component squares. *)
  Lemma triple_square_bound : forall x y z k,
    (k <= x + y + z -> k ^ 2 <= 16 * (x ^ 2 + y ^ 2 + z ^ 2))%nat.
  Proof.
    intros x y z k Hsum.
    pose proof (sum_square_bound x (y + z) k ltac:(lia)) as Houter.
    pose proof (sum_square_bound y z (y + z) ltac:(lia)) as Hinner. lia.
  Qed.

  (** The table budget contains the full linear width charge. *)
  Lemma table_budget_width : forall rw xs,
    (Pos.to_nat rw +
      fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) + 1 <=
      table_budget rw xs)%nat.
  Proof.
    intros rw xs. unfold table_budget.
    pose proof (natural_le_square
      (Pos.to_nat rw +
        fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) + 1)
      ltac:(lia)) as Hsquare. lia.
  Qed.

  (** The published table constant covers the unit dispatch charge. *)
  Lemma table_unit_budget : forall rw xs,
    (1 <= c_word_table * N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs. pose proof (table_budget_positive rw xs) as Hpositive.
    apply time_of_nat_le in Hpositive. change (N.of_nat 1) with 1%N in Hpositive.
    unfold c_word_table. nia.
  Qed.

  (** The result width square is included in every table budget. *)
  Lemma table_top_square : forall rw xs,
    (N.of_nat ((Pos.to_nat rw + 1) ^ 2) <= N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs. apply time_of_nat_le. unfold table_budget.
    assert (Hsquare : ((Pos.to_nat rw + 1) ^ 2 <=
      (Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2)%nat).
    { apply Nat.pow_le_mono_l. lia. }
    lia.
  Qed.

  (** Positivity of the table budget is preserved by its time-carrier conversion. *)
  Lemma table_budget_positive_N : forall rw xs,
    (1 <= N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs. change 1%N with (N.of_nat 1).
    apply time_of_nat_le. apply table_budget_positive.
  Qed.

  (** A unary arithmetic budget is covered by its operand and the table widths. *)
  Lemma unary_square_budget : forall rw xs wa a k, In (wa, a) xs ->
    (k <= Pos.to_nat wa + Pos.to_nat rw + congr_bits a + 1)%nat ->
    (N.of_nat (k ^ 2) <= 4 * N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs wa a k Hmember Hsize.
    pose proof (member_sum_bound (fun x => D.psize (fst x) (snd x))
      xs (wa, a) Hmember) as Hpayload.
    cbn [fst snd] in Hpayload. rewrite D.psize_congr in Hpayload.
    pose proof (sum_square_bound
      (Pos.to_nat rw +
        fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) + 1)
      (Pos.to_nat wa + congr_bits a + 1) k ltac:(lia)) as Hsquare.
    assert (Hbudget : (k ^ 2 <= 4 * table_budget rw xs)%nat).
    { unfold table_budget.
      eapply Nat.le_trans; [exact Hsquare|].
      apply Nat.mul_le_mono_l. apply Nat.add_le_mono_l. exact Hpayload. }
    apply time_of_nat_le in Hbudget. rewrite Nat2N.inj_mul in Hbudget.
    cost_constants. exact Hbudget.
  Qed.

  (** A binary arithmetic budget is covered even when both operands coincide. *)
  Lemma binary_square_budget : forall rw xs wa a wb b k,
    In (wa, a) xs -> In (wb, b) xs ->
    (k <= Pos.to_nat rw + congr_bits a + congr_bits b + 1)%nat ->
    (N.of_nat (k ^ 2) <= 32 * N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs wa a wb b k Ha Hb Hsize.
    pose proof (member_sum_bound (fun x => D.psize (fst x) (snd x))
      xs (wa, a) Ha) as Hasize.
    pose proof (member_sum_bound (fun x => D.psize (fst x) (snd x))
      xs (wb, b) Hb) as Hbsize.
    cbn [fst snd] in Hasize, Hbsize.
    rewrite D.psize_congr in Hasize, Hbsize.
    pose proof (triple_square_bound
      (Pos.to_nat rw +
        fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) + 1)
      (Pos.to_nat wa + congr_bits a + 1) (Pos.to_nat wb + congr_bits b + 1) k
      ltac:(lia)) as Hsquare.
    assert (Hbudget : (k ^ 2 <= 32 * table_budget rw xs)%nat).
    { unfold table_budget. unfold D.p in *. lia. }
    apply time_of_nat_le in Hbudget. rewrite Nat2N.inj_mul in Hbudget.
    cost_constants. exact Hbudget.
  Qed.

  (** Scaling a call budget preserves an upper bound on its time. *)
  Lemma scaled_cost : forall t c g k budget : N,
    (t <= c * g -> g <= k * budget -> t <= k * c * budget)%N.
  Proof.
    intros t c g k budget Hcost Hbudget.
    eapply N.le_trans; [exact Hcost|].
    eapply N.le_trans with (m := (c * (k * budget))%N).
    - apply N.mul_le_mono_l. exact Hbudget.
    - nia.
  Qed.

  (** A top fallback fits within the table time budget. *)
  Lemma top_time_budget : forall rw xs,
    (D.T_ptop rw <= D.c_payload * N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs. eapply N.le_trans; [apply D.T_ptop_le|].
    apply N.mul_le_mono_l. apply table_top_square.
  Qed.

  (** A top fallback fits within the table result-size budget. *)
  Lemma top_size_budget : forall rw xs,
    (N.of_nat (D.psize rw (D.ptop rw)) <=
      D.c_payload * N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs. eapply N.le_trans; [apply D.ptop_size|].
    apply N.mul_le_mono_l. apply table_top_square.
  Qed.

  (** Joining two table operands fits the sum of their declared payload budgets. *)
  Lemma join_call_budget : forall rw xs wa a wb b t,
    In (wa, a) xs -> In (wb, b) xs ->
    (t <= D.c_payload * N.of_nat (D.psize rw a + D.psize rw b + 1))%N ->
    (t <= 9 * D.c_payload * N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs wa a wb b t Ha Hb Hcost.
    pose proof (unary_square_budget rw xs wa a
      (Pos.to_nat rw + congr_bits a + 1) Ha ltac:(lia)) as Hasize.
    pose proof (unary_square_budget rw xs wb b
      (Pos.to_nat rw + congr_bits b + 1) Hb ltac:(lia)) as Hbsize.
    rewrite <- (D.psize_congr rw a) in Hasize.
    rewrite <- (D.psize_congr rw b) in Hbsize.
    pose proof (table_budget_positive rw xs) as Hpositive.
    apply time_of_nat_le in Hpositive. change (N.of_nat 1) with 1%N in Hpositive.
    eapply scaled_cost; [exact Hcost|].
    rewrite !Nat2N.inj_add. change (N.of_nat 1) with 1%N. lia.
  Qed.

  (** A result bounded by the result width fits the table size budget. *)
  Lemma normalized_output_budget : forall rw xs r,
    (congr_bits r <= 2 * Pos.to_nat rw)%nat ->
    (N.of_nat (D.psize rw r) <= 9 * N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs r Hbits.
    assert (Hsize : (D.psize rw r <= 9 * (Pos.to_nat rw + 1) ^ 2)%nat).
    { rewrite D.psize_congr.
      replace (9 * (Pos.to_nat rw + 1) ^ 2)%nat with
        ((3 * (Pos.to_nat rw + 1)) ^ 2)%nat by (rewrite Nat.pow_mul_l; reflexivity).
      apply Nat.pow_le_mono_l. lia. }
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_mul in Hsize. cost_constants.
    pose proof (table_top_square rw xs). lia.
  Qed.

  (** Comparing positive widths charges at most their first operand's bit length. *)
  Lemma positive_leb_time : forall wa wb,
    (Pos.T_leb wa wb <= N.of_nat (Pos.size_nat wa) + 2)%N.
  Proof.
    intros wa wb. pose proof (Pos.T_compare_le wa wb).
    time_unfold Pos.T_leb. destruct (Pos.compare wa wb); lia.
  Qed.

  (** Comparing a declared operand width fits the table width budget. *)
  Lemma width_comparison_budget : forall rw xs wa a wb, In (wa, a) xs ->
    (Pos.T_eqb wa wb <= N.of_nat (table_budget rw xs) /\
     Pos.T_leb wa wb <= 2 * N.of_nat (table_budget rw xs))%N.
  Proof.
    intros rw xs wa a wb Hmember.
    pose proof (member_sum_bound (fun x => Pos.to_nat (fst x)) xs (wa, a) Hmember)
      as Hwidth. cbn [fst] in Hwidth.
    pose proof (WordTime.positive_size_value wa) as Hbits.
    pose proof (table_budget_width rw xs) as Hbudget.
    assert (Hsize : (Pos.size_nat wa + 1 <= table_budget rw xs)%nat) by lia.
    apply time_of_nat_le in Hsize. rewrite Nat2N.inj_add in Hsize. cost_constants.
    pose proof (Pos.T_eqb_le wa wb). pose proof (positive_leb_time wa wb).
    split; lia.
  Qed.

  (** Unary dispatch charges its width check and selected transfer call. *)
  Lemma unary_forward_time : forall o rw wa a,
    (T_wfwd o rw [(wa, a)] <= c_word_table *
      N.of_nat (table_budget rw [(wa, a)]))%N.
  Proof.
    intros o rw wa a.
    assert (Hmember : In (wa, a) [(wa, a)]) by (left; reflexivity).
    pose proof (table_unit_budget rw [(wa, a)]) as Hunit.
    pose proof (table_budget_positive_N rw [(wa, a)]) as Hpositive.
    pose proof (unary_square_budget rw [(wa, a)] wa a
      (Pos.to_nat rw + congr_bits a + 1) Hmember ltac:(lia)) as Hsquare.
    pose proof (unary_square_budget rw [(wa, a)] wa a
      (Pos.to_nat wa + Pos.to_nat rw + congr_bits a + 1) Hmember ltac:(lia))
      as Hprojectsquare.
    pose proof (scaled_cost _ _ _ _ _ (D.T_congr_neg_le rw a) Hsquare) as Hneg.
    pose proof (scaled_cost _ _ _ _ _ (D.T_congr_norm_le rw a) Hsquare) as Hnorm.
    pose proof (scaled_cost _ _ _ _ _ (D.T_congr_project_le wa rw a) Hprojectsquare)
      as Hproject.
    pose proof (top_time_budget rw [(wa, a)]) as Htop.
    destruct (width_comparison_budget rw [(wa, a)] wa a rw Hmember) as [Heq Hle].
    clear Hsquare Hprojectsquare.
    destruct o; time_unfold T_wfwd; cbn beta iota zeta; try exact Hunit.
    - destruct (Pos.eqb wa rw); unfold c_word_table; nia.
    - destruct (Pos.leb wa rw); unfold c_word_table; nia.
    - unfold c_word_table. nia.
  Qed.

  (** Binary dispatch charges both width checks and the selected transfer call. *)
  Lemma binary_forward_time : forall o rw wa a wb b,
    (T_wfwd o rw [(wa, a); (wb, b)] <= c_word_table *
      N.of_nat (table_budget rw [(wa, a); (wb, b)]))%N.
  Proof.
    intros o rw wa a wb b.
    assert (Ha : In (wa, a) [(wa, a); (wb, b)]) by (left; reflexivity).
    assert (Hb : In (wb, b) [(wa, a); (wb, b)]) by (right; left; reflexivity).
    pose proof (table_unit_budget rw [(wa, a); (wb, b)]) as Hunit.
    pose proof (table_budget_positive_N rw [(wa, a); (wb, b)]) as Hpositive.
    pose proof (binary_square_budget rw [(wa, a); (wb, b)] wa a wb b
      (Pos.to_nat rw + congr_bits a + congr_bits b + 1) Ha Hb ltac:(lia)) as Hsquare.
    pose proof (scaled_cost _ _ _ _ _ (D.T_congr_add_le rw a b) Hsquare) as Hadd.
    pose proof (scaled_cost _ _ _ _ _ (D.T_congr_sub_le rw a b) Hsquare) as Hsub.
    pose proof (scaled_cost _ _ _ _ _ (D.T_congr_mul_le rw a b) Hsquare) as Hmul.
    pose proof (scaled_cost _ _ _ _ _ (D.T_congr_shl_le rw a b) Hsquare) as Hshl.
    pose proof (scaled_cost _ _ _ _ _ (D.T_congr_urem_le rw a b) Hsquare) as Hurem.
    pose proof (top_time_budget rw [(wa, a); (wb, b)]) as Htop.
    destruct (width_comparison_budget rw [(wa, a); (wb, b)] wa a rw Ha) as [Heqa _].
    destruct (width_comparison_budget rw [(wa, a); (wb, b)] wb b rw Hb) as [Heqb _].
    pose proof (Datatypes.T_andb_le (Pos.eqb wa rw) (Pos.eqb wb rw)) as Hboth.
    clear Hsquare.
    destruct o; time_unfold T_wfwd; cbn beta iota zeta; try exact Hunit.
    all: destruct (Pos.eqb wa rw && Pos.eqb wb rw); unfold c_word_table; nia.
  Qed.

  (** Selection dispatch charges the branch width checks and payload join. *)
  Lemma select_forward_time : forall o rw wc c wa a wb b,
    (T_wfwd o rw [(wc, c); (wa, a); (wb, b)] <= c_word_table *
      N.of_nat (table_budget rw [(wc, c); (wa, a); (wb, b)]))%N.
  Proof.
    intros o rw wc c wa a wb b.
    assert (Ha : In (wa, a) [(wc, c); (wa, a); (wb, b)])
      by (right; left; reflexivity).
    assert (Hb : In (wb, b) [(wc, c); (wa, a); (wb, b)])
      by (right; right; left; reflexivity).
    pose proof (table_unit_budget rw [(wc, c); (wa, a); (wb, b)]) as Hunit.
    pose proof (table_budget_positive_N rw [(wc, c); (wa, a); (wb, b)]) as Hpositive.
    pose proof (join_call_budget rw [(wc, c); (wa, a); (wb, b)] wa a wb b
      (D.T_pjoin rw a b) Ha Hb (D.T_pjoin_le rw a b)) as Hjoin.
    pose proof (top_time_budget rw [(wc, c); (wa, a); (wb, b)]) as Htop.
    destruct (width_comparison_budget rw [(wc, c); (wa, a); (wb, b)] wa a rw Ha)
      as [Heqa _].
    destruct (width_comparison_budget rw [(wc, c); (wa, a); (wb, b)] wb b rw Hb)
      as [Heqb _].
    pose proof (Datatypes.T_andb_le (Pos.eqb wa rw) (Pos.eqb wb rw)) as Hboth.
    destruct o; time_unfold T_wfwd; cbn beta iota zeta; try exact Hunit.
    destruct (Pos.eqb wa rw && Pos.eqb wb rw); unfold c_word_table; nia.
  Qed.

  (** Every supported unary table result fits the declared table budget. *)
  Lemma unary_forward_size : forall o rw wa a r, wfwd o rw [(wa, a)] = Some r ->
    (N.of_nat (D.psize rw r) <= c_word_table *
      N.of_nat (table_budget rw [(wa, a)]))%N.
  Proof.
    intros o rw wa a r Hresult.
    pose proof (table_budget_positive_N rw [(wa, a)]) as Hpositive.
    pose proof (normalized_output_budget rw [(wa, a)] (D.congr_neg rw a)
      (D.congr_neg_bits rw a)) as Hneg.
    pose proof (normalized_output_budget rw [(wa, a)] (D.congr_norm rw a)
      (D.congr_norm_bits rw a)) as Hnorm.
    pose proof (normalized_output_budget rw [(wa, a)] (D.congr_project wa rw a)
      (D.congr_project_bits wa rw a)) as Hproject.
    pose proof (top_size_budget rw [(wa, a)]) as Htop.
    destruct o; cbn [wfwd] in Hresult; try discriminate.
    - destruct (Pos.eqb wa rw) in Hresult; injection Hresult as <-;
        unfold c_word_table; nia.
    - destruct (Pos.leb wa rw) in Hresult; injection Hresult as <-;
        unfold c_word_table; nia.
    - injection Hresult as <-. unfold c_word_table. nia.
  Qed.

  (** Every supported binary table result fits the declared table budget. *)
  Lemma binary_forward_size : forall o rw wa a wb b r,
    wfwd o rw [(wa, a); (wb, b)] = Some r ->
    (N.of_nat (D.psize rw r) <= c_word_table *
      N.of_nat (table_budget rw [(wa, a); (wb, b)]))%N.
  Proof.
    intros o rw wa a wb b r Hresult.
    pose proof (table_budget_positive_N rw [(wa, a); (wb, b)]) as Hpositive.
    destruct (D.congr_binary_bits rw a b) as [Ha [Hs [Hm [Hl Hr]]]].
    pose proof (normalized_output_budget rw [(wa, a); (wb, b)]
      (D.congr_add rw a b) Ha) as Hadd.
    pose proof (normalized_output_budget rw [(wa, a); (wb, b)]
      (D.congr_sub rw a b) Hs) as Hsub.
    pose proof (normalized_output_budget rw [(wa, a); (wb, b)]
      (D.congr_mul rw a b) Hm) as Hmul.
    pose proof (normalized_output_budget rw [(wa, a); (wb, b)]
      (D.congr_shl rw a b) Hl) as Hshl.
    pose proof (normalized_output_budget rw [(wa, a); (wb, b)]
      (D.congr_urem rw a b) Hr) as Hurem.
    pose proof (top_size_budget rw [(wa, a); (wb, b)]) as Htop.
    destruct o; cbn [wfwd] in Hresult; try discriminate.
    all: destruct (Pos.eqb wa rw && Pos.eqb wb rw) in Hresult;
      injection Hresult as <-; unfold c_word_table; nia.
  Qed.

  (** A selected branch join or top fallback fits the declared table budget. *)
  Lemma select_forward_size : forall o rw wc c wa a wb b r,
    wfwd o rw [(wc, c); (wa, a); (wb, b)] = Some r ->
    (N.of_nat (D.psize rw r) <= c_word_table *
      N.of_nat (table_budget rw [(wc, c); (wa, a); (wb, b)]))%N.
  Proof.
    intros o rw wc c wa a wb b r Hresult.
    assert (Ha : In (wa, a) [(wc, c); (wa, a); (wb, b)])
      by (right; left; reflexivity).
    assert (Hb : In (wb, b) [(wc, c); (wa, a); (wb, b)])
      by (right; right; left; reflexivity).
    pose proof (table_budget_positive_N rw [(wc, c); (wa, a); (wb, b)]) as Hpositive.
    pose proof (join_call_budget rw [(wc, c); (wa, a); (wb, b)] wa a wb b
      (N.of_nat (D.psize rw (D.pjoin rw a b))) Ha Hb (D.pjoin_size rw a b)) as Hjoin.
    pose proof (top_size_budget rw [(wc, c); (wa, a); (wb, b)]) as Htop.
    destruct o; cbn [wfwd] in Hresult; try discriminate.
    destruct (Pos.eqb wa rw && Pos.eqb wb rw) in Hresult;
      injection Hresult as <-; unfold c_word_table; nia.
  Qed.

  (** The result stays within its declared work budget. *)
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw xs.
    change (T_wfwd o rw xs <= c_word_table * N.of_nat (table_budget rw xs))%N.
    destruct xs as [|[w1 a1] xs].
    - pose proof (table_unit_budget rw []) as Hunit.
      destruct o; time_unfold T_wfwd; exact Hunit.
    - destruct xs as [|[w2 a2] xs].
      + apply unary_forward_time.
      + destruct xs as [|[w3 a3] xs].
        * apply binary_forward_time.
        * destruct xs as [|[w4 a4] xs].
          -- apply select_forward_time.
          -- pose proof (table_unit_budget rw
               ((w1, a1) :: (w2, a2) :: (w3, a3) :: (w4, a4) :: xs)) as Hunit.
             destruct o; time_unfold T_wfwd; exact Hunit.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        D.psize rw q +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs. pose proof (table_budget_positive rw xs) as Hbudget.
    unfold table_budget in Hbudget.
    assert (Hpositive : (1 <= N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        D.psize rw q +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N).
    { change 1%N with (N.of_nat 1). apply time_of_nat_le. lia. }
    time_unfold T_wbwd. unfold c_word_table. nia.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (D.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw xs r Hresult.
    change (N.of_nat (D.psize rw r) <=
      c_word_table * N.of_nat (table_budget rw xs))%N.
    destruct xs as [|[w1 a1] xs].
    - destruct o; cbn [wfwd] in Hresult; discriminate.
    - destruct xs as [|[w2 a2] xs].
      + eapply unary_forward_size. exact Hresult.
      + destruct xs as [|[w3 a3] xs].
        * eapply binary_forward_size. exact Hresult.
        * destruct xs as [|[w4 a4] xs].
          -- eapply select_forward_size. exact Hresult.
          -- destruct o; cbn [wfwd] in Hresult; discriminate.
  Qed.
  (** The result stays within its declared work budget. *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => D.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        D.psize rw q +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof.
    intros o rw q xs ys Hresult. discriminate Hresult.
  Qed.
End CongruenceTableT.
