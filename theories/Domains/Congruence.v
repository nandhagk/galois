(** * Congruence payload code

    Congruences describe residues of normalized words.
    For example, modulus two and residue zero describe even words.
    Builds on: CongruenceSig and the fixed-width word operations. *)

From Stdlib Require Import ZArith Zpow_facts List Bool Lia Wellfounded.Inverse_Image.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Bits Require Import Word Fun Op Testbit Arith.
From Galois.Domains Require Import CongruenceSig WordSig.
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

  Definition k_div : N := 1%N. (* STUB *)
  Definition k_gcd : N := 1%N. (* STUB *)

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
  Lemma F_div_aligned : forall a b, (0 <= a)%Z -> (0 < b)%Z ->
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
    apply F_div_aligned; lia.
  Qed.


  (** Division charges one dividend scan per quotient bit. *)
  Lemma T_div_aligned_le : forall a b, (0 <= a)%Z -> (0 < b)%Z ->
    (T_div_aligned a b <= k_div *
      N.of_nat ((Z.size_nat a - Z.size_nat b + 2) * (Z.size_nat a + 1)))%N.
  Proof. Admitted. (* STUB *)

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

  (** The full Euclidean coefficient chain has quadratic input-bit work. *)
  Lemma T_extgcd_le : forall a b,
    (T_extgcd a b <= k_gcd *
      N.of_nat ((Z.size_nat a + Z.size_nat b + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)

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
  rewrite Z.pow_add_r by lia. unfold wrap.
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


Module CongruenceCode (L : WORD_LANGUAGE_OPS) <: CONGRUENCE_OPS L.
  Definition p := congr.
  Definition wordb w z := (0 <=? z) && (z <? modulus w).
  Definition congr_norm w c :=
    match c with
    | CBot => CBot
    | C m r =>
      let m' := Z.abs m in
      if m' =? 0 then if wordb w r then C 0 r else CBot else
        let r' := r mod m' in
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
  Definition pwiden (_ : pwparam) w a b :=
    if pleb w b a then a else pjoin w a b.
  Definition pnarrow w a b := pmeet w a b.
  Definition wrap_class w m r := congr_norm w (C (Z.gcd m (modulus w)) r).
  Definition congr_neg w a :=
    match congr_norm w a with CBot => CBot | C m r => wrap_class w m (-r) end.
  Definition congr_add w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd m n) (r + s)
    | _, _ => CBot
    end.
  Definition congr_sub w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd m n) (r - s)
    | _, _ => CBot
    end.
  Definition congr_mul w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd (m * n) (Z.gcd (m * s) (n * r))) (r * s)
    | _, _ => CBot
    end.
  Definition congr_project source target a :=
    match congr_norm source a with CBot => CBot | C m r => wrap_class target m r end.
  Definition congr_shl w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C 0 k =>
      if Zpos w <=? k then C 0 0 else wrap_class w (m * 2 ^ k) (r * 2 ^ k)
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
    unfold congr_norm. destruct (Z.abs m =? 0) eqn:Hm.
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
    destruct c as [|m r]; [exact I|]. unfold congr_norm.
    destruct (Z.abs m =? 0) eqn:Hm.
    - destruct (wordb w r) eqn:Hr; cbn; [left; split|exact I];
        [reflexivity|now apply cong_wordb_spec].
    - apply Z.eqb_neq in Hm. pose proof (Z.abs_nonneg m).
      destruct (modulus w <=? Z.abs m) eqn:Hlarge.
      + destruct (wordb w (r mod Z.abs m)) eqn:Hr; cbn;
          [left; split|exact I]; [reflexivity|now apply cong_wordb_spec].
      + apply Z.leb_gt in Hlarge. right. split; [lia|apply Z.mod_pos_bound; lia].
  Qed.

  Local Lemma cong_canonical_fixed w c : strong_canonical w c -> congr_norm w c = c.
  Proof.
    destruct c as [|m r]; [reflexivity|].
    intros [[-> Hword]|[[Hpositive Hsmall] Hr]]; unfold congr_norm.
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
    intros Hm Hword. unfold congr_norm. rewrite Z.abs_eq by lia.
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
    destruct c as [|m r]; [reflexivity|]. unfold congr_norm.
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
  Lemma norm_gamma : forall w a z,
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
    intro Hz. unfold wrap_class. apply (proj2 (cong_norm_gamma w _ _)).
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
    intros q w a b. unfold pwiden. destruct (pleb w b a).
    - apply cong_raw_leb_refl.
    - exact (proj1 (cong_join_upper w a b)).
  Qed.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof.
    intros q w a b. unfold pwiden. destruct (pleb w b a) eqn:Horder.
    - exact Horder.
    - exact (proj2 (cong_join_upper w a b)).
  Qed.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof.
    intros q w a b Hstable. unfold pwiden. now rewrite Hstable.
  Qed.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof.
    intros q w a b Hnonbottom Hunstable.
    unfold pwiden. rewrite Hunstable.
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
    - unfold pwiden. rewrite Hstable. reflexivity.
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
    intros w a b z Ha Hb. rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a z)) in Ha.
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
    intros w a z Hbot Ha. apply (proj2 (norm_gamma w a z)) in Ha.
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
    intros w a z v Hpoint Hword Ha. apply (proj2 (norm_gamma w a z)) in Ha.
    unfold ppoint in Hpoint. destruct (congr_norm w a) as [| [| m | m] r];
      try discriminate.
    injection Hpoint as <-. destruct Ha as [_ [k Hk]]. lia.
  Qed.
  (** Payload concretization agrees with residue-class membership. *)
  Lemma F1_gamma : forall w a z, pgamma w a z <-> congr_gamma w a z.
  Proof.
    intros w a z. reflexivity.
  Qed.
  (** Normalization keeps precisely the same represented integers. *)
  Lemma F2_norm_gamma : forall w a z,
    pgamma w (congr_norm w a) z <-> pgamma w a z.
  Proof.
    apply norm_gamma.
  Qed.
  (** Negation retains wrapped concrete negation. *)
  Lemma F6_congr_neg_sound : forall w a x,
    pgamma w a x -> pgamma w (congr_neg w a) (L.wrap w (- x)).
  Proof.
    intros w a x Ha. rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a x)) in Ha.
    unfold congr_neg. destruct (congr_norm w a) as [|m r]; [contradiction|].
    destruct Ha as [_ Hresidue]. apply cong_wrap_class_sound.
    apply cong_mod_divide. apply cong_mod_divide in Hresidue.
    destruct Hresidue as [k Hk]. exists (-k). nia.
  Qed.
  (** Addition retains wrapped concrete addition. *)
  Lemma F7_congr_add_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_add w a b) (L.wrap w (x + y)).
  Proof.
    intros w a b x y Ha Hb. rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a x)) in Ha.
    apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold congr_add.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s]; try contradiction.
    destruct Ha as [_ Hx], Hb as [_ Hy]. apply cong_wrap_class_sound.
    apply cong_mod_divide. apply cong_mod_divide in Hx. apply cong_mod_divide in Hy.
    destruct Hx as [i Hi], Hy as [j Hj].
    destruct (Z.gcd_divide_l m n) as [k Hk], (Z.gcd_divide_r m n) as [l Hl].
    exists (i * k + j * l). nia.
  Qed.
  (** Subtraction retains wrapped concrete subtraction. *)
  Lemma F8_congr_sub_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_sub w a b) (L.wrap w (x - y)).
  Proof.
    intros w a b x y Ha Hb. rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a x)) in Ha.
    apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold congr_sub.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n s]; try contradiction.
    destruct Ha as [_ Hx], Hb as [_ Hy]. apply cong_wrap_class_sound.
    apply cong_mod_divide. apply cong_mod_divide in Hx. apply cong_mod_divide in Hy.
    destruct Hx as [i Hi], Hy as [j Hj].
    destruct (Z.gcd_divide_l m n) as [k Hk], (Z.gcd_divide_r m n) as [l Hl].
    exists (i * k - j * l). nia.
  Qed.
  (** Multiplication retains wrapped concrete multiplication. *)
  Lemma F9_congr_mul_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_mul w a b) (L.wrap w (x * y)).
  Proof.
    intros w a b x y Ha Hb. rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a x)) in Ha.
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
  Lemma F10_congr_project_sound : forall source target a x,
    (target <= source)%positive -> pgamma source a x ->
    pgamma target (congr_project source target a) (L.wrap target x).
  Proof.
    intros source target a x Hwidth Ha. rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma source a x)) in Ha.
    unfold congr_project. destruct (congr_norm source a) as [|m r]; [contradiction|].
    apply cong_wrap_class_sound. exact (proj2 Ha).
  Qed.
  (** Shift transfer retains the wrapped concrete shift. *)
  Lemma F11_congr_shl_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y ->
    pgamma w (congr_shl w a b) (L.wrap w (Z.shiftl x y)).
  Proof.
    intros w a b x y Ha Hb.
    rewrite normalized_wshl by (eapply gamma_word; eassumption).
    rewrite <- !gamma_mod_agrees in *. apply (proj2 (cong_norm_gamma w a x)) in Ha.
    apply (proj2 (cong_norm_gamma w b y)) in Hb. unfold congr_shl.
    destruct (congr_norm w a) as [|m r], (congr_norm w b) as [|n k]; try contradiction.
    destruct n as [|n|n]; try (apply cong_top_sound; apply wshl_is_word).
    destruct Ha as [Hwordx Hx], Hb as [Hwordy Hy].
    rewrite Z.mod_0_r in Hy. assert (y = k) by lia. subst y.
    rewrite wshl_value, (wrap_id w k Hwordy), (wrap_id w x Hwordx).
    destruct (Zpos w <=? k).
    - split; [apply zero_is_word|reflexivity].
    - apply cong_wrap_class_sound. apply cong_mod_divide. apply cong_mod_divide in Hx.
      destruct Hx as [i Hi]. exists i. nia.
  Qed.
  (** Remainder transfer retains unsigned remainder, including a zero divisor. *)
  Lemma F12_congr_urem_sound : forall w a b x y,
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
    apply (proj2 (W.F2_norm_gamma target a x)).
    apply (proj2 (W.F1_gamma target a x)).
    apply (proj1 (W.F1_gamma source a x)) in Ha.
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
      now apply W.F6_congr_neg_sound.
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
      rewrite (wrap_id w x Hx). apply W.F10_congr_project_sound.
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
    - rewrite wadd_value. now apply W.F7_congr_add_sound.
    - rewrite wsub_value. now apply W.F8_congr_sub_sound.
    - rewrite wmul_value. now apply W.F9_congr_mul_sound.
    - rewrite <- (normalized_wurem wa x y Hx Hy). now apply W.F12_congr_urem_sound.
    - rewrite <- (normalized_wshl wa x y Hx Hy). now apply W.F11_congr_shl_sound.
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
  Definition F_div_aligned := CongruenceCRT.F_div_aligned.
  Definition extgcd_agrees := CongruenceCRT.extgcd_agrees.
  Definition T_div_aligned_le := CongruenceCRT.T_div_aligned_le.
  Definition T_extgcd_le := CongruenceCRT.T_extgcd_le.
  TimeFun wordb.
  TimeFun congr_norm.
  TimeFun raw_leb.
  TimeFun pleb.
  TimeFun pjoin.
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
  Definition c_payload : N := 1%N. (* STUB *)
  Definition c_congruence : N := 1%N. (* STUB *)
  Definition k_congr_gcd : N := 1%N. (* STUB *)
  Definition k_congr_crt : N := 1%N. (* STUB *)
  Definition k_congr_transfer : N := 1%N. (* STUB *)

  (** Joined payloads fit within the combined operand sizes. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Met payloads fit within the combined operand sizes. *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widened payloads fit within the operand and parameter sizes. *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Narrowed payloads fit within the combined operand sizes. *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload widening charges both operands and its parameters. *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload narrowing charges both payload sizes. *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload inclusion charges the two payload sizes. *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Payload join charges the two payload sizes. *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Payload meet charges the two payload sizes. *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Bottom recognition charges the payload size. *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat ((psize w a + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Point recognition charges the payload size. *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat ((psize w a + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Constant abstraction charges the width and literal bit size. *)
  Lemma T_pconst_le : forall w z, (T_pconst w z <=
    c_payload * N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Payload size uses the tagged width. *)
  Lemma psize_congr : forall w a, psize w a = ((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat.
  Proof. Admitted. (* STUB *)
  (** Normalized payloads fit two words of the width. *)
  Lemma congr_norm_bits : forall w a,
    (congr_bits (congr_norm w a) <= 2 * Pos.to_nat w)%nat.
  Proof. Admitted. (* STUB *)
  (** Negation results fit two words of the width. *)
  Lemma congr_neg_bits : forall w a,
    (congr_bits (congr_neg w a) <= 2 * Pos.to_nat w)%nat.
  Proof. Admitted. (* STUB *)
  (** Binary transfer results fit two words of the width. *)
  Lemma congr_binary_bits : forall w a b,
    (congr_bits (congr_add w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_sub w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_mul w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_shl w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_urem w a b) <= 2 * Pos.to_nat w)%nat.
  Proof. Admitted. (* STUB *)
  (** Projection results fit two words of the target width. *)
  Lemma congr_project_bits : forall source target a,
    (congr_bits (congr_project source target a) <= 2 * Pos.to_nat target)%nat.
  Proof. Admitted. (* STUB *)
  (** Normalization has the published quadratic arithmetic bound. *)
  Lemma T_congr_norm_le : forall w a,
    (T_congr_norm w a <= c_congruence * N.of_nat (((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Negation has the published quadratic arithmetic bound. *)
  Lemma T_congr_neg_le : forall w a,
    (T_congr_neg w a <= c_congruence * N.of_nat (((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Addition has the published quadratic arithmetic bound. *)
  Lemma T_congr_add_le : forall w a b,
    (T_congr_add w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Subtraction has the published quadratic arithmetic bound. *)
  Lemma T_congr_sub_le : forall w a b,
    (T_congr_sub w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Multiplication has the published quadratic arithmetic bound. *)
  Lemma T_congr_mul_le : forall w a b,
    (T_congr_mul w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Shift transfer has the published quadratic arithmetic bound. *)
  Lemma T_congr_shl_le : forall w a b,
    (T_congr_shl w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Remainder transfer has the published quadratic arithmetic bound. *)
  Lemma T_congr_urem_le : forall w a b,
    (T_congr_urem w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Projection charges both source and target widths. *)
  Lemma T_congr_project_le : forall source target a,
    (T_congr_project source target a <=
    c_congruence * N.of_nat
      (((Pos.to_nat source + Pos.to_nat target + congr_bits a + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Congruence multiplication has the published quadratic width bound. *)
  Lemma mul_bigO : (bigO (fun _ => True)
    (fun x : positive * (congr * congr) => N.of_nat
      (((Pos.to_nat (fst x) + congr_bits (fst (snd x)) + congr_bits (snd (snd x)) + 1) ^ 2)%nat))
    (fun x => T_congr_mul (fst x) (fst (snd x)) (snd (snd x))))%N.
  Proof. Admitted. (* STUB *)
  (** Normalization produces a canonical representation. *)
  Lemma F3_norm_canonical : forall w a, canonical w (congr_norm w a).
  Proof.
    intros w a. pose proof (cong_norm_canonical w a) as Hcanonical.
    destruct (congr_norm w a) as [| m r]; [exact I |].
    destruct Hcanonical as [[Hm Hr] | [Hm Hr]].
    - left. split; assumption.
    - right. split; [lia | exact Hr].
  Qed.
  (** Normalization is idempotent. *)
  Lemma F4_norm_idempotent : forall w a,
    congr_norm w (congr_norm w a) = congr_norm w a.
  Proof.
    apply cong_norm_idempotent.
  Qed.
  (** Chinese remainder meet retains each shared integer. *)
  Lemma F5_crt_meet_sound : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof.
    apply pgamma_meet.
  Qed.
  (** The requested congruence rank is bounded by width plus two. *)
  Lemma F13_wrank_le : forall w a, (congr_wrank w a <= Pos.to_nat w + 2)%nat.
  Proof.
    intros w a. change (raw_wrank w (congr_norm w a) <= Pos.to_nat w + 2)%nat.
    apply raw_wrank_bound. apply cong_norm_canonical.
  Qed.
  (** Payload widening uses the normalized congruence rank. *)
  Lemma F14_pwrank : forall q w a, pwrank q w a = congr_wrank w a.
  Proof.
    intros q w a. reflexivity.
  Qed.
  (** Gcd-based joining has the published quadratic arithmetic bound. *)
  Lemma T1_join : forall w a b,
    (T_pjoin w a b <= k_congr_gcd *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Chinese remainder meet has the published quadratic arithmetic bound. *)
  Lemma T2_meet : forall w a b,
    (T_pmeet w a b <= k_congr_crt *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)

  (** The result stays within its declared work budget. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
End CongruenceT.

Module CongruenceTableT (L : WORD_LANGUAGE_T) (D : CONGRUENCE_T L)
    <: CONGRUENCE_TABLE_T L D.
  Include CongruenceTable L D.
  TimeFun wfwd.
  TimeFun wbwd.
  Definition c_word_table : N := 1%N. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        D.psize rw q +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (D.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => D.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        D.psize rw q +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
End CongruenceTableT.
