(** * Exact first-failure specification

    The binary recursion visits successive indices and stops at the earliest failed test.
    For example, width-two values zero, two, zero, two never fail an unsigned test below three.
    Builds on: AnalysesLoopsChrec and BitsWord. *)

From Stdlib Require Import List Bool Arith Lia ZArith NArith PArith.
From Galois.Bits Require Import BitsWord.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec.
Import Chrec.

Module Failure.

(** The executable comparison observes the same wrapped words as the proposition. *)
Definition test_check (w : width) (sg : signedness) (c : cmp_kind) (a b : Z) : bool :=
  match c with
  | CmpLt => (view_z w sg a <? view_z w sg b)%Z
  | CmpLe => (view_z w sg a <=? view_z w sg b)%Z
  | CmpNe => negb (Z.eqb (view_z w sg a) (view_z w sg b))
  end.

(** Boolean continuation tests decide the corresponding word comparison. *)
Theorem test_check_spec w sg c a b :
  test_check w sg c a b = true <-> test_holds w sg c a b.
Proof.
  destruct c; unfold test_check, test_holds.
  - apply Z.ltb_lt.
  - apply Z.leb_le.
  - rewrite Bool.negb_true_iff, Z.eqb_neq; reflexivity.
Qed.

(** An interval result identifies its first failure or certifies every point in the interval. *)
Definition failure_interval (f : N -> bool) (start len : N) (r : option N) : Prop :=
  match r with
  | Some t =>
    (start <= t < start + len)%N /\ f t = false /\
      forall k, (start <= k < t)%N -> f k = true
  | None => forall k, (start <= k < start + len)%N -> f k = true
  end.

(** Searching a singleton reads its sole index. *)
Definition failure_one (f : N -> bool) (start : N) : option N :=
  if f start then None else Some start.

(** Sequential search delays the second interval until the first returns no failure. *)
Definition failure_append (r : option N) (next : unit -> option N) : option N :=
  match r with
  | Some t => Some t
  | None => next tt
  end.

Lemma failure_one_correct f start : failure_interval f start 1 (failure_one f start).
Proof.
  unfold failure_one; destruct (f start) eqn:Htest; cbn [failure_interval].
  - intros k Hk; assert (k = start) by lia; subst k; exact Htest.
  - split; [lia|]; split; [exact Htest|]; intros k Hk; lia.
Qed.

Lemma failure_append_correct f start n m r next :
  failure_interval f start n r ->
  (r = None -> failure_interval f (start + n) m (next tt)) ->
  failure_interval f start (n + m) (failure_append r next).
Proof.
  destruct r as [t|]; cbn [failure_interval failure_append].
  - intros [Ht [Htest Hbefore]] _; split; [lia|]; split; assumption.
  - intros Hfirst Hnext; specialize (Hnext eq_refl).
    destruct (next tt) as [t|]; cbn [failure_interval] in *.
    + destruct Hnext as [Ht [Htest Hbefore]]; split; [lia|]; split; [exact Htest|].
      intros k Hk; destruct (N.lt_ge_cases k (start + n)) as [Hleft|Hright].
      * apply Hfirst; lia.
      * apply Hbefore; lia.
    + intros k Hk; destruct (N.lt_ge_cases k (start + n)) as [Hleft|Hright].
      * apply Hfirst; lia.
      * apply Hnext; lia.
Qed.

(** Binary length recursion visits each reached index without constructing unary fuel. *)
Fixpoint failure_search (len : positive) (f : N -> bool) (start : N) : option N :=
  match len with
  | xH => failure_one f start
  | xO p =>
    failure_append (failure_search p f start)
      (fun _ => failure_search p f (start + N.pos p))
  | xI p =>
    failure_append (failure_search p f start)
      (fun _ => failure_append (failure_search p f (start + N.pos p))
        (fun _ => failure_one f (start + N.pos p + N.pos p)))
  end.

Lemma binary_length_even p : N.pos (xO p) = (N.pos p + N.pos p)%N.
Proof.
  change (N.double (N.pos p) = (N.pos p + N.pos p)%N).
  rewrite N.double_spec; lia.
Qed.

Lemma binary_length_odd p : N.pos (xI p) = (N.pos p + (N.pos p + 1))%N.
Proof.
  change (N.succ_double (N.pos p) = (N.pos p + (N.pos p + 1))%N).
  rewrite N.succ_double_spec; lia.
Qed.

(** Exact search returns the first failure in its entire stated finite interval. *)
Theorem failure_search_correct len f start :
  failure_interval f start (N.pos len) (failure_search len f start).
Proof.
  revert start; induction len as [p IH|p IH|]; intro start; cbn [failure_search].
  - rewrite binary_length_odd.
    apply failure_append_correct; [apply IH|]; intro Hnone.
    apply failure_append_correct; [apply IH|]; intro Hnone'.
    apply failure_one_correct.
  - rewrite binary_length_even.
    apply failure_append_correct; [apply IH|]; intro Hnone; apply IH.
  - apply failure_one_correct.
Qed.

(** A whole word modulus is a binary period for every affine word sequence. *)
Definition word_period (w : width) : positive := Pos.pow 2 w.

Lemma word_period_modulus w : Z.of_N (N.pos (word_period w)) = modulus w.
Proof.
  exact (Pos2Z.inj_pow 2 w).
Qed.

(** Congruent integers have identical observations under either signedness. *)
Theorem view_z_congruent w sg a b :
  wrap w a = wrap w b -> view_z w sg a = view_z w sg b.
Proof.
  intro Heq; unfold view_z; rewrite Heq; reflexivity.
Qed.

(** Reducing an affine index modulo the binary period leaves its observed word unchanged. *)
Theorem affine_word_period w a step k :
  wrap w (a + step * Z.of_N k) =
  wrap w (a + step * Z.of_N (k mod N.pos (word_period w))).
Proof.
  rewrite N2Z.inj_mod, word_period_modulus.
  pose proof (Z.div_mod (Z.of_N k) (modulus w) (modulus_nonzero w)) as Hdiv.
  replace (a + step * Z.of_N k)%Z with
    (a + step * (Z.of_N k mod modulus w) +
      (step * (Z.of_N k / modulus w)) * modulus w)%Z by nia.
  apply wrap_add_modulus.
Qed.

(** The specification tests wrapped affine values at binary indices. *)
Definition affine_test w sg cmp a step bound (k : N) : bool :=
  test_check w sg cmp (a + step * Z.of_N k) bound.

(** The wrapped continuation test repeats after one word period. *)
Theorem affine_test_period w sg cmp a step bound k :
  affine_test w sg cmp a step bound k =
    affine_test w sg cmp a step bound (k mod N.pos (word_period w)).
Proof.
  unfold affine_test, test_check.
  rewrite (view_z_congruent w sg _ _ (affine_word_period w a step k)); reflexivity.
Qed.

Lemma affine_test_zero_step w sg cmp a step bound : wrap w step = 0%Z ->
  forall k, affine_test w sg cmp a step bound k = affine_test w sg cmp a step bound 0.
Proof.
  intros Hzero k; unfold affine_test.
  assert (Heq : wrap w (a + step * Z.of_N k) = wrap w a).
  { rewrite wrap_add, wrap_mul, Hzero; cbn [Z.mul]; rewrite wrap_0, Z.add_0_r;
      apply wrap_wrap. }
  unfold test_check.
  rewrite (view_z_congruent w sg _ _ Heq), Z.mul_0_r, Z.add_0_r; reflexivity.
Qed.

(** Exact affine search tests one constant word or an entire word period. *)
Definition first_failure w sg cmp a step bound : option N :=
  if (wrap w step =? 0)%Z then
    failure_one (affine_test w sg cmp a step bound) 0
  else failure_search (word_period w) (affine_test w sg cmp a step bound) 0.

(** A successful affine search identifies the exact first failed wrapped comparison. *)
Theorem affine_first_failure_sound w sg cmp a step bound t :
  first_failure w sg cmp a step bound = Some t ->
  (forall k, (k < t)%N -> affine_test w sg cmp a step bound k = true) /\
    affine_test w sg cmp a step bound t = false.
Proof.
  unfold first_failure; destruct (wrap w step =? 0)%Z eqn:Hzero.
  - unfold failure_one; destruct (affine_test w sg cmp a step bound 0) eqn:Htest;
      intro Heq; [discriminate|]; inversion Heq; subst t.
    split; [intros k Hk; lia|exact Htest].
  - intro Hsearch.
    pose proof (failure_search_correct (word_period w)
      (affine_test w sg cmp a step bound) 0) as Hcorrect.
    rewrite Hsearch in Hcorrect; cbn [failure_interval] in Hcorrect.
    destruct Hcorrect as [Ht [Htest Hbefore]]; split; [|exact Htest].
    intros k Hk; apply Hbefore; lia.
Qed.

(** No affine failure means that every index satisfies the wrapped continuation test. *)
Theorem affine_first_failure_none w sg cmp a step bound :
  first_failure w sg cmp a step bound = None <->
    forall k, affine_test w sg cmp a step bound k = true.
Proof.
  unfold first_failure; destruct (wrap w step =? 0)%Z eqn:Hzero.
  - apply Z.eqb_eq in Hzero; unfold failure_one.
    destruct (affine_test w sg cmp a step bound 0) eqn:Htest; split.
    + intros _ k; rewrite (affine_test_zero_step w sg cmp a step bound Hzero); exact Htest.
    + intro Hall; reflexivity.
    + discriminate.
    + intro Hall; specialize (Hall 0%N); congruence.
  - pose proof (failure_search_correct (word_period w)
      (affine_test w sg cmp a step bound) 0) as Hcorrect.
    destruct (failure_search (word_period w) (affine_test w sg cmp a step bound) 0)
      as [t|] eqn:Hsearch; cbn [failure_interval] in Hcorrect; split.
    + discriminate.
    + intro Hall; destruct Hcorrect as [_ [Htest _]]; specialize (Hall t); congruence.
    + intros _ k; rewrite affine_test_period; apply Hcorrect.
      split; [apply N.le_0_l|]; rewrite N.add_0_l; apply N.mod_lt; discriminate.
    + intro Hall; reflexivity.
Qed.

(** A first failed comparison is returned at its unique earliest index. *)
Theorem affine_first_failure_complete w sg cmp a step bound t :
  (forall k, (k < t)%N -> affine_test w sg cmp a step bound k = true) ->
  affine_test w sg cmp a step bound t = false ->
  first_failure w sg cmp a step bound = Some t.
Proof.
  intros Hbefore Hfailed.
  destruct (first_failure w sg cmp a step bound) as [j|] eqn:Hsearch.
  - destruct (affine_first_failure_sound w sg cmp a step bound j Hsearch)
      as [Hbefore' Hfailed'].
    assert (j = t).
    { destruct (N.lt_trichotomy j t) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
      - specialize (Hbefore j Hlt); congruence.
      - specialize (Hbefore' t Hgt); congruence. }
    subst j; reflexivity.
  - pose proof (proj1 (affine_first_failure_none w sg cmp a step bound) Hsearch t)
      as Hholds; congruence.
Qed.

(** Trip counts are exact first failures for additive recurrences with invariant steps. *)
Definition trip_count {V} (inv : V -> Z) (w : width) (sg : signedness) (c : cmp_kind)
    (ch : Chrec.t V) (bound : iexpr V) : option N :=
  match ch with
  | CRec base (CInv step) =>
    first_failure w sg c (Chrec.eval inv base O) (eval_iexpr inv step)
      (eval_iexpr inv bound)
  | _ => None
  end.

(** Successful trip counting establishes first failure without any no-wrap premise. *)
Theorem trip_count_first_failure {V} (inv : V -> Z) w sg cmp ch bound t :
  trip_count inv w sg cmp ch bound = Some t ->
  (forall k, (N.of_nat k < t)%N ->
    test_holds w sg cmp (Chrec.eval inv ch k) (eval_iexpr inv bound)) /\
  ~ test_holds w sg cmp (Chrec.eval inv ch (N.to_nat t)) (eval_iexpr inv bound).
Proof.
  destruct ch as [e|base step|base ratio|a b|a b]; try discriminate.
  destruct step as [step|a b|a b|a b|a b]; try discriminate.
  intro Hcount; apply affine_first_failure_sound in Hcount.
  destruct Hcount as [Hbefore Hfailed]; split.
  - intros k Hk; rewrite Chrec.eval_affine; apply test_check_spec.
    specialize (Hbefore (N.of_nat k) Hk); unfold affine_test in Hbefore.
    rewrite nat_N_Z, Z.mul_comm in Hbefore; exact Hbefore.
  - rewrite Chrec.eval_affine; intro Hholds; apply test_check_spec in Hholds.
    unfold affine_test in Hfailed; rewrite N_nat_Z, Z.mul_comm in Hholds; congruence.
Qed.

(** An affine trip counter returns None exactly when continuation never fails. *)
Theorem trip_count_affine_none {V} (inv : V -> Z) w sg cmp base step bound :
  trip_count inv w sg cmp (CRec base (CInv step)) bound = None <->
  forall k, test_holds w sg cmp
    (Chrec.eval inv (CRec base (CInv step)) k) (eval_iexpr inv bound).
Proof.
  unfold trip_count.
  rewrite affine_first_failure_none; split.
  - intros Hall k; rewrite Chrec.eval_affine; apply test_check_spec.
    specialize (Hall (N.of_nat k)); unfold affine_test in Hall.
    rewrite nat_N_Z, Z.mul_comm in Hall; exact Hall.
  - intros Hall k; unfold affine_test; apply test_check_spec.
    specialize (Hall (N.to_nat k));
      rewrite Chrec.eval_affine, N_nat_Z, Z.mul_comm in Hall; exact Hall.
Qed.

(** The representable-range checker decides the no-wrap interval. *)
Definition in_range_check (w : width) (sg : signedness) (z : Z) : bool :=
  match sg with
  | Unsigned => (0 <=? z)%Z && (z <? modulus w)%Z
  | Signed => (- (modulus w / 2) <=? z)%Z && (z <? modulus w / 2)%Z
  end.

Lemma in_range_check_spec w sg z : in_range_check w sg z = true <-> in_range w sg z.
Proof.
  destruct sg; unfold in_range_check, in_range;
    rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; reflexivity.
Qed.

(** No-wrap checking bounds the mathematical base, endpoint and invariant bound independently. *)
Definition nowrap_check {V} (w : width) (sg : signedness) (inv : V -> Z) (ch : Chrec.t V)
    (bound : iexpr V) (t : N) : bool :=
  match ch with
  | CRec base (CInv step) =>
    let a := Chrec.eval inv base O in
    let s := eval_iexpr inv step in
    in_range_check w sg a && in_range_check w sg (a + s * Z.of_N t) &&
      in_range_check w sg (eval_iexpr inv bound)
  | _ => false
  end.

Lemma affine_range_between w sg a step t k :
  (0 <= k <= t)%Z -> in_range w sg a -> in_range w sg (a + step * t) ->
  in_range w sg (a + step * k).
Proof.
  intros Hindex Hbase Hend; destruct sg; cbn [in_range] in *;
    destruct (Z.le_gt_cases 0 step); nia.
Qed.

(** Endpoint checking proves that every recurrence value through the endpoint stays in range. *)
Theorem nowrap_check_sound {V} w sg (inv : V -> Z) ch bound t :
  nowrap_check w sg inv ch bound t = true ->
  (forall k, (N.of_nat k <= t)%N -> in_range w sg (Chrec.eval inv ch k)) /\
    in_range w sg (eval_iexpr inv bound).
Proof.
  destruct ch as [e|base step|base ratio|a b|a b]; try discriminate.
  destruct step as [step|a b|a b|a b|a b]; try discriminate.
  unfold nowrap_check; rewrite !Bool.andb_true_iff, !in_range_check_spec.
  intros [[Hbase Hend] Hbound]; split; [|exact Hbound].
  intros k Hindex; rewrite Chrec.eval_affine, Z.mul_comm; eapply affine_range_between;
    [|exact Hbase|exact Hend].
  apply N2Z.inj_le in Hindex; rewrite nat_N_Z in Hindex; lia.
Qed.

(** Exact wrapped trip counts and separate no-wrap evidence establish all four arithmetic claims. *)
Theorem trip_count_sound {V} (inv : V -> Z) (w : width) (sg : signedness) (cmp : cmp_kind)
    (ch : Chrec.t V) (bound : iexpr V) (t : N) :
  trip_count inv w sg cmp ch bound = Some t -> nowrap_check w sg inv ch bound t = true ->
  (forall k, (N.of_nat k < t)%N ->
    test_holds w sg cmp (Chrec.eval inv ch k) (eval_iexpr inv bound)) /\
  ~ test_holds w sg cmp (Chrec.eval inv ch (N.to_nat t)) (eval_iexpr inv bound) /\
  (forall k, (N.of_nat k <= t)%N -> in_range w sg (Chrec.eval inv ch k)) /\
  in_range w sg (eval_iexpr inv bound).
Proof.
  intros Htrip Hnowrap.
  destruct (trip_count_first_failure inv w sg cmp ch bound t Htrip) as [Hbefore Hfailed].
  destruct (nowrap_check_sound w sg inv ch bound t Hnowrap) as [Hrange Hbound].
  split; [exact Hbefore|]; split; [exact Hfailed|]; split; assumption.
Qed.

End Failure.
