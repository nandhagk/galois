(** * Primitive simultaneous narrowing bounds

    Pass bounds retain declared-set preparation, frozen query work and every lattice callback.
    For example, an unsuccessful order guard still pays for both lookups and comparison.
    Builds on: FixpointNarrow, FixpointTotalCost and FixpointIndexCost. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointIndexCost FixpointCheck FixpointAnalysis FixpointSolver FixpointNarrow FixpointTotalCost.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module NarrowCost.

Local Lemma left_cost_on {V B} (f : B -> V -> Cost.t B) xs start k :
  (forall s x, In x xs -> Cost.ticks (f s x) <= k) ->
  Cost.ticks (fold_left_c f xs start) <= N.of_nat (length xs) * (1 + k).
Proof.
  intro Hb.
  assert (Hstep : forall s x, True -> In x xs ->
    True /\ Cost.ticks (f s x) + 0 <= k + 0).
  { intros s x _ Hx; split; [exact I|pose proof (Hb s x Hx); lia]. }
  pose proof (ticks_fold_left_c_potential f (fun _ => True) (fun _ => 0)
    k xs start Hstep I).
  nia.
Qed.

Local Lemma right_cost_on {V B} (f : V -> B -> Cost.t B) xs start k :
  (forall x s, In x xs -> Cost.ticks (f x s) <= k) ->
  Cost.ticks (fold_right_c f start xs) <= N.of_nat (length xs) * (1 + k).
Proof.
  intro Hb.
  assert (Hstep : forall x s, In x xs -> True ->
    True /\ Cost.ticks (f x s) + 0 <= k + 0).
  { intros x s Hx _; split; [exact I|pose proof (Hb x s Hx); lia]. }
  pose proof (ticks_fold_right_c_potential f (fun _ => True) (fun _ => 0)
    k xs start Hstep I) as Hfold.
  destruct Hfold; nia.
Qed.

(** A pass's numeric budget adds declared preparation, aggregate collection and selected writes. *)
Definition pass_budget (b : TotalCost.Budget.t) narrowing rows outputs :=
  N.of_nat rows *
    (3 + SystemIndexCost.Budget.target_ticks (TotalCost.Budget.metadata b) +
      SystemIndexCost.Budget.sides_ticks (TotalCost.Budget.metadata b) +
      N.of_nat (SystemIndexCost.Budget.output_count (TotalCost.Budget.metadata b))) +
  SystemIndexCost.Budget.distinct (TotalCost.Budget.metadata b) outputs +
  N.of_nat rows * (1 + TotalCost.Budget.evaluation b +
    N.of_nat (TotalCost.Budget.outputs b) * (1 + TotalCost.Budget.rule b)) +
  N.of_nat outputs *
    (3 + 3 * TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b + narrowing).

Section Pass.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (b : TotalCost.Budget.t) (HB : TotalCost.model a b)
  (narrowing : N).
Hypothesis Hnarrow : forall x y, Cost.ticks (narrow_c (Analysis.lat a) x y) <= narrowing.

Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let SS := Analysis.static a.
Let cs := System.constraints S.
Let rows := length cs.
Let outputs := length (Narrow.outputs a).

Local Lemma declared_key x :
  In x (Narrow.outputs a) -> TotalCost.key_domain a x.
Proof.
  rewrite Narrow.outputs_equation; intro Hx; apply in_flat_map in Hx as [c [Hc Hx]].
  exists c; split; [exact Hc|now left].
Qed.

Local Lemma output_key c old x v :
  In c cs -> In (x, v) (fst (Eval.outputs S c (lookup EX L old))) ->
  TotalCost.key_domain a x.
Proof.
  intros Hc Hv; exists c; split; [exact Hc|left].
  rewrite Eval.outputs_spec in Hv; cbn [fst] in Hv; destruct Hv as [Heq|Hv].
  - injection Heq as <- <-; now left.
  - right; apply (System.sides_within (Analysis.static_law HL) c (lookup EX L old)).
    apply in_map_iff; exists (x, v); split; [reflexivity|exact Hv].
Qed.

Local Lemma apply_cost outs sums :
  (forall x v, In (x, v) outs -> TotalCost.key_domain a x) ->
  Cost.ticks (Update.apply_c EX L (join_c L) outs sums) <=
    N.of_nat (length outs) * (1 + TotalCost.Budget.rule b).
Proof.
  revert sums; induction outs as [|[x v] outs IH]; intros sums Hkeys;
    rewrite Update.apply_cost.
  - cbn [length]; lia.
  - specialize (IH (fst (Update.rule EX L (join_c L) sums x v))
      (fun y w Hw => Hkeys y w (or_intror Hw))).
    pose proof (TotalCost.rule_cost a b HB sums x v
      (Hkeys x v (or_introl eq_refl))) as Hrule.
    change (Cost.ticks (Update.rule_c EX L (join_c L) sums x v) <=
      TotalCost.Budget.rule b) in Hrule.
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Aggregate collection evaluates each original row once against the frozen assignment. *)
Theorem collect_cost old :
  Cost.ticks (Narrow.collect_c a old) <= N.of_nat rows *
    (1 + TotalCost.Budget.evaluation b +
      N.of_nat (TotalCost.Budget.outputs b) * (1 + TotalCost.Budget.rule b)).
Proof.
  unfold Narrow.collect_c.
  eapply N.le_trans with (m := N.of_nat (length cs) *
    (1 + (TotalCost.Budget.evaluation b +
      N.of_nat (TotalCost.Budget.outputs b) * (1 + TotalCost.Budget.rule b)))).
  - apply left_cost_on.
    intros sums c Hc; fold EX L S.
    rewrite Cost.ticks_bind, Cost.ticks_map.
    rewrite (Eval.outputs_c_spec S c _ (lookup EX L old)) by reflexivity.
    pose proof (TotalCost.evaluation_cost a HL b HB old c Hc) as Heval.
    change (Cost.ticks (Eval.outputs_c S (lookup_c EX L old) c) <=
      TotalCost.Budget.evaluation b) in Heval.
    pose proof (apply_cost (fst (Eval.outputs S c (lookup EX L old))) sums
      (fun x v Hv => output_key c old x v Hc Hv)) as Happly.
    pose proof (TotalCost.output_sizes HB c (lookup EX L old) Hc) as Hsize.
    change (length (fst (Eval.outputs S c (lookup EX L old))) <=
      TotalCost.Budget.outputs b)%nat in Hsize.
    nia.
  - unfold rows, cs, S; nia.
Qed.

(** Declared-output traversal includes invocation ticks, metadata callbacks and list copies. *)
Theorem declarations_cost :
  Cost.ticks (Narrow.outputs_c a) <= N.of_nat rows *
    (3 + SystemIndexCost.Budget.target_ticks (TotalCost.Budget.metadata b) +
      SystemIndexCost.Budget.sides_ticks (TotalCost.Budget.metadata b) +
      N.of_nat (SystemIndexCost.Budget.output_count (TotalCost.Budget.metadata b))).
Proof.
  unfold Narrow.outputs_c.
  eapply N.le_trans with (m := N.of_nat (length cs) *
    (1 + (2 + SystemIndexCost.Budget.target_ticks (TotalCost.Budget.metadata b) +
      SystemIndexCost.Budget.sides_ticks (TotalCost.Budget.metadata b) +
      N.of_nat (SystemIndexCost.Budget.output_count (TotalCost.Budget.metadata b))))).
  - apply right_cost_on.
    intros c rest Hc; rewrite !Cost.ticks_bind, Cost.ticks_step, Cost.ticks_ret, ticks_app_c.
    destruct (SystemIndexCost.callback_budget (TotalCost.metadata_model HB) c Hc)
      as [Ht [_ Hs]].
    destruct (SystemIndexCost.count_budget (TotalCost.metadata_model HB) c Hc) as [_ Hcount].
    change (length (System.target S c :: side_targets SS c) <=
      SystemIndexCost.Budget.output_count (TotalCost.Budget.metadata b))%nat in Hcount.
    cbn [length] in Hcount; unfold S, SS in *.
    fold (side_targets (Analysis.static a) c); nia.
  - unfold rows, cs, S; nia.
Qed.

(** Canonical declared-key preparation keeps insertion and enumeration charges. *)
Theorem distinct_cost :
  Cost.ticks (distinct_c EX (Narrow.outputs a)) <=
    SystemIndexCost.Budget.distinct (TotalCost.Budget.metadata b) outputs.
Proof.
  apply SystemIndexCost.distinct_numeric_cost; [apply Analysis.key_laws, HL|].
  intros x Hx; destruct (declared_key x Hx) as [c [Hc Hkey]].
  exact (SystemIndexCost.key_budget (TotalCost.metadata_model HB) c Hc x Hkey).
Qed.

(** Each selected output retains both lookups, the order guard, narrowing and the map write. *)
Theorem output_cost old sums acc x :
  In x (Narrow.outputs a) ->
  Cost.ticks (Narrow.output_c EX L old sums acc x) <=
    2 + 3 * TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b + narrowing.
Proof.
  intro Hx; pose proof (declared_key x Hx) as Hkey.
  pose proof (TotalCost.lookup_cost a b HB old x Hkey) as Hold.
  pose proof (TotalCost.lookup_cost a b HB sums x Hkey) as Hsum.
  destruct Hkey as [c [Hc Hmeta]].
  destruct (SystemIndexCost.key_budget (TotalCost.metadata_model HB) c Hc x Hmeta) as [He Hw].
  assert (Hwrite : forall value, Cost.ticks (Map.set_c EX x value acc) <= TotalCost.Budget.key b).
  { intro value; rewrite Map.set_cost; fold (key_bits EX x).
    change (Cost.ticks (encode_c EX x) <=
      SystemIndexCost.Budget.encoder_ticks (TotalCost.Budget.metadata b)) in He.
    change (key_bits EX x <=
      SystemIndexCost.Budget.key_digits (TotalCost.Budget.metadata b)) in Hw.
    unfold TotalCost.Budget.key; lia. }
  pose proof (proj1 (TotalCost.lattice_calls HB (lookup EX L sums x) (lookup EX L old x)))
    as Hle.
  unfold Narrow.output_c; rewrite !Cost.ticks_bind, Cost.ticks_step.
  fold (lookup EX L old x) (lookup EX L sums x).
  fold (leb L (lookup EX L sums x) (lookup EX L old x)).
  destruct (leb L (lookup EX L sums x) (lookup EX L old x)) eqn:Hbelow;
    rewrite ?Cost.ticks_bind, ?Cost.ticks_step, ?Cost.ticks_ret;
    pose proof (Hnarrow (lookup EX L old x) (lookup EX L sums x)) as Hn.
  all: match goal with
  | |- context [Cost.ticks (Map.set_c ?e ?key ?value ?dest)] =>
      pose proof (Hwrite value) as Hset
  end.
  all: unfold EX, L in *; nia.
Qed.

(** Primitive duties yield a closed numeric simultaneous-pass bound for every input assignment. *)
Theorem narrow_pass_cost old :
  Cost.ticks (Narrow.pass_c a old) <= pass_budget b narrowing rows outputs.
Proof.
  pose proof declarations_cost as Hdeclared.
  pose proof distinct_cost as Hdistinct.
  pose proof (collect_cost old) as Hcollect.
  assert (Hfold : Cost.ticks (fold_left_c
    (Narrow.output_c EX L old (Cost.value (Narrow.collect_c a old)))
    (distinct EX (Narrow.outputs a)) old) <= N.of_nat outputs *
      (3 + 3 * TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b + narrowing)).
  { pose proof (left_cost_on (Narrow.output_c EX L old (Cost.value (Narrow.collect_c a old)))
      (distinct EX (Narrow.outputs a)) old
      (2 + 3 * TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b + narrowing)
      (fun acc x Hx => output_cost old _ acc x
        (proj1 (distinct_spec EX (Analysis.key_laws HL) _ x) Hx))) as Hcost.
    pose proof (SystemIndexCost.distinct_length EX (Analysis.key_laws HL)
      (Narrow.outputs a)) as Hlength.
    change (length (distinct EX (Narrow.outputs a)) <= outputs)%nat in Hlength.
    assert (HN : N.of_nat (length (distinct EX (Narrow.outputs a))) <= N.of_nat outputs)
      by lia.
    eapply N.le_trans; [exact Hcost|].
    apply N.mul_le_mono; [exact HN|lia]. }
  unfold Narrow.pass_c; rewrite !Cost.ticks_bind.
  change (Cost.ticks (Narrow.outputs_c a) +
    (Cost.ticks (distinct_c EX (Narrow.outputs a)) +
      (Cost.ticks (Narrow.collect_c a old) +
        Cost.ticks (fold_left_c
          (Narrow.output_c EX L old (Cost.value (Narrow.collect_c a old)))
          (distinct EX (Narrow.outputs a)) old))) <= pass_budget b narrowing rows outputs).
  unfold pass_budget; nia.
Qed.

(** Unary policy-count conversion retains one tick per consumed successor. *)
Theorem fuel_cost n : Cost.ticks (Narrow.fuel_c n) = N.of_nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [Narrow.fuel_c]; rewrite !Cost.ticks_bind, Cost.ticks_step, Cost.ticks_map, IH.
  rewrite Nat2N.inj_succ; lia.
Qed.

(** Repeated passes retain numeric policy conversion and the binary countdown driver's descent. *)
Theorem narrow_rounds_cost n old :
  Cost.ticks (Narrow.rounds_c a n old) <=
    N.of_nat n + (pass_budget b narrowing rows outputs + 2) * (N.of_nat n + 1) +
    2 * N.pos (Pos.size (Cost.value (Narrow.fuel_c n))).
Proof.
  set (k := pass_budget b narrowing rows outputs).
  assert (Hstep : forall s, True ->
    Cost.ticks (Narrow.step_c a s) <= k /\
    match Cost.value (Narrow.step_c a s) with
    | inl t => True /\ N.of_nat (fst t) < N.of_nat (fst s)
    | inr _ => True
    end).
  { intros [count m] _; destruct count as [|count]; cbn [Narrow.step_c fst snd].
    - rewrite Cost.ticks_ret, Cost.value_ret; split; [lia|exact I].
    - rewrite Cost.ticks_map, Cost.value_map; split.
      + apply narrow_pass_cost.
      + cbn [fst]; split; [exact I|rewrite Nat2N.inj_succ; lia]. }
  pose proof (iterate_cost (Narrow.step_c a) (fun _ => True)
    (fun s => N.of_nat (fst s)) k (Cost.value (Narrow.fuel_c n)) (n, old) Hstep I) as Hloop.
  cbn beta in Hloop; cbn [fst] in Hloop.
  unfold Narrow.rounds_c; rewrite !Cost.ticks_bind, Cost.ticks_ret, fuel_cost.
  unfold k in Hloop; nia.
Qed.

Local Lemma checked_outputs_cost old outs :
  (forall x v, In (x, v) outs -> TotalCost.key_domain a x) ->
  fold_right (fun xa sum =>
    3 + Cost.ticks (lookup_c EX L old (fst xa)) +
      Cost.ticks (leb_c L (snd xa) (Cost.value (lookup_c EX L old (fst xa)))) + sum)
    0 outs <= N.of_nat (length outs) *
      (3 + TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b).
Proof.
  intro Hkeys; induction outs as [|[x v] outs IH]; cbn [fold_right fst snd length].
  - lia.
  - specialize (IH (fun y w Hw => Hkeys y w (or_intror Hw))).
    pose proof (TotalCost.lookup_cost a b HB old x (Hkeys x v (or_introl eq_refl))) as Hlook.
    pose proof (proj1 (TotalCost.lattice_calls HB v (lookup EX L old x))) as Hle.
    change (Cost.ticks (lookup_c EX L old x) <= TotalCost.Budget.key b) in Hlook.
    change (Cost.ticks (leb_c L v (Cost.value (lookup_c EX L old x))) <=
      TotalCost.Budget.lattice_ticks b) in Hle.
    rewrite Nat2N.inj_succ; nia.
Qed.

(** Full checking is bounded from the same primitive callbacks and selected query paths. *)
Theorem checker_cost old :
  Cost.ticks (check_post_c L S (lookup_c EX L old)) <= N.of_nat rows *
    (1 + TotalCost.Budget.evaluation b +
      N.of_nat (TotalCost.Budget.outputs b) *
        (3 + TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b)).
Proof.
  apply check_post_cost; unfold check_budget.
  assert (Hrow : forall c, In c cs ->
    1 + Cost.ticks (Eval.outputs_c S (lookup_c EX L old) c) +
    fold_right (fun xa sum =>
      3 + Cost.ticks (lookup_c EX L old (fst xa)) +
        Cost.ticks (leb_c L (snd xa) (Cost.value (lookup_c EX L old (fst xa)))) + sum)
      0 (fst (Cost.value (Eval.outputs_c S (lookup_c EX L old) c))) <=
      1 + TotalCost.Budget.evaluation b + N.of_nat (TotalCost.Budget.outputs b) *
        (3 + TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b)).
  { intros c Hc.
    rewrite (Eval.outputs_c_spec S c _ (lookup EX L old)) by reflexivity.
    pose proof (checked_outputs_cost old (fst (Eval.outputs S c (lookup EX L old)))
      (fun x v Hv => output_key c old x v Hc Hv)) as Houts.
    pose proof (TotalCost.evaluation_cost a HL b HB old c Hc) as Heval.
    pose proof (TotalCost.output_sizes HB c (lookup EX L old) Hc) as Hsize.
    change (Cost.ticks (Eval.outputs_c S (lookup_c EX L old) c) <=
      TotalCost.Budget.evaluation b) in Heval.
    change (length (fst (Eval.outputs S c (lookup EX L old))) <=
      TotalCost.Budget.outputs b)%nat in Hsize.
    nia. }
  fold cs; unfold rows; clear Hnarrow.
  induction cs as [|c rest IH]; cbn [fold_right length]; [lia|].
  specialize (IH (fun d Hd => Hrow d (or_intror Hd))).
  specialize (Hrow c (or_introl eq_refl)); rewrite Nat2N.inj_succ; nia.
Qed.

(** Checked narrowing retains candidate and checker work even when the candidate is discarded. *)
Theorem narrow_checked_cost n old :
  Cost.ticks (Narrow.checked_c a n old) <=
    N.of_nat n + (pass_budget b narrowing rows outputs + 2) * (N.of_nat n + 1) +
    2 * N.pos (Pos.size (Cost.value (Narrow.fuel_c n))) +
    N.of_nat rows * (1 + TotalCost.Budget.evaluation b +
      N.of_nat (TotalCost.Budget.outputs b) *
        (3 + TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b)).
Proof.
  pose proof (narrow_rounds_cost n old) as Hrounds.
  pose proof (checker_cost (Cost.value (Narrow.rounds_c a n old))) as Hcheck.
  unfold Narrow.checked_c; rewrite !Cost.ticks_bind.
  destruct (Cost.value (check_post_c (Analysis.lat a) (Analysis.system a)
    (lookup_c (Analysis.key_enc a) (Analysis.lat a)
      (Cost.value (Narrow.rounds_c a n old))))); rewrite Cost.ticks_ret;
    unfold EX, L, S in *; nia.
Qed.

(** Any wrapped solver retains its own cost and adds the proved checked-narrowing budget. *)
Theorem narrow_wrap_cost (sv : Solver.t X C A) fuel :
  Cost.ticks (Solver.run_c (Narrow.wrap sv) a fuel) <=
    1 + Cost.ticks (Solver.run_c sv a fuel) +
    let n := Policy.narrowing (Analysis.policy a) in
    N.of_nat n + (pass_budget b narrowing rows outputs + 2) * (N.of_nat n + 1) +
    2 * N.pos (Pos.size (Cost.value (Narrow.fuel_c n))) +
    N.of_nat rows * (1 + TotalCost.Budget.evaluation b +
      N.of_nat (TotalCost.Budget.outputs b) *
        (3 + TotalCost.Budget.key b + TotalCost.Budget.lattice_ticks b)).
Proof.
  assert (Heq : Cost.ticks (Solver.run_c (Narrow.wrap sv) a fuel) =
    Cost.ticks (Narrow.wrap_run_c sv a fuel)) by reflexivity.
  rewrite Heq, Narrow.wrap_cost.
  destruct (Solver.run sv a fuel) as [old|have|why]; cbn zeta.
  - pose proof (narrow_checked_cost (Policy.narrowing (Analysis.policy a)) old); nia.
  - nia.
  - nia.
Qed.

End Pass.

(** Checked-narrowing families inherit numeric big-O bounds from primitive callback duties. *)
Theorem narrow_bigO {T X C A} (a : T -> Analysis.t X C A)
    (HL : forall t, Analysis.laws (a t)) (b : T -> TotalCost.Budget.t)
    (HB : forall t, TotalCost.model (a t) (b t)) (narrowing : T -> N)
    (HN : forall t x y, Cost.ticks (narrow_c (Analysis.lat (a t)) x y) <= narrowing t)
    (rounds : T -> nat) (old : T -> assignment X A) :
  bigO (fun t =>
    let rows := length (System.constraints (Analysis.system (a t))) in
    let outputs := length (Narrow.outputs (a t)) in
    N.of_nat (rounds t) +
      (pass_budget (b t) (narrowing t) rows outputs + 2) * (N.of_nat (rounds t) + 1) +
      2 * N.pos (Pos.size (Cost.value (Narrow.fuel_c (rounds t)))) +
      N.of_nat rows * (1 + TotalCost.Budget.evaluation (b t) +
        N.of_nat (TotalCost.Budget.outputs (b t)) *
          (3 + TotalCost.Budget.key (b t) + TotalCost.Budget.lattice_ticks (b t))))
    (fun t => Cost.ticks (Narrow.checked_c (a t) (rounds t) (old t))).
Proof.
  exists 1; intro t.
  pose proof (narrow_checked_cost (a t) (HL t) (b t) (HB t) (narrowing t) (HN t)
    (rounds t) (old t)) as Hcost.
  cbn zeta; nia.
Qed.

End NarrowCost.
Import NarrowCost.
