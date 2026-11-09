(** * Accounting for actual binary-iterator traces

    A trace lists the states whose callbacks the existing iterator invokes.
    For example, an immediate stop has one visited state even when the supplied fuel is large.
    Builds on: CostLoop and its public continuation equations. *)

From Stdlib Require Import List NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module SemiNaiveTrace.

(** Traces contain actual callback transitions and allow exhaustion at their final state. *)
Inductive trace {S R} (step : S -> Cost.t (S + R)) : nat -> S -> S + R -> list S -> Prop :=
  | trace_exhausted s : trace step O s (inl s) []
  | trace_stopped n s r :
      Cost.value (step s) = inr r -> trace step (Datatypes.S n) s (inr r) [s]
  | trace_next n s next result visited :
      Cost.value (step s) = inl next ->
      trace step n next result visited -> trace step (Datatypes.S n) s result (s :: visited).

(** Summation retains supplied occurrences and does not deduplicate visited states. *)
Definition sum {A} (price : A -> N) xs := fold_right (fun x n => price x + n) 0 xs.

Lemma sum_app {A} (price : A -> N) xs ys :
  sum price (xs ++ ys) = sum price xs + sum price ys.
Proof.
  unfold sum; induction xs as [|x xs IH]; cbn [fold_right app]; [reflexivity |].
  rewrite IH; lia.
Qed.

Lemma sum_bound {A} (price bound : A -> N) xs :
  (forall x, In x xs -> price x <= bound x) -> sum price xs <= sum bound xs.
Proof.
  unfold sum; induction xs as [|x xs IH]; intro Hbound; cbn [fold_right]; [lia |].
  pose proof (Hbound x (or_introl eq_refl)).
  specialize (IH (fun y Hy => Hbound y (or_intror Hy))); lia.
Qed.

Lemma trace_append {S R} step n s middle xs :
  @trace S R step n s (inl middle) xs ->
  forall m result ys, trace step m middle result ys -> trace step (n + m)%nat s result (xs ++ ys).
Proof.
  intro Htrace; remember (inl middle) as result eqn:Heq.
  induction Htrace as [s | n s r Hstop | n s next result visited Hnext Htrace IH];
    intros m final ys Hfinal.
  - injection Heq as ->; exact Hfinal.
  - discriminate.
  - cbn [app]; apply trace_next with (next := next); [exact Hnext |].
    apply IH; assumption.
Qed.

Lemma trace_extend_stop {S R} step n s r xs :
  @trace S R step n s (inr r) xs ->
  forall m, trace step (n + m)%nat s (inr r) xs.
Proof.
  intro Htrace; remember (inr r) as result eqn:Heq.
  induction Htrace as [s | n s result Hstop | n s next result visited Hnext Htrace IH];
    intro m; [discriminate | |].
  - injection Heq as <-; apply trace_stopped, Hstop.
  - apply trace_next with (next := next); [exact Hnext | apply IH, Heq].
Qed.

(** Fixed callback fuel and deterministic steps give a unique visited-state list. *)
Theorem trace_unique {S R} step n s result xs ys :
  @trace S R step n s result xs -> trace step n s result ys -> xs = ys.
Proof.
  intro Htrace; revert ys.
  induction Htrace as [s | n s r Hstop | n s next result visited Hnext Htrace IH];
    intros ys Hother;
    inversion Hother as [s0 | n0 s0 r0 Hstop0 |
      n0 s0 next0 result0 visited0 Hnext0 Htail0]; subst; try congruence.
  assert (Heq : next = next0) by congruence; subst next0.
  f_equal; apply IH, Htail0.
Qed.

(** A fixed fuel and start state determine both the result and its actual visited-state list. *)
Theorem trace_functional {S R} step n s result xs other ys :
  @trace S R step n s result xs -> trace step n s other ys -> result = other /\ xs = ys.
Proof.
  intro Htrace; revert other ys.
  induction Htrace as [s | n s r Hstop | n s next result visited Hnext Htrace IH];
    intros other ys Hother;
    inversion Hother as [s0 | n0 s0 r0 Hstop0 |
      n0 s0 next0 result0 visited0 Hnext0 Htail0]; subst; try congruence;
    try (split; [congruence | reflexivity]).
  assert (Heq : next = next0) by congruence; subst next0.
  destruct (IH _ _ Htail0) as [Hresult Hvisited]; split; [exact Hresult | congruence].
Qed.

(** Each callback pays two units of binary-driver credit in addition to its actual ticks. *)
Definition charge {S R} (step : S -> Cost.t (S + R)) visited :=
  sum (fun s => Cost.ticks (step s) + 2) visited.

(** Exhausted blocks refund one unit while stopped blocks retain a logarithmic descent allowance. *)
Definition accounted {S R} (step : S -> Cost.t (S + R)) n d s (m : Cost.t (S + R)) :=
  exists visited, trace step n s (Cost.value m) visited /\
    match Cost.value m with
    | inl _ => Cost.ticks m + 1 <= charge step visited
    | inr _ => Cost.ticks m <= charge step visited + d
    end.

Lemma continue_credit {S R} (step : S -> Cost.t (S + R)) n q d s m next :
  accounted step n d s m ->
  (forall middle, accounted step q d middle (next middle)) ->
  exists visited, trace step (n + q)%nat s (Cost.value (continue_c m next)) visited /\
    match Cost.value (continue_c m next) with
    | inl _ => Cost.ticks (continue_c m next) + 2 <= charge step visited
    | inr _ => Cost.ticks (continue_c m next) <= charge step visited + d
    end.
Proof.
  intros [xs [Htrace Hcost]] Hnext.
  rewrite value_continue_c, ticks_continue_c.
  destruct (Cost.value m) as [middle | result].
  - destruct (Hnext middle) as [ys [Htail Htailcost]].
    exists (xs ++ ys); split; [eapply trace_append; eassumption |].
    unfold charge; rewrite sum_app.
    unfold charge in Hcost, Htailcost.
    destruct (Cost.value (next middle)); lia.
  - exists xs; split; [apply trace_extend_stop, Htrace | lia].
Qed.

Lemma continue_accounted {S R} (step : S -> Cost.t (S + R)) n q d s m next :
  accounted step n d s m ->
  (forall middle, accounted step q d middle (next middle)) ->
  accounted step (n + q)%nat d s (continue_c m next).
Proof.
  intros Hfirst Hnext.
  destruct (continue_credit step n q d s m next Hfirst Hnext) as [visited [Htrace Hcost]].
  exists visited; split; [exact Htrace |].
  destruct (Cost.value (continue_c m next)); lia.
Qed.

Lemma tick_continue_accounted {S R} (step : S -> Cost.t (S + R)) n q d s m next :
  accounted step n d s m ->
  (forall middle, accounted step q d middle (next middle)) ->
  accounted step (n + q)%nat (d + 1) s (Cost.step ;; continue_c m next).
Proof.
  intros Hfirst Hnext.
  destruct (continue_credit step n q d s m next Hfirst Hnext) as [visited [Htrace Hcost]].
  exists visited; autorewrite with galois_cost; split; [exact Htrace |].
  destruct (Cost.value (continue_c m next)); lia.
Qed.

Lemma callback_accounted {S R} (step : S -> Cost.t (S + R)) d s :
  accounted step 1%nat d s (Cost.step ;; step s).
Proof.
  exists [s]; autorewrite with galois_cost.
  unfold charge, sum; cbn [fold_right].
  destruct (Cost.value (step s)) as [next | result] eqn:Hstep; split; try lia.
  - apply trace_next with (next := next); [exact Hstep | apply trace_exhausted].
  - apply trace_stopped, Hstep.
Qed.

(** The actual iterator admits a callback trace and a bound charging its binary descent. *)
Theorem iterate_accounted {S R} (step : S -> Cost.t (S + R)) fuel s :
  accounted step (Pos.to_nat fuel) (N.pos (Pos.size fuel)) s (iterate step fuel s).
Proof.
  revert s; induction fuel as [p IH | p IH |]; intro s.
  - cbn [iterate].
    change (N.pos (Pos.size (xI p))) with (N.succ (N.pos (Pos.size p))).
    replace (N.succ (N.pos (Pos.size p))) with (N.pos (Pos.size p) + 1) by lia.
    rewrite Pos2Nat.inj_xI.
    replace (Datatypes.S (2 * Pos.to_nat p)) with
      (1 + (Pos.to_nat p + Pos.to_nat p))%nat by lia.
    change (accounted step (1 + (Pos.to_nat p + Pos.to_nat p))%nat
      (N.pos (Pos.size p) + 1) s
      (Cost.step ;; continue_c (Cost.step ;; step s)
        (fun middle => continue_c (iterate step p middle) (iterate step p)))).
    apply tick_continue_accounted; [apply callback_accounted |].
    intro middle; apply continue_accounted; apply IH.
  - cbn [iterate].
    change (N.pos (Pos.size (xO p))) with (N.succ (N.pos (Pos.size p))).
    replace (N.succ (N.pos (Pos.size p))) with (N.pos (Pos.size p) + 1) by lia.
    rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by lia.
    change (accounted step (Pos.to_nat p + Pos.to_nat p)%nat (N.pos (Pos.size p) + 1) s
      (Cost.step ;; continue_c (iterate step p s) (iterate step p))).
    apply tick_continue_accounted; apply IH.
  - apply callback_accounted.
Qed.

(** A primitive callback bound sums over the same actual trace for either iterator outcome. *)
Theorem iterate_cost_trace {S R} (step : S -> Cost.t (S + R)) fuel s :
  exists visited, trace step (Pos.to_nat fuel) s (Cost.value (iterate step fuel s)) visited /\
    forall price, (forall state, In state visited -> Cost.ticks (step state) <= price state) ->
      Cost.ticks (iterate step fuel s) <=
        sum (fun state => price state + 2) visited + N.pos (Pos.size fuel).
Proof.
  destruct (iterate_accounted step fuel s) as [visited [Htrace Hcost]].
  exists visited; split; [exact Htrace |]; intros price Hprice.
  assert (Hsum : charge step visited <= sum (fun state => price state + 2) visited).
  { clear Htrace Hcost; unfold charge, sum; revert Hprice.
    induction visited as [|state rest IH]; intro Hprice; cbn [fold_right]; [lia |].
    pose proof (Hprice state (or_introl eq_refl)).
    specialize (IH (fun x Hx => Hprice x (or_intror Hx))); lia. }
  destruct (Cost.value (iterate step fuel s)); lia.
Qed.

End SemiNaiveTrace.
Import SemiNaiveTrace.
