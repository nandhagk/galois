(** * Complete cost composition for the actual stratum iterator

    Setup and primitive round prices sum over the states visited by the existing binary iterator.
    For example, exhaustion charges the rounds already performed without assuming a solved result.
    Builds on: DatalogSemiNaiveInitialCost, DatalogSemiNaiveReady and iterator trace accounting. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseTrieCost.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation
  DatalogSemiNaive DatalogSemiNaiveIndex DatalogSemiNaiveReady DatalogSemiNaiveBudget
  DatalogSemiNaiveCost DatalogSemiNaiveCandidateCost DatalogSemiNaiveInitialCost
  DatalogSemiNaiveTrace DatalogSemiNaiveFinite.
Import List.ListNotations SemiNaive SemiNaiveIndex SemiNaiveReady SemiNaiveBudget
  SemiNaiveCost SemiNaiveCandidateCost SemiNaiveInitialCost SemiNaiveTrace.
Local Open Scope N_scope.

Module SemiNaiveRunCost.

(** Round duties are independent primitive data bounds on actual emitted and inserted rows. *)
Definition round_data {P} (prog : program P) st lower k b s :=
  candidate_data prog st lower k s b /\
  (FinSet.is_empty (fresh prog st lower k s) = false ->
  (forall f, FinSet.mem (ground_encoding prog) f (fresh prog st lower k s) = true ->
    key_budget (penc prog) (predicate_encode b) (predicate_width b) (fst f) /\
    key_budget tuple_encoding (tuple_encode b) (tuple_width b) (snd f)) /\
  forall j, In j (jobs s) ->
    maintenance_data prog
      (add_atoms prog (FinSet.elements (fresh prog st lower k s)) Map.empty)
      (plan j) (args_bound b) (rows_bound b)
      (predicate_encode b) (predicate_width b) (tuple_encode b) (tuple_width b)).

(** The round price includes all candidate work and only a reached advancement pass. *)
Definition round_charge {P} (prog : program P) st lower k b s :=
  candidates_charge prog st lower k s b +
  TrieCost.trie_k *
    (1 + N.of_nat (FinSet.size (candidates prog st lower k s)) * ground_width b) +
  if FinSet.is_empty (fresh prog st lower k s) then 0 else
    advance_charge s (fresh prog st lower k s) (args_bound b) (rows_bound b)
      (predicate_encode b) (predicate_width b) (tuple_encode b) (tuple_width b) (ground_width b).

Lemma round_cost {P} (prog : program P) st lower k b s :
  encoding_laws (penc prog) -> ready prog st lower k s ->
  round_data prog st lower k b s ->
  Cost.ticks (step_c prog st lower k s) <= round_charge prog st lower k b s.
Proof.
  intros HE Hready [Hcandidates Hadvance].
  pose proof (candidates_cost prog st lower k s b Hcandidates) as Hgenerate.
  pose proof (new_difference_cost prog st lower k s (ground_width b)
    (candidates_width prog st lower k s b HE Hcandidates)) as Hnew.
  unfold step_c; repeat rewrite Cost.ticks_bind.
  fold (@fresh P prog st lower k s).
  assert (Hempty : Cost.ticks (FinSet.is_empty_c (fresh prog st lower k s)) = 0).
  { reflexivity. }
  rewrite Hempty; fold (FinSet.is_empty (fresh prog st lower k s)).
  unfold round_charge; destruct (FinSet.is_empty (fresh prog st lower k s)) eqn:Hstop.
  - rewrite Cost.ticks_ret; lia.
  - destruct (Hadvance eq_refl) as [Hkeys Hmaintenance].
    assert (Hbatchkeys : forall f,
      FinSet.mem (ground_encoding prog) f (fresh prog st lower k s) = true ->
      key_bits (ground_encoding prog) f <= ground_width b /\
      key_budget (penc prog) (predicate_encode b) (predicate_width b) (fst f) /\
      key_budget tuple_encoding (tuple_encode b) (tuple_width b) (snd f)).
    { intros f Hf; split; [|apply Hkeys, Hf].
      apply (fresh_members prog st lower k s f Hready) in Hf.
      exact (candidates_width prog st lower k s b HE Hcandidates f (proj1 Hf)). }
    pose proof (advance_cost prog s (fresh prog st lower k s) (args_bound b) (rows_bound b)
      (predicate_encode b) (predicate_width b) (tuple_encode b) (tuple_width b) (ground_width b)
      HE (fresh_wf prog st lower k s (accumulated_wf _ _ _ _ _ Hready))
      Hbatchkeys Hmaintenance) as Hmaintenancecost.
    rewrite Cost.ticks_map; lia.
Qed.

Lemma trace_ready {P} (prog : program P) (HE : encoding_laws (penc prog)) st lower k
    n start result visited :
  trace (step_c prog st lower k) n start result visited -> ready prog st lower k start ->
  forall s, In s visited -> ready prog st lower k s.
Proof.
  intro Htrace; induction Htrace as [start | n start result Hstop |
    n start next result visited Hnext Htrace IH]; intros Hready s Hs.
  - contradiction.
  - destruct Hs as [<- | Hbad]; [exact Hready | contradiction].
  - destruct Hs as [<- | Hs]; [exact Hready |].
    apply IH; [exact (step_ready prog HE st lower k start next Hready Hnext) | exact Hs].
Qed.

(** Actual callback count is at most final accumulated cardinality plus the stationary probe. *)
Theorem trace_rounds {P} (prog : program P) (HE : encoding_laws (penc prog)) st lower k
    n start result visited :
  trace (step_c prog st lower k) n start result visited -> ready prog st lower k start ->
  (length visited + FinSet.size (accumulated start) <=
    S (FinSet.size (accumulated
      (match result with inl s => s | inr s => s end))))%nat.
Proof.
  intro Htrace; induction Htrace as [start | n start result Hstop |
    n start next result visited Hnext Htrace IH]; intro Hready.
  - cbn [length]; lia.
  - change (step prog st lower k start = inr result) in Hstop.
    rewrite step_equation in Hstop; destruct (FinSet.is_empty (fresh prog st lower k start));
      [injection Hstop as <-; cbn [length]; lia | discriminate].
  - pose proof (step_ready prog HE st lower k start next Hready Hnext) as Hnextready.
    pose proof (SemiNaiveFinite.step_growth prog HE st lower k start next Hready Hnext) as Hgrow.
    specialize (IH Hnextready); cbn [length]; lia.
Qed.

(** The domain retains setup, primitive callback prices, inventories and binary fuel descent. *)
Definition stratum_charge {P} (prog : program P) facts st lower k fuel b visited :=
  initial_charge prog facts st lower k b +
  sum (fun s => round_charge prog st lower k b s + 2) visited + N.pos (Pos.size fuel).

(** Every fuel has an actual trace without any semantic or primitive-cost premise. *)
Theorem stratum_trace {P} (prog : program P) facts st lower k fuel :
  exists visited, trace (step_c prog st lower k) (Pos.to_nat fuel)
    (initial prog facts st lower k) (run prog st lower k fuel (initial prog facts st lower k))
    visited.
Proof.
  destruct (iterate_accounted (step_c prog st lower k) fuel
    (initial prog facts st lower k)) as [visited [Htrace _]].
  exists visited; exact Htrace.
Qed.

(** The complete stratum cost follows from primitive duties on the same actual iterator trace. *)
Theorem semi_naive_cost {P} (prog : program P) facts st lower k fuel b visited :
  encoding_laws (penc prog) ->
  trace (step_c prog st lower k) (Pos.to_nat fuel)
    (initial prog facts st lower k) (run prog st lower k fuel (initial prog facts st lower k))
    visited ->
  initial_data prog facts st lower k b ->
  (forall s, In s visited -> round_data prog st lower k b s) ->
  Cost.ticks (stratum_c prog facts st lower k fuel) <=
    stratum_charge prog facts st lower k fuel b visited.
Proof.
  intros HE Htrace Hinitial Hrounds.
  pose proof (initial_cost prog facts st lower k b HE Hinitial) as Hsetup.
  destruct (iterate_cost_trace (step_c prog st lower k) fuel
    (initial prog facts st lower k)) as [actual [Hactual Hprice]].
  pose proof (trace_unique _ _ _ _ _ _ Hactual Htrace) as ->.
  specialize (Hprice (round_charge prog st lower k b)).
  assert (Hcallbacks : forall s, In s visited ->
    Cost.ticks (step_c prog st lower k s) <= round_charge prog st lower k b s).
  { intros s Hs; apply round_cost; [exact HE | |apply Hrounds, Hs].
    exact (trace_ready prog HE st lower k _ _ _ _ Htrace
      (initial_ready prog HE facts st lower k) s Hs). }
  specialize (Hprice Hcallbacks).
  fold (@run_c P prog st lower k fuel (initial prog facts st lower k)) in Hprice.
  unfold stratum_c; repeat rewrite Cost.ticks_bind.
  fold (@initial P prog facts st lower k).
  fold (@run P prog st lower k fuel (initial prog facts st lower k)).
  destruct (run prog st lower k fuel (initial prog facts st lower k));
    rewrite Cost.ticks_ret; unfold stratum_charge; lia.
Qed.

(** Programs, primitive budgets, fuel and actual traces may vary throughout the stratum family. *)
Theorem semi_naive_bigO {X P} (prog : X -> program P) facts st lower k fuel b visited :
  (forall x, encoding_laws (penc (prog x))) ->
  (forall x, trace (step_c (prog x) (st x) (lower x) (k x)) (Pos.to_nat (fuel x))
    (initial (prog x) (facts x) (st x) (lower x) (k x))
    (run (prog x) (st x) (lower x) (k x) (fuel x)
      (initial (prog x) (facts x) (st x) (lower x) (k x))) (visited x)) ->
  (forall x, initial_data (prog x) (facts x) (st x) (lower x) (k x) (b x)) ->
  (forall x s, In s (visited x) -> round_data (prog x) (st x) (lower x) (k x) (b x) s) ->
  bigO (fun x => stratum_charge (prog x) (facts x) (st x) (lower x) (k x)
    (fuel x) (b x) (visited x))
    (fun x => Cost.ticks (stratum_c (prog x) (facts x) (st x) (lower x) (k x) (fuel x))).
Proof.
  intros HE Htrace Hinitial Hrounds; exists 1; intro x.
  pose proof (semi_naive_cost (prog x) (facts x) (st x) (lower x) (k x)
    (fuel x) (b x) (visited x) (HE x) (Htrace x) (Hinitial x) (Hrounds x)); nia.
Qed.

End SemiNaiveRunCost.
Import SemiNaiveRunCost.
