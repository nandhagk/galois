(** * Whole fast-program numerical and family bounds

    The bound composes primitive stratification, actual stratum traces and reached storage passes.
    For example, an exhausted stratum pays no target-copy pass and higher levels only propagate it.
    Builds on: DatalogEngineValueCost and the actual fast wrapper. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogSolve
  DatalogEngine DatalogEngineProof DatalogSemiNaive DatalogSemiNaiveBudget DatalogSemiNaiveCost
  DatalogSemiNaiveReady DatalogSemiNaiveInitialCost DatalogSemiNaiveRunCost DatalogSemiNaiveTrace
  DatalogEngineSetupCost DatalogEngineValueCost.
Import List.ListNotations SemiNaive SemiNaiveBudget SemiNaiveCost SemiNaiveInitialCost
  SemiNaiveReady SemiNaiveRunCost SemiNaiveTrace EngineSetupCost EngineValueCost.
Local Open Scope N_scope.

Module EngineCost.

(** Summing level prices retains every supplied level occurrence without running another solver. *)
Fixpoint sum_levels (price : nat -> N) n :=
  match n with
  | O => 0
  | S k => sum_levels price k + price k
  end.

(** Each actual solved prefix supplies only value and primitive-key duties for its next stratum. *)
Definition level_data {P} (prog : program P) facts st fuel b
    (visited : nat -> list (state P)) : Prop :=
  forall k, (k < count st)%nat ->
    match solve_levels_fast prog facts st fuel k with
    | Outcome.Solved db =>
      trace (step_c prog st (rel_of_c prog db) k) (Pos.to_nat fuel)
        (initial prog facts st (rel_of_c prog db) k)
        (run prog st (rel_of_c prog db) k fuel (initial prog facts st (rel_of_c prog db) k))
        (visited k) /\
      initial_values prog facts st (rel_of_c prog db) k b /\
      forall s, In s (visited k) -> round_values prog st (rel_of_c prog db) k b s
    | _ => True
    end.

(** Reached level prices include complete stratum work and every target storage occurrence. *)
Definition level_charge {P} (prog : program P) facts st fuel b visited k :=
  match solve_levels_fast prog facts st fuel k with
  | Outcome.Solved db =>
    stratum_charge prog facts st (rel_of_c prog db) k fuel b (visited k) +
    match stratum prog facts st (rel_of_c prog db) k fuel with
    | Outcome.Solved local =>
      (N.of_nat (length (rules prog)) + N.of_nat (length facts)) * (4 + level_bound b) +
      N.of_nat (length (stratum_targets prog facts st k)) *
        (4 + 2 * (predicate_encode b + predicate_width b))
    | _ => 0
    end
  | _ => 0
  end.

(** Every level visit pays propagation overhead even when a previous stratum exhausted its fuel. *)
Definition levels_charge {P} (prog : program P) facts st fuel b visited n :=
  N.of_nat n + sum_levels (level_charge prog facts st fuel b visited) n.

Lemma levels_cost_equation {P} (prog : program P) facts st fuel k :
  Cost.ticks (solve_levels_fast_c prog facts st fuel (S k)) =
  1 + Cost.ticks (solve_levels_fast_c prog facts st fuel k) +
  match solve_levels_fast prog facts st fuel k with
  | Outcome.Solved db =>
    Cost.ticks (stratum_c prog facts st (rel_of_c prog db) k fuel) +
    match stratum prog facts st (rel_of_c prog db) k fuel with
    | Outcome.Solved local =>
      Cost.ticks (stratum_targets_c prog facts st k) +
      Cost.ticks (store_relations_c prog (stratum_targets prog facts st k)
        (rel_of_c prog local) db)
    | _ => 0
    end
  | _ => 0
  end.
Proof.
  cbn [solve_levels_fast_c]; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step.
  fold (@solve_levels_fast P prog facts st fuel k).
  destruct (solve_levels_fast prog facts st fuel k) as [db | have | why];
    rewrite ?Cost.ticks_ret; try lia.
  rewrite Cost.ticks_bind; fold (@stratum P prog facts st (rel_of_c prog db) k fuel).
  destruct (stratum prog facts st (rel_of_c prog db) k fuel);
    rewrite ?Cost.ticks_ret; try lia.
  rewrite Cost.ticks_bind, Cost.ticks_map.
  fold (@stratum_targets P prog facts st k); lia.
Qed.

(** Complete level folding derives lower and level callback prices from primitive predicate keys. *)
Theorem levels_cost {P} (prog : program P) facts st fuel b visited n :
  encoding_laws (penc prog) -> stratify prog = Some st ->
  predicate_keys prog facts (predicate_encode b) (predicate_width b) ->
  1 + predicate_encode b + predicate_width b <= level_bound b ->
  1 + predicate_encode b + predicate_width b <= lower_bound b ->
  level_data prog facts st fuel b visited -> (n <= count st)%nat ->
  Cost.ticks (solve_levels_fast_c prog facts st fuel n) <=
    levels_charge prog facts st fuel b visited n.
Proof.
  intros HE Hst Hkeys Hl Hlower Hdata.
  induction n as [|k IH]; intro Hn; [change (0 <= 0); lia |].
  rewrite levels_cost_equation.
  specialize (IH ltac:(lia)); specialize (Hdata k ltac:(lia)).
  unfold levels_charge at 1; cbn [sum_levels]; rewrite Nat2N.inj_succ.
  unfold level_charge at 2.
  destruct (solve_levels_fast prog facts st fuel k) as [db | have | why] eqn:Hprevious.
  - destruct Hdata as [Htrace [Hinitial Hrounds]].
    pose proof (wrapper_callbacks prog facts st db b Hst Hkeys Hl Hlower) as Hcallbacks.
    assert (Hround : forall s, In s (visited k) ->
      round_data prog st (rel_of_c prog db) k b s).
    { intros s Hs; apply (round_lift prog facts st (rel_of_c prog db) k b s);
        [|exact Hcallbacks |exact Hkeys |apply Hrounds, Hs].
      exact (trace_ready prog HE st (rel_of_c prog db) k _ _ _ _ Htrace
        (initial_ready prog HE facts st (rel_of_c prog db) k) s Hs). }
    pose proof (semi_naive_cost prog facts st (rel_of_c prog db) k fuel b (visited k)
      HE Htrace (initial_lift prog facts st (rel_of_c prog db) k b Hcallbacks Hkeys Hinitial)
      Hround) as Hstratum.
    destruct (stratum prog facts st (rel_of_c prog db) k fuel) as [local | have | why].
    + pose proof (targets_cost prog facts st k (level_bound b)
        (fun p Hp => proj1 (Hcallbacks p Hp))) as Htargets.
      pose proof (store_cost prog (stratum_targets prog facts st k) local db
        (predicate_encode b) (predicate_width b)
        (fun p Hp => Hkeys p (target_support prog facts st k p Hp))) as Hstore.
      unfold levels_charge in IH; lia.
    + unfold levels_charge in IH; lia.
    + unfold levels_charge in IH; lia.
  - unfold levels_charge in IH; lia.
  - unfold levels_charge in IH; lia.
Qed.

(** The whole-program domain includes primitive stratification and all reached level prices. *)
Definition program_charge {P} (prog : program P) facts fuel b visited :=
  stratifier_charge prog (predicate_encode b) (predicate_width b) +
  match stratify prog with
  | None => 0
  | Some st => levels_charge prog facts st fuel b visited (count st)
  end.

(** Whole fast-program cost uses value-only duties and primitive keys for every actual outcome. *)
Theorem solve_program_fast_cost {P} (prog : program P) facts fuel b visited :
  encoding_laws (penc prog) ->
  predicate_keys prog facts (predicate_encode b) (predicate_width b) ->
  1 + predicate_encode b + predicate_width b <= level_bound b ->
  1 + predicate_encode b + predicate_width b <= lower_bound b ->
  (match stratify prog with
   | None => True
   | Some st => level_data prog facts st fuel b visited
   end) ->
  Cost.ticks (solve_program_fast_c prog facts fuel) <= program_charge prog facts fuel b visited.
Proof.
  intros HE Hkeys Hl Hlower Hdata.
  pose proof (stratifier_cost prog (predicate_encode b) (predicate_width b)
    (fun p Hp => Hkeys p (proj2 (in_app_iff _ _ _) (or_introl Hp)))) as Hstratifier.
  unfold solve_program_fast_c; rewrite Cost.ticks_bind; fold (@stratify P prog).
  unfold program_charge; destruct (stratify prog) as [st |] eqn:Hst.
  - apply N.add_le_mono; [exact Hstratifier |].
    apply levels_cost; [exact HE | exact Hst | exact Hkeys | exact Hl | exact Hlower |
      exact Hdata | lia].
  - rewrite Cost.ticks_ret; lia.
Qed.

(** Programs, source inventories, fuel, primitive budgets and actual traces may vary together. *)
Theorem solve_program_fast_bigO {X P} (prog : X -> program P) facts fuel b visited :
  (forall x, encoding_laws (penc (prog x))) ->
  (forall x, predicate_keys (prog x) (facts x) (predicate_encode (b x)) (predicate_width (b x))) ->
  (forall x, 1 + predicate_encode (b x) + predicate_width (b x) <= level_bound (b x)) ->
  (forall x, 1 + predicate_encode (b x) + predicate_width (b x) <= lower_bound (b x)) ->
  (forall x, match stratify (prog x) with
   | None => True
   | Some st => level_data (prog x) (facts x) st (fuel x) (b x) (visited x)
   end) ->
  bigO (fun x => program_charge (prog x) (facts x) (fuel x) (b x) (visited x))
    (fun x => Cost.ticks (solve_program_fast_c (prog x) (facts x) (fuel x))).
Proof.
  intros HE Hkeys Hl Hlower Hdata; exists 1; intro x.
  pose proof (solve_program_fast_cost (prog x) (facts x) (fuel x) (b x) (visited x)
    (HE x) (Hkeys x) (Hl x) (Hlower x) (Hdata x)); nia.
Qed.

End EngineCost.
Import EngineCost.
