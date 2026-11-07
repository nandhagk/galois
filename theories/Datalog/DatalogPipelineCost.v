(** * Reference pipeline cost equations

    The equations expose the complete callback costs retained by stratification and solving.
    For example, successful stratum solving includes certification and the second reference run.
    Builds on: DatalogSolve and CostList. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseMap.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogCompile
  DatalogSolve.
From Galois.Fixpoint Require Import FixpointAnalysis FixpointAnalyze FixpointSolver FixpointKleene.
Import Cost.Notations.
Local Open Scope N_scope.

(** Only successful certification charges the second callback invocation and its complete work. *)
Theorem finish_stratum_cost {P R} (a : Analysis.t P (Constraint.t P) relation)
    fuel (certified : Outcome.t P relation R) :
  Cost.ticks (finish_stratum_c a fuel certified) =
    match certified with
    | Outcome.Solved _ => 1 + Cost.ticks (Solver.run_c Kleene.solver a fuel)
    | _ => 0
    end.
Proof.
  destruct certified; [|reflexivity |reflexivity].
  unfold finish_stratum_c; rewrite Cost.ticks_bind, Cost.ticks_step; reflexivity.
Qed.

(** Each stratum solve retains preparation, full analysis and the selected second invocation. *)
Theorem solve_stratum_cost {P} (prog : program P) facts st lower k fuel :
  Cost.ticks (solve_stratum_c prog facts st lower k fuel) =
    Cost.ticks (DatalogCompile.stratum_analysis_c prog facts st lower k) +
    Cost.ticks (analyze_c (DatalogCompile.stratum_analysis prog facts st lower k) fuel) +
    match analyze (DatalogCompile.stratum_analysis prog facts st lower k) fuel with
    | Outcome.Solved _ => 1 + Cost.ticks (Solver.run_c Kleene.solver
        (DatalogCompile.stratum_analysis prog facts st lower k) fuel)
    | _ => 0
    end.
Proof.
  unfold solve_stratum_c; repeat rewrite Cost.ticks_bind.
  rewrite finish_stratum_cost.
  fold (DatalogCompile.stratum_analysis prog facts st lower k).
  fold (analyze (DatalogCompile.stratum_analysis prog facts st lower k) fuel).
  destruct (analyze (DatalogCompile.stratum_analysis prog facts st lower k) fuel);
    rewrite ?Cost.ticks_ret; lia.
Qed.

(** A solved level charges all target preparation and all costed database copies. *)
Theorem solve_levels_cost {P} (prog : program P) facts st fuel n :
  Cost.ticks (solve_levels_c prog facts st fuel n) =
  match n with
  | O => 0
  | S k =>
    1 + Cost.ticks (solve_levels_c prog facts st fuel k) +
    match solve_levels prog facts st fuel k with
    | Outcome.Solved db =>
      Cost.ticks (solve_stratum_c prog facts st (rel_of_c prog db) k fuel) +
      match solve_stratum prog facts st (rel_of_c prog db) k fuel with
      | Outcome.Solved m =>
        Cost.ticks (stratum_targets_c prog facts st k) +
        Cost.ticks (store_relations_c prog (stratum_targets prog facts st k)
          (rel_of_c prog m) db)
      | _ => 0
      end
    | _ => 0
    end
  end.
Proof.
  destruct n as [|k]; [reflexivity |].
  cbn [solve_levels_c]; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step.
  fold (@solve_levels P prog facts st fuel k).
  destruct (solve_levels prog facts st fuel k) as [db | have | why];
    rewrite ?Cost.ticks_ret; try lia.
  rewrite Cost.ticks_bind; fold (@solve_stratum P prog facts st (rel_of_c prog db) k fuel).
  destruct (solve_stratum prog facts st (rel_of_c prog db) k fuel);
    rewrite ?Cost.ticks_ret; try lia.
  rewrite Cost.ticks_bind, Cost.ticks_map; fold (@stratum_targets P prog facts st k); lia.
Qed.

(** Program solving retains the entire stratifier charge before selecting a level fold. *)
Theorem solve_program_cost {P} (prog : program P) facts fuel :
  Cost.ticks (solve_program_c prog facts fuel) =
    Cost.ticks (stratify_c prog) +
    match stratify prog with
    | Some st => Cost.ticks (solve_levels_c prog facts st fuel (count st))
    | None => 0
    end.
Proof.
  unfold solve_program_c; rewrite Cost.ticks_bind; fold (@stratify P prog).
  destruct (stratify prog); reflexivity.
Qed.

(** A stratification pass includes the level checker, edge preparation and all map updates. *)
Theorem stratify_loop_cost {P} (prog : program P) n m :
  Cost.ticks (stratify_loop_c prog n m) =
  match n with
  | O => 0
  | S n' =>
    1 + Cost.ticks (levels_ok_c prog m) +
    if levels_ok prog m then 0 else
      Cost.ticks (program_edges_c prog) +
      Cost.ticks (raise_pass_c (penc prog) (program_edges prog) m) +
      Cost.ticks (stratify_loop_c prog n'
        (raise_pass (penc prog) (program_edges prog) m))
  end.
Proof.
  destruct n as [|n]; [reflexivity |].
  cbn [stratify_loop_c]; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step.
  fold (levels_ok prog m); destruct (levels_ok prog m).
  - rewrite Cost.ticks_ret; lia.
  - repeat rewrite Cost.ticks_bind.
    fold (program_edges prog).
    fold (raise_pass (penc prog) (program_edges prog) m); lia.
Qed.

(** The finite budget includes preparation, every reference pass and the selected final maximum. *)
Theorem stratify_cost {P} (prog : program P) :
  Cost.ticks (stratify_c prog) =
    Cost.ticks (rule_nodes_c prog) + N.of_nat (length (rule_nodes prog)) + 1 +
    Cost.ticks (stratify_loop_c prog
      (length (rule_nodes prog) * length (rule_nodes prog) + 1)%nat Map.empty) +
    let '(m, done) := stratify_loop prog
      (length (rule_nodes prog) * length (rule_nodes prog) + 1)%nat Map.empty in
    if done then Cost.ticks (maximum_c prog m) else 0.
Proof.
  unfold stratify_c; repeat rewrite Cost.ticks_bind.
  rewrite ticks_length_c, value_length_c, Cost.ticks_step.
  fold (rule_nodes prog).
  fold (stratify_loop prog
    (length (rule_nodes prog) * length (rule_nodes prog) + 1)%nat Map.empty).
  destruct (stratify_loop prog _ Map.empty) as [m []].
  - rewrite Cost.ticks_bind, Cost.ticks_ret; lia.
  - rewrite Cost.ticks_ret; lia.
Qed.

(** A uniform local stratum budget bounds the level fold linearly in completed level count. *)
Theorem solve_levels_cost_le {P} (prog : program P) facts st fuel n w :
  (forall k, (k < n)%nat ->
    match solve_levels prog facts st fuel k with
    | Outcome.Solved db =>
      Cost.ticks (solve_stratum_c prog facts st (rel_of_c prog db) k fuel) +
      match solve_stratum prog facts st (rel_of_c prog db) k fuel with
      | Outcome.Solved m =>
        Cost.ticks (stratum_targets_c prog facts st k) +
        Cost.ticks (store_relations_c prog (stratum_targets prog facts st k)
          (rel_of_c prog m) db)
      | _ => 0
      end <= w
    | _ => True
    end) ->
  Cost.ticks (solve_levels_c prog facts st fuel n) <= N.of_nat n * (w + 1).
Proof.
  induction n as [|n IH]; intro Hbudget; [reflexivity |].
  rewrite solve_levels_cost, Nat2N.inj_succ.
  assert (Htail : Cost.ticks (solve_levels_c prog facts st fuel n) <= N.of_nat n * (w + 1)).
  { apply IH; intros k Hk; apply Hbudget; lia. }
  specialize (Hbudget n ltac:(lia)).
  destruct (solve_levels prog facts st fuel n); nia.
Qed.
