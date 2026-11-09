(** * Nonempty importing clients of complete engine costs

    The clients discharge primitive data duties for actual prepared, advanced and stopped states.
    For example, a ground recursive pivot emits a new predicate fact before its next round stops.
    Builds on: DatalogEngineCost and the source engine's public cost domains. *)

From Stdlib Require Import List Bool PeanoNat NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogSolve DatalogJoin DatalogJoinCost DatalogJoinFireCost DatalogJoinPrepareCost
  DatalogSemiNaive DatalogSemiNaiveIndex DatalogSemiNaiveReady DatalogSemiNaiveBudget
  DatalogSemiNaiveTrace DatalogSemiNaiveCost
  DatalogSemiNaiveInitialCost DatalogSemiNaiveRunCost DatalogEngine DatalogEngineProof
  DatalogEngineValueCost DatalogEngineCost.
Import List.ListNotations SemiNaive SemiNaiveIndex SemiNaiveReady SemiNaiveBudget
  SemiNaiveTrace SemiNaiveCost
  SemiNaiveInitialCost SemiNaiveRunCost EngineValueCost EngineCost.
Local Open Scope nat_scope.

Definition cost_rule : rule bool :=
  Rule (Atom true [TConst 2%positive]) [LPos (Atom false [TConst 2%positive])].
Definition cost_program : program bool := Program bool_encoding (fun _ => Cost.ret 1) [cost_rule].
Definition cost_facts : list (ground_atom bool) := [(false, [2%positive])].
Definition cost_strata :=
  match stratify cost_program with
  | Some st => st
  | None => Stratification (fun _ => Cost.ret 0) 1
  end.
Definition cost_lower := rel_of_c cost_program Map.empty.
Definition cost_budget := Budget 1 0 0 1 2 401 401 200 200 200 200 1000 1000.
Definition cost_start := initial cost_program cost_facts cost_strata cost_lower 0.
Definition cost_after := advance cost_program cost_start
  (fresh cost_program cost_strata cost_lower 0 cost_start).
Definition cost_visited (_ : nat) := [cost_start; cost_after].

Lemma cost_keys p : key_budget (penc cost_program) 200 200 p.
Proof.
  destruct p; split; vm_compute; discriminate.
Qed.

Lemma cost_start_rows row :
  member row (tagged cost_program cost_strata 0 cost_lower
    (accumulated_index cost_start) (frontier_index cost_start) (false, true)) = true ->
  row = [2%positive].
Proof.
  intro Hrow; apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws _ _
    (proj2_sig (tagged cost_program cost_strata 0 cost_lower
      (accumulated_index cost_start) (frontier_index cost_start) (false, true)))) in Hrow.
  change (In row [[2%positive]]) in Hrow.
  destruct Hrow as [Heq | Hbad]; [congruence | contradiction].
Qed.

Lemma cost_initial_values :
  initial_values cost_program cost_facts cost_strata cost_lower 0 cost_budget.
Proof.
  split.
  - intros r Hbad; change (In r []) in Hbad; contradiction.
  - split.
    + intros f Hf; change (In f [(false, [2%positive])]) in Hf.
      destruct Hf as [<- | Hbad]; [|contradiction].
      repeat split; vm_compute; discriminate.
    + intros spec Hspec; change (In spec [(cost_rule, 0)]) in Hspec.
      destruct Hspec as [<- | Hbad]; [|contradiction].
      split; [reflexivity | split; [reflexivity |]].
      split; [reflexivity | split; [vm_compute; discriminate | split]].
      * intros row Hrow; apply cost_start_rows in Hrow; subst row; vm_compute; discriminate.
      * split; [|exact I].
        intros row key Hrow Hselect; apply cost_start_rows in Hrow; subst row.
        vm_compute in Hselect; injection Hselect as <-; split; vm_compute; discriminate.
Qed.

Definition cost_job0 :=
  Cost.value (prepare_job_c cost_program
    (tagged_c cost_program cost_strata 0 cost_lower
      (accumulated_index cost_start) (frontier_index cost_start)) (cost_rule, 0)).
Definition cost_job1 :=
  Cost.value (update_job_c cost_program (frontier_index cost_after) cost_job0).

Lemma cost_fire0 :
  firing_data (tagged_rule cost_job0)
    (tagged_c cost_program cost_strata 0 cost_lower
      (accumulated_index cost_start) (frontier_index cost_start)) (plan cost_job0) cost_budget.
Proof.
  split.
  - split.
    + split; [reflexivity | split; [reflexivity |]].
      intros binding Hin; change (In binding [[]]) in Hin.
      destruct Hin as [<- | Hbad]; [|contradiction].
      split; [reflexivity | split; [vm_compute; discriminate | split]].
      * vm_compute; discriminate.
      * intros row c Hrow Hc; change (In row [[2%positive]]) in Hrow.
        destruct Hrow as [<- | Hbad]; [|contradiction].
        destruct Hc as [<- | Hbad]; [vm_compute; discriminate | contradiction].
    + exact I.
  - split; [reflexivity |].
    intros binding Hin; change (In binding [[]]) in Hin.
    destruct Hin as [<- | Hbad]; [|contradiction].
    split; [reflexivity | split].
    + intros atom Hbad; change (In (LNeg atom) [LPos (Atom (false, true)
        [TConst 2%positive])]) in Hbad.
      destruct Hbad as [Hbad | Hbad]; [discriminate | contradiction].
    + split; vm_compute; discriminate.
Qed.

Lemma cost_fire1 :
  firing_data (tagged_rule cost_job1)
    (tagged_c cost_program cost_strata 0 cost_lower
      (accumulated_index cost_after) (frontier_index cost_after)) (plan cost_job1) cost_budget.
Proof.
  split.
  - split.
    + split; [reflexivity | split; [reflexivity |]].
      intros binding Hin; change (In binding [[]]) in Hin.
      destruct Hin as [<- | Hbad]; [|contradiction].
      split; [reflexivity | split; [vm_compute; discriminate | split]].
      * vm_compute; discriminate.
      * intros row c Hbad Hc; change (In row []) in Hbad; contradiction.
    + exact I.
  - split; [reflexivity | intros binding Hbad; change (In binding []) in Hbad; contradiction].
Qed.

Lemma cost_round0 :
  round_values cost_program cost_strata cost_lower 0 cost_budget cost_start.
Proof.
  split.
  - intros j Hj; change (In j [cost_job0]) in Hj.
    destruct Hj as [<- | Hbad]; [|contradiction]; split; [apply cost_fire0 |].
    intros row Hrow; apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws _ _
      (proj2_sig (Join.fire (tagged_rule cost_job0)
        (tagged_c cost_program cost_strata 0 cost_lower
          (accumulated_index cost_start) (frontier_index cost_start))
        (plan cost_job0)))) in Hrow.
    change (In row [[2%positive]]) in Hrow.
    destruct Hrow as [<- | Hbad]; [split; vm_compute; discriminate | contradiction].
  - intro Hnonempty; split.
    + intros f Hf; apply (FinSet.elements_spec (ground_encoding cost_program)
        (ground_encoding_laws cost_program bool_encoding_laws) _ _
        (fresh_wf cost_program cost_strata cost_lower 0 cost_start
          (accumulated_wf _ _ _ _ _
            (initial_ready cost_program bool_encoding_laws cost_facts
              cost_strata cost_lower 0)))) in Hf.
      change (In f [(true, [2%positive])]) in Hf.
      destruct Hf as [<- | Hbad]; [repeat split; vm_compute; discriminate | contradiction].
    + intros j Hj; change (In j [cost_job0]) in Hj.
      destruct Hj as [<- | Hbad]; [|contradiction].
      intros node Hnode; vm_compute in Hnode; destruct Hnode as [<- | Hbad]; [|contradiction].
      split; [reflexivity | split; [apply cost_keys | split]].
      * vm_compute; discriminate.
      * split.
        -- intros row Hbad.
           apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws _ _
             (proj2_sig (rel_of cost_program (frontier_index cost_after) false))) in Hbad.
           change (In row []) in Hbad; contradiction.
        -- intros row key Hbad Hselect.
           apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws _ _
             (proj2_sig (rel_of cost_program (frontier_index cost_after) false))) in Hbad.
           change (In row []) in Hbad; contradiction.
Qed.

Lemma cost_round1 :
  round_values cost_program cost_strata cost_lower 0 cost_budget cost_after.
Proof.
  split.
  - intros j Hj; change (In j [cost_job1]) in Hj.
    destruct Hj as [<- | Hbad]; [|contradiction]; split; [apply cost_fire1 |].
    intros row Hbad; apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws _ _
      (proj2_sig (Join.fire (tagged_rule cost_job1)
        (tagged_c cost_program cost_strata 0 cost_lower
          (accumulated_index cost_after) (frontier_index cost_after))
        (plan cost_job1)))) in Hbad.
    change (In row []) in Hbad; contradiction.
  - intro Hbad; change (true = false) in Hbad; discriminate.
Qed.

Lemma cost_trace fuel : (2 <= Pos.to_nat fuel)%nat ->
  trace (step_c cost_program cost_strata cost_lower 0) (Pos.to_nat fuel) cost_start
    (run cost_program cost_strata cost_lower 0 fuel cost_start) [cost_start; cost_after].
Proof.
  intro Hfuel.
  assert (Hexpected : trace (step_c cost_program cost_strata cost_lower 0)
    (Pos.to_nat fuel) cost_start (inr cost_after) [cost_start; cost_after]).
  { destruct (Pos.to_nat fuel) as [|[|n]] eqn:Hn; [lia | lia |].
    apply trace_next with (next := cost_after).
    - vm_compute; reflexivity.
    - apply trace_stopped; vm_compute; reflexivity. }
  destruct (stratum_trace cost_program cost_facts cost_strata cost_lower 0 fuel)
    as [visited Hactual].
  destruct (trace_functional _ _ _ _ _ _ _ Hexpected Hactual) as [Hresult _].
  fold cost_start in Hresult.
  rewrite <- Hresult; exact Hexpected.
Qed.

Lemma cost_level_data fuel : (2 <= Pos.to_nat fuel)%nat ->
  level_data cost_program cost_facts cost_strata fuel cost_budget cost_visited.
Proof.
  intros Hfuel k Hk; change (k < 1)%nat in Hk; assert (k = 0)%nat by lia; subst k.
  split; [apply cost_trace, Hfuel | split; [apply cost_initial_values |]].
  intros s [<- | [<- | Hbad]]; [apply cost_round0 | apply cost_round1 | contradiction].
Qed.

(** The complete numerical wrapper theorem applies to a real nonempty recursive run. *)
Example nonempty_program_numeric :
  (Cost.ticks (solve_program_fast_c cost_program cost_facts 2%positive) <=
    program_charge cost_program cost_facts 2%positive cost_budget cost_visited)%N.
Proof.
  apply solve_program_fast_cost.
  - apply bool_encoding_laws.
  - intros p Hp; apply cost_keys.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - apply cost_level_data; reflexivity.
Qed.

(** Fuel and binary descent vary in the nonempty recursive importing family. *)
Example varying_program_fuel :
  bigO (fun fuel : positive =>
    program_charge cost_program cost_facts (Pos.succ fuel) cost_budget cost_visited)
    (fun fuel => Cost.ticks (solve_program_fast_c cost_program cost_facts (Pos.succ fuel))).
Proof.
  apply solve_program_fast_bigO.
  - intro fuel; apply bool_encoding_laws.
  - intros fuel p Hp; apply cost_keys.
  - intro fuel; vm_compute; discriminate.
  - intro fuel; vm_compute; discriminate.
  - intro fuel; apply cost_level_data.
    rewrite Pos2Nat.inj_succ; pose proof (Pos2Nat.is_pos fuel); lia.
Qed.

(** The numerical client emits a new fact and subsequently closes with the stationary probe. *)
Example nonempty_cost_run :
  match solve_program_fast cost_program cost_facts 2%positive with
  | Outcome.Solved db =>
    (db_holds cost_program db false [2%positive], db_holds cost_program db true [2%positive])
  | _ => (false, false)
  end = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** Exhaustion has a complete numerical bound on its actual one-round trace. *)
Example exhausted_program_numeric :
  (Cost.ticks (solve_program_fast_c cost_program cost_facts 1%positive) <=
    program_charge cost_program cost_facts 1%positive cost_budget (fun _ => [cost_start]))%N.
Proof.
  apply solve_program_fast_cost.
  - apply bool_encoding_laws.
  - intros p Hp; apply cost_keys.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - intros k Hk; change (k < 1)%nat in Hk; assert (k = 0)%nat by lia; subst k.
    split.
    + change (trace (step_c cost_program cost_strata cost_lower 0) 1 cost_start
        (inl cost_after) [cost_start]).
      apply trace_next with (next := cost_after).
      * vm_compute; reflexivity.
      * apply trace_exhausted.
    + split; [apply cost_initial_values |].
      intros s [<- | Hbad]; [apply cost_round0 | contradiction].
Qed.

Example exhausted_cost_run :
  match solve_program_fast cost_program cost_facts 1%positive with
  | Outcome.OutOfFuel _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition cost_rejected : program bool :=
  Program bool_encoding (fun _ => Cost.ret 1)
    [Rule (Atom true [TConst 2%positive]) [LNeg (Atom false [TConst 2%positive])];
     Rule (Atom false [TConst 2%positive]) [LNeg (Atom true [TConst 2%positive])]].

(** A rejected program pays its primitive stratification budget without assuming a solved result. *)
Example rejected_program_numeric :
  (Cost.ticks (solve_program_fast_c cost_rejected [] 1%positive) <=
    program_charge cost_rejected [] 1%positive cost_budget (fun _ => []))%N.
Proof.
  apply solve_program_fast_cost.
  - apply bool_encoding_laws.
  - intros p Hp; apply cost_keys.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - vm_compute; exact I.
Qed.

Example rejected_cost_run :
  solve_program_fast cost_rejected [] 1%positive = Outcome.Rejected Reason.Bad_stratification.
Proof.
  vm_compute; reflexivity.
Qed.
