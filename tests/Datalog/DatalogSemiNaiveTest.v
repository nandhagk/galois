(** * Direct semi-naive engine computations

    These examples run occurrence-pivot strata and the stratified fast program wrapper.
    For example, nonlinear transitive closure needs both frontier positions and a stationary probe.
    Builds on: DatalogSemiNaive and DatalogEngine. *)

From Stdlib Require Import List Bool PeanoNat PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogModel DatalogCompile DatalogCompileProof DatalogSolve DatalogJoin DatalogSemiNaive
  DatalogSemiNaiveProof
  DatalogSemiNaiveIndex DatalogSemiNaiveFinite DatalogSemiNaiveCost
  DatalogEngine DatalogEngineProof.
Import List.ListNotations SemiNaive SemiNaiveIndex SemiNaiveProof SemiNaiveFinite SemiNaiveCost.
Local Open Scope nat_scope.

Definition engine_zero : stratification nat := Stratification (fun _ => Cost.ret 0) 1.
Definition engine_lower (_ : nat) := Cost.ret (set_empty tuple_encoding).
Definition engine_unary p : atom nat := Atom p [TVar 0].
Definition engine_copy h b : rule nat := Rule (engine_unary h) [LPos (engine_unary b)].

Definition engine_observe {P} (prog : program P) facts fuel queries :=
  match solve_program_fast prog facts fuel with
  | Outcome.Solved db => Some (map (fun f => db_holds prog db (fst f) (snd f)) queries)
  | _ => None
  end.

Definition engine_tag {P R} (result : Outcome.t P relation R) :=
  match result with
  | Outcome.Solved _ => 0
  | Outcome.OutOfFuel _ => 1
  | Outcome.Rejected _ => 2
  end.

Definition engine_cycle : program nat :=
  Program nat_encoding (fun _ => Cost.ret 1) [engine_copy 0 1; engine_copy 1 0].

(** A recursive cycle reaches its finite closure and stops after its frontier is consumed. *)
Example engine_cycle_computes :
  engine_observe engine_cycle [(0, [2%positive])] 2%positive
    [(0, [2%positive]); (1, [2%positive]); (1, [3%positive])] = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition engine_path x y : atom nat := Atom 0 [TVar x; TVar y].
Definition engine_nonlinear_rule : rule nat :=
  Rule (engine_path 0 2) [LPos (engine_path 0 1); LPos (engine_path 1 2)].
Definition engine_nonlinear : program nat :=
  Program nat_encoding (fun _ => Cost.ret 2) [engine_nonlinear_rule].
Definition engine_edges : list (ground_atom nat) :=
  [(0, [1%positive; 2%positive]); (0, [2%positive; 3%positive]);
   (0, [3%positive; 4%positive])].

(** Both recursive positions are retained as distinct jobs. *)
Example nonlinear_pivots :
  map pivot (jobs (initial engine_nonlinear engine_edges engine_zero engine_lower 0)) = [0; 1].
Proof.
  vm_compute; reflexivity.
Qed.

(** Mixed frontier and accumulated paths produce the length-three path. *)
Example nonlinear_chain_computes :
  engine_observe engine_nonlinear engine_edges 3%positive
    [(0, [1%positive; 4%positive]); (0, [4%positive; 1%positive]);
     (0, [1%positive; 3%positive]); (0, [2%positive; 4%positive])] =
    Some [true; false; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

(** A cycle in the input relation terminates after deriving the reflexive paths. *)
Example nonlinear_cycle_computes :
  engine_observe engine_nonlinear
    [(0, [1%positive; 2%positive]); (0, [2%positive; 1%positive])] 2%positive
    [(0, [1%positive; 1%positive]); (0, [2%positive; 2%positive]);
     (0, [1%positive; 3%positive])] = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

(** Reaching the final facts without the stationary probe still reports exhaustion. *)
Example nonlinear_fuel_boundary :
  (engine_tag (solve_program_fast engine_nonlinear engine_edges 1%positive),
   engine_tag (solve_program_fast engine_nonlinear engine_edges 2%positive),
   engine_tag (solve_program_fast engine_nonlinear engine_edges 3%positive)) = (1, 1, 0).
Proof.
  vm_compute; reflexivity.
Qed.

(** Exhaustion carries the actual interrupted local database. *)
Example nonlinear_exhaustion_assignment :
  match stratum engine_nonlinear engine_edges engine_zero engine_lower 0 1%positive with
  | Outcome.OutOfFuel db =>
    (db_holds engine_nonlinear db 0 [1%positive; 3%positive],
     db_holds engine_nonlinear db 0 [1%positive; 4%positive])
  | _ => (false, true)
  end = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition engine_duplicate_rule : rule nat :=
  Rule (engine_unary 1) [LPos (engine_unary 0); LPos (engine_unary 0)].
Definition engine_duplicates : program nat :=
  Program nat_encoding (fun _ => Cost.ret 1) [engine_duplicate_rule; engine_duplicate_rule].

(** Identical source atoms and duplicate rules keep their separate occurrence pivots. *)
Example duplicate_occurrence_tags :
  map (fun j => map pred (positive_atoms (body (tagged_rule j))))
    (jobs (initial engine_duplicates [(0, [2%positive])]
      engine_zero engine_lower 0)) =
    [[(0, true); (0, false)]; [(0, false); (0, true)];
     [(0, true); (0, false)]; [(0, false); (0, true)]].
Proof.
  vm_compute; reflexivity.
Qed.

(** Repeated pivots and duplicate seeds produce one new tuple per relation. *)
Example duplicate_derivations_computes :
  engine_observe engine_duplicates [(0, [2%positive]); (0, [2%positive])] 2%positive
    [(0, [2%positive]); (1, [2%positive]); (1, [3%positive])] = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

(** Candidates already in accumulated storage disappear in the candidate-first difference. *)
Example duplicate_candidates_removed :
  let start := initial engine_duplicates [(0, [2%positive]); (1, [2%positive])]
    engine_zero engine_lower 0 in
  (FinSet.size (candidates engine_duplicates engine_zero engine_lower 0 start),
   FinSet.size (fresh engine_duplicates engine_zero engine_lower 0 start),
   engine_tag (stratum engine_duplicates [(0, [2%positive]); (1, [2%positive])]
     engine_zero engine_lower 0 1%positive)) = (1, 0, 0).
Proof.
  vm_compute; reflexivity.
Qed.

Definition engine_ground : program nat :=
  Program nat_encoding (fun _ => Cost.ret 1)
    [Rule (Atom 0 [TConst 5%positive]) []].

(** An empty-body rule and duplicate facts share one initial frontier tuple. *)
Example nonrecursive_seed_collision :
  let facts := [(0, [5%positive]); (0, [5%positive])] in
  (FinSet.size (accumulated (initial engine_ground facts engine_zero engine_lower 0)),
   engine_observe engine_ground facts 1%positive
     [(0, [5%positive]); (0, [6%positive])]) = (1, Some [true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition engine_negation : program nat :=
  Program nat_encoding (fun _ => Cost.ret 1)
    [engine_copy 1 0;
     Rule (engine_unary 2) [LPos (engine_unary 0); LNeg (engine_unary 1)];
     Rule (engine_unary 3) [LPos (engine_unary 0); LNeg (engine_unary 4)]].

(** Completed lower closure determines negative tests in the higher stratum. *)
Example stratified_negation_computes :
  engine_observe engine_negation [(0, [2%positive])] 2%positive
    [(1, [2%positive]); (2, [2%positive]); (3, [2%positive])] =
    Some [true; false; true].
Proof.
  vm_compute; reflexivity.
Qed.

Definition engine_negative_cycle : program nat :=
  Program nat_encoding (fun _ => Cost.ret 1)
    [Rule (Atom 0 [TConst 1%positive]) [LNeg (Atom 1 [TConst 1%positive])];
     Rule (Atom 1 [TConst 1%positive]) [LNeg (Atom 0 [TConst 1%positive])]].

(** Failed stratification is distinct from exhausted evaluation. *)
Example negative_cycle_rejected :
  solve_program_fast engine_negative_cycle [] 1%positive =
    Outcome.Rejected Reason.Bad_stratification.
Proof.
  vm_compute; reflexivity.
Qed.

Definition engine_empty : program nat := Program nat_encoding (fun _ => Cost.ret 1) [].

Example empty_engine_computes :
  engine_observe engine_empty [] 1%positive [(0, [1%positive])] = Some [false].
Proof.
  vm_compute; reflexivity.
Qed.

Example fact_only_engine_computes :
  engine_observe engine_empty [(7, [2%positive])] 1%positive
    [(7, [2%positive]); (7, [3%positive]); (0, [2%positive])] = Some [true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition engine_nullary : program nat :=
  Program nat_encoding (fun _ => Cost.ret 0) [Rule (Atom 0 []) []].

Example nullary_engine_computes :
  engine_observe engine_nullary [] 1%positive [(0, []); (0, [1%positive])] = Some [true; false].
Proof.
  vm_compute; reflexivity.
Qed.

(** Runtime costs include initialization, indexed rounds and the stationary probe. *)
Example nonlinear_engine_ticks :
  (0 < Cost.ticks (stratum_c engine_nonlinear engine_edges
    engine_zero engine_lower 0 3%positive))%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** * Importing semantic families *)

Definition engine_cycle_facts (cs : list positive) : list (ground_atom nat) :=
  map (fun c => (0, [c])) cs.

Lemma engine_copy_safe h b : safe_rule (engine_copy h b).
Proof.
  intros v [Hv | [a [Ha _]]].
  - exists (engine_unary b); split; [now left | exact Hv].
  - cbn in Ha; destruct Ha as [Hbad | Hbad]; [discriminate | contradiction].
Qed.

Lemma engine_cycle_wf cs : program_wf engine_cycle (engine_cycle_facts cs).
Proof.
  split.
  - intros r [<- | [<- | Hbad]]; [| | contradiction];
      split; [apply engine_copy_safe | | apply engine_copy_safe |];
      split; [reflexivity | intros l [<- | Hbad]; [reflexivity | contradiction]
        | reflexivity | intros l [<- | Hbad]; [reflexivity | contradiction]].
  - intros f Hf; apply in_map_iff in Hf as [c [<- _]]; reflexivity.
Qed.

Lemma engine_cycle_stratified : stratified engine_cycle engine_zero.
Proof.
  split.
  - intro p; change (0 < 1); lia.
  - intros r l [<- | [<- | Hbad]] Hl; [| | contradiction];
      destruct Hl as [<- | Hbad];
      [change (0 <= 0); lia | contradiction | change (0 <= 0); lia | contradiction].
Qed.

(** The client varies the source fact inventory including repeated and absent constants. *)
Example semantic_cycle_family cs fuel db :
  solve_program_fast engine_cycle (engine_cycle_facts cs) fuel = Outcome.Solved db ->
  represents (rel_of engine_cycle db) (least_model engine_cycle (engine_cycle_facts cs)).
Proof.
  apply solve_program_fast_exact; [apply nat_encoding_laws | apply engine_cycle_wf].
Qed.

(** Every fuel above the named finite capacity works on the actual fast wrapper for this family. *)
Example adequate_cycle_family cs fuel :
  (Pos.of_succ_nat (capacity engine_cycle (engine_cycle_facts cs)) <= fuel)%positive ->
  exists db, solve_program_fast engine_cycle (engine_cycle_facts cs) fuel = Outcome.Solved db.
Proof.
  apply solve_program_fast_adequate.
  - apply nat_encoding_laws.
  - apply engine_cycle_wf.
  - exists engine_zero; apply engine_cycle_stratified.
Qed.

(** A nonempty actual run instantiates the universal semantic theorem at all queried tuples. *)
Example nonempty_semantic_cycle :
  exists db, solve_program_fast engine_cycle (engine_cycle_facts [2%positive; 3%positive])
    2%positive = Outcome.Solved db /\
    represents (rel_of engine_cycle db)
      (least_model engine_cycle (engine_cycle_facts [2%positive; 3%positive])).
Proof.
  assert (Hrun : exists db,
    solve_program_fast engine_cycle (engine_cycle_facts [2%positive; 3%positive])
      2%positive = Outcome.Solved db).
  { vm_compute; eexists; reflexivity. }
  destruct Hrun as [db Hdb]; exists db; split; [exact Hdb |].
  apply (semantic_cycle_family _ _ _ Hdb).
Qed.

(** * New-batch numerical clients *)

Definition engine_cost_batch :=
  FinSet.of_list (ground_encoding engine_empty) [(7%nat, [2%positive])].

Definition engine_cost_state old : state nat :=
  State old FinSet.empty Map.empty Map.empty [].

Lemma engine_cost_batch_keys f :
  FinSet.mem (ground_encoding engine_empty) f engine_cost_batch = true ->
  (key_bits (ground_encoding engine_empty) f <= 1000)%N /\
  key_budget (penc engine_empty) 200 200 (fst f) /\
  key_budget tuple_encoding 200 200 (snd f).
Proof.
  intro Hf; apply (mem_of_list (ground_encoding engine_empty)
    (ground_encoding_laws engine_empty nat_encoding_laws)) in Hf.
  destruct Hf as [<- | Hbad]; [|contradiction].
  repeat split; vm_compute; discriminate.
Qed.

(** This numerical client accepts arbitrary old storage while inserting a nonempty indexed batch. *)
Example nonempty_advance_numeric old :
  (Cost.ticks (advance_c engine_empty (engine_cost_state old) engine_cost_batch) <=
    advance_charge (engine_cost_state old) engine_cost_batch 1 1 200 200 200 200 1000)%N.
Proof.
  apply advance_cost.
  - apply nat_encoding_laws.
  - apply FinSet.wf_of_list.
  - apply engine_cost_batch_keys.
  - intros j Hbad; contradiction.
Qed.

(** Accumulated cardinality varies without entering the fresh-side advancement domain. *)
Example varying_accumulated_advance :
  bigO (fun old : FinSet.t (ground_atom nat) =>
    advance_charge (engine_cost_state old) engine_cost_batch 1 1 200 200 200 200 1000)
    (fun old => Cost.ticks (advance_c engine_empty (engine_cost_state old) engine_cost_batch)).
Proof.
  apply advance_bigO.
  - intro old; apply nat_encoding_laws.
  - intro old; apply FinSet.wf_of_list.
  - intros old; apply engine_cost_batch_keys.
  - intros old j Hbad; contradiction.
Qed.

(** A prepared ground-pivot plan starts empty and receives the new batch through maintenance. *)
Definition engine_cost_recursive_rule : rule nat :=
  Rule (Atom 7 [TConst 2%positive]) [LPos (Atom 7 [TConst 2%positive])].

Definition engine_cost_job : job nat :=
  Job engine_cost_recursive_rule 0 (tag_rule engine_cost_recursive_rule 0)
    (Join.prepare (tag_program engine_empty) [Atom (7, true) [TConst 2%positive]]
      (fun _ => Cost.ret (set_empty tuple_encoding))).

Lemma engine_cost_frontier_rows row :
  member row (rel_of engine_empty
    (add_atoms engine_empty (FinSet.elements engine_cost_batch) Map.empty) 7) = true ->
  row = [2%positive].
Proof.
  rewrite (add_atoms_exact engine_empty nat_encoding_laws) by apply Map.wf_empty.
  rewrite rel_empty.
  change ((false = true \/ In (7, row) [(7, [2%positive])]) -> row = [2%positive]).
  intros [Hbad | [Heq | Hbad]]; [discriminate | congruence | contradiction].
Qed.

Lemma engine_cost_job_data :
  maintenance_data engine_empty
    (add_atoms engine_empty (FinSet.elements engine_cost_batch) Map.empty)
    (plan engine_cost_job) 1 1 200 200 200 200.
Proof.
  intros node Hnode; vm_compute in Hnode; destruct Hnode as [<- | Hbad]; [|contradiction].
  split; [reflexivity | split].
  - split; vm_compute; discriminate.
  - split; [vm_compute; discriminate | split].
    + intros row Hrow; apply engine_cost_frontier_rows in Hrow; subst row;
        vm_compute; discriminate.
    + intros row key Hrow Hselect; apply engine_cost_frontier_rows in Hrow; subst row.
      vm_compute in Hselect; injection Hselect as <-.
      split; vm_compute; discriminate.
Qed.

Definition engine_cost_inventory_state (n : nat) old : state nat :=
  State old FinSet.empty Map.empty Map.empty (repeat engine_cost_job n).

(** The family varies the cached job inventory and arbitrary accumulated storage together. *)
Example varying_inventory_advance :
  bigO (fun x : nat * FinSet.t (ground_atom nat) =>
    advance_charge (engine_cost_inventory_state (fst x) (snd x))
      engine_cost_batch 1 1 200 200 200 200 1000)
    (fun x => Cost.ticks (advance_c engine_empty
      (engine_cost_inventory_state (fst x) (snd x)) engine_cost_batch)).
Proof.
  apply advance_bigO.
  - intro x; apply nat_encoding_laws.
  - intro x; apply FinSet.wf_of_list.
  - intros x; apply engine_cost_batch_keys.
  - intros x j Hj; apply repeat_spec in Hj; subst j; apply engine_cost_job_data.
Qed.

Example nonempty_inventory_numeric old :
  (Cost.ticks (advance_c engine_empty (engine_cost_inventory_state 2 old) engine_cost_batch) <=
    advance_charge (engine_cost_inventory_state 2 old)
      engine_cost_batch 1 1 200 200 200 200 1000)%N.
Proof.
  apply advance_cost.
  - apply nat_encoding_laws.
  - apply FinSet.wf_of_list.
  - apply engine_cost_batch_keys.
  - intros j Hj; apply repeat_spec in Hj; subst j; apply engine_cost_job_data.
Qed.

(** Updating the prepared frontier plan makes its nonempty matching binding observable. *)
Example maintained_frontier_plan_runs :
  Join.run (plan (Cost.value (update_job_c engine_empty
    (add_atoms engine_empty (FinSet.elements engine_cost_batch) Map.empty)
    engine_cost_job))) = [[]].
Proof.
  vm_compute; reflexivity.
Qed.

(** * Chain tick controls *)

Definition engine_linear_chain : program nat :=
  Program nat_encoding (fun p => Cost.ret (if Nat.eqb p 0 then 2 else 1))
    [Rule (Atom 1 [TVar 1])
      [LPos (Atom 1 [TVar 0]); LPos (Atom 0 [TVar 0; TVar 1])]].

Definition engine_chain_four : list (ground_atom nat) :=
  [(1, [1%positive]); (0, [1%positive; 2%positive]); (0, [2%positive; 3%positive]);
   (0, [3%positive; 4%positive])].

Definition engine_chain_eight : list (ground_atom nat) :=
  engine_chain_four ++
  [(0, [4%positive; 5%positive]); (0, [5%positive; 6%positive]);
   (0, [6%positive; 7%positive]); (0, [7%positive; 8%positive])].

Example four_fact_chain_computes :
  engine_observe engine_linear_chain engine_chain_four 4%positive
    [(1, [1%positive]); (1, [2%positive]); (1, [3%positive]); (1, [4%positive]);
     (1, [5%positive])] = Some [true; true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example eight_fact_chain_computes :
  engine_observe engine_linear_chain engine_chain_eight 8%positive
    [(1, [1%positive]); (1, [4%positive]); (1, [7%positive]); (1, [8%positive]);
     (1, [9%positive])] = Some [true; true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

(** These computed tick observations are a finite control and supply no asymptotic theorem. *)
Example chain_tick_growth_control :
  (0 < Cost.ticks (solve_program_fast_c engine_linear_chain engine_chain_four 4%positive) /\
   Cost.ticks (solve_program_fast_c engine_linear_chain engine_chain_eight 8%positive) <=
     3 * Cost.ticks (solve_program_fast_c engine_linear_chain engine_chain_four 4%positive))%N.
Proof.
  vm_compute; split; [reflexivity | discriminate].
Qed.

Definition engine_chain_strata : stratification nat :=
  Stratification (fun p => Cost.ret (if Nat.eqb p 0 then 0 else 1)) 2.

Definition engine_chain_lower facts p :=
  if Nat.eqb p 0 then facts_at_c engine_linear_chain facts p
  else Cost.ret (set_empty tuple_encoding).

Lemma engine_chain_stratified : stratified engine_linear_chain engine_chain_strata.
Proof.
  split.
  - intro p; change ((if Nat.eqb p 0 then 0 else 1) < 2).
    destruct (Nat.eqb p 0); lia.
  - intros r l [<- | Hbad] Hl; [|contradiction].
    destruct Hl as [<- | [<- | Hbad]]; [| |contradiction].
    + change (1 <= 1); lia.
    + change (0 <= 1); lia.
Qed.

(** The manually stratified chain has one reachability pivot and a fixed lower edge relation. *)
Example single_pivot_chain_inventory :
  map pivot (jobs (initial engine_linear_chain engine_chain_eight engine_chain_strata
    (engine_chain_lower engine_chain_eight) 1)) = [0].
Proof.
  vm_compute; reflexivity.
Qed.

(** Both tick-control runs close their stratum and perform the stationary probe. *)
Example single_pivot_chain_solved :
  (engine_tag (stratum engine_linear_chain engine_chain_four engine_chain_strata
     (engine_chain_lower engine_chain_four) 1 4%positive),
   engine_tag (stratum engine_linear_chain engine_chain_eight engine_chain_strata
     (engine_chain_lower engine_chain_eight) 1 8%positive)) = (0, 0).
Proof.
  vm_compute; reflexivity.
Qed.

(** Doubling facts uses at most three times the ticks in this nonempty stratum control. *)
Example single_pivot_chain_tick_control :
  (0 < Cost.ticks (stratum_c engine_linear_chain engine_chain_four engine_chain_strata
     (engine_chain_lower engine_chain_four) 1 4%positive) /\
   Cost.ticks (stratum_c engine_linear_chain engine_chain_eight engine_chain_strata
     (engine_chain_lower engine_chain_eight) 1 8%positive) <=
     3 * Cost.ticks (stratum_c engine_linear_chain engine_chain_four engine_chain_strata
       (engine_chain_lower engine_chain_four) 1 4%positive))%N.
Proof.
  vm_compute; split; [reflexivity | discriminate].
Qed.
