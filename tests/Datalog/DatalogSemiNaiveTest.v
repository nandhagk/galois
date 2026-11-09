(** * Direct semi-naive engine computations

    These examples run occurrence-pivot strata and the stratified fast program wrapper.
    For example, nonlinear transitive closure needs both frontier positions and a stationary probe.
    Builds on: DatalogSemiNaive and DatalogEngine. *)

From Stdlib Require Import List Bool PeanoNat PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogModel DatalogCompileProof DatalogSolve DatalogSemiNaive DatalogSemiNaiveProof
  DatalogSemiNaiveFinite DatalogEngine DatalogEngineProof.
Import List.ListNotations SemiNaive SemiNaiveProof SemiNaiveFinite.
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

(** This client varies the complete source fact inventory, including repeated and absent constants. *)
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
