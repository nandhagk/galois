(** * Fast-engine comparison with actual legacy delta solving

    Successful bounded legacy computations are lifted to the public total delta solver.
    For example, nonlinear closure compares complete relations after both frontier pivots run.
    Builds on: DatalogSemiNaiveTest, DatalogSolveLegacyTest and RulesDelta. *)

From Stdlib Require Import List Bool PeanoNat PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogSolve DatalogEngine.
From Galois.Tests.Datalog Require Import DatalogSemiNaiveTest DatalogSolveTest.
From Galois.Tests.Legacy.Datalog Require Import DatalogSolveLegacyTest.
From GaloisLegacy.Collections Require CollectionsFinSet.
From GaloisLegacy.Rules Require RulesSolve RulesJoin RulesDelta.
Import List.ListNotations.

Definition fast_legacy_relations (prog : program nat) fast old ps :=
  forallb (fun p => FinSet.equal (set_raw (rel_of prog fast p))
    (set_raw (set_of_list tuple_encoding
      (CollectionsFinSet.FinSet.elements (RulesSolve.rel_of (old_program prog) old p))))) ps.

Definition compare_fast_delta strategy (prog : program nat) facts ps :=
  match solve_program_fast prog facts 8%positive,
    RulesDelta.solve_program_delta strategy (old_program prog) facts with
  | Outcome.Solved fast, Some old => fast_legacy_relations prog fast old ps
  | _, _ => false
  end.

Definition compare_fast_bounded strategy (prog : program nat) facts ps :=
  match solve_program_fast prog facts 8%positive,
    RulesDelta.delta_bounded_program strategy (old_program prog) facts 8%positive with
  | Outcome.Solved fast, Some old => fast_legacy_relations prog fast old ps
  | _, _ => false
  end.

Lemma fast_bounded_is_total strategy prog facts ps :
  compare_fast_bounded strategy prog facts ps = true ->
  compare_fast_delta strategy prog facts ps = true.
Proof.
  unfold compare_fast_bounded, compare_fast_delta.
  destruct (solve_program_fast prog facts 8%positive) as [fast | have | why];
    [|discriminate | discriminate].
  destruct (RulesDelta.delta_bounded_program strategy (old_program prog) facts 8%positive)
    as [old |] eqn:Hold; [|discriminate].
  rewrite (RulesDelta.delta_bounded_program_agrees strategy (old_program prog)
    facts 8%positive old Hold); exact (fun H => H).
Qed.

(** The empty-program fixture compares actual total delta solving under either legacy strategy. *)
Example fast_delta_empty strategy :
  compare_fast_delta strategy engine_empty [] [0; 7] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_recursive_cycle strategy :
  compare_fast_delta strategy engine_cycle [(0, [2%positive])] [0; 1; 7] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_nonlinear strategy :
  compare_fast_delta strategy engine_nonlinear engine_edges [0; 1] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_duplicates strategy :
  compare_fast_delta strategy engine_cycle [(0, [2%positive]); (0, [2%positive])]
    [0; 1] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_nonrecursive strategy :
  compare_fast_delta strategy engine_ground [] [0; 1] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_seed_collision strategy :
  compare_fast_delta strategy engine_ground [(0, [5%positive]); (0, [5%positive])]
    [0; 1] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Definition engine_repeated_once : program nat :=
  Program nat_encoding (fun _ => Cost.ret 1) [engine_duplicate_rule].

Example fast_delta_repeated_body strategy :
  compare_fast_delta strategy engine_repeated_once [(0, [2%positive])] [0; 1] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_repeated_rules strategy :
  compare_fast_delta strategy engine_duplicates [(0, [2%positive])] [0; 1] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_negation strategy :
  compare_fast_delta strategy engine_negation [(0, [2%positive])] [0; 1; 2; 3; 4] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

(** The negative cycle is rejected by the fast and actual legacy total entry points. *)
Example fast_delta_negative_cycle strategy :
  solve_program_fast engine_negative_cycle [] 8%positive =
    Outcome.Rejected Reason.Bad_stratification /\
  RulesDelta.solve_program_delta strategy (old_program engine_negative_cycle) [] = None.
Proof.
  destruct strategy; vm_compute; split; reflexivity.
Qed.

Example fast_delta_linear_chain strategy :
  compare_fast_delta strategy linear chain [0; 1; 7] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_repeated_constant strategy :
  compare_fast_delta strategy repeated_program repeated_facts [0; 1; 2] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_fact_only strategy :
  compare_fast_delta strategy engine_empty [(7, [2%positive])] [0; 7] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.

Example fast_delta_nullary strategy :
  compare_fast_delta strategy engine_nullary [] [0; 1] = true.
Proof.
  apply fast_bounded_is_total; destruct strategy; vm_compute; reflexivity.
Qed.
