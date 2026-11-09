(** * Stratified program evaluation through semi-naive strata

    The program wrapper completes lower strata before any higher-stratum negative test.
    For example, a recursive lower predicate is closed before a rule tests its absence.
    Builds on: DatalogSemiNaive, DatalogStratify and DatalogSolve storage. *)

From Stdlib Require Import PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseMap.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogSolve
  DatalogSemiNaive.
Import Cost.Notations.

(** Completed local databases replace exactly the supplied stratum targets in the lower database. *)
Fixpoint solve_levels_fast_c {P} (prog : program P) facts st fuel n
    : Cost.t (Outcome.t P relation (database P)) :=
  match n with
  | O => Cost.ret (Outcome.Solved Map.empty)
  | S k =>
    Cost.step ;;
    let* previous := solve_levels_fast_c prog facts st fuel k in
    match previous with
    | Outcome.OutOfFuel have => Cost.ret (Outcome.OutOfFuel have)
    | Outcome.Rejected why => Cost.ret (Outcome.Rejected why)
    | Outcome.Solved db =>
      let* current := SemiNaive.stratum_c prog facts st (rel_of_c prog db) k fuel in
      match current with
      | Outcome.OutOfFuel have => Cost.ret (Outcome.OutOfFuel have)
      | Outcome.Rejected why => Cost.ret (Outcome.Rejected why)
      | Outcome.Solved local =>
        let* ps := stratum_targets_c prog facts st k in
        Cost.map Outcome.Solved (store_relations_c prog ps (rel_of_c prog local) db)
      end
    end
  end.

Definition solve_levels_fast {P} prog facts st fuel n :=
  Cost.value (@solve_levels_fast_c P prog facts st fuel n).

(** The fast program path calls the stratifier and the pivot engine without a reference fallback. *)
Definition solve_program_fast_c {P} (prog : program P) facts fuel
    : Cost.t (Outcome.t P relation (database P)) :=
  let* checked := stratify_c prog in
  match checked with
  | None => Cost.ret (Outcome.Rejected Reason.Bad_stratification)
  | Some st => solve_levels_fast_c prog facts st fuel (count st)
  end.

Definition solve_program_fast {P} prog facts fuel :=
  Cost.value (@solve_program_fast_c P prog facts fuel).

Arguments solve_program_fast_c {P} prog facts fuel : simpl never.
Arguments solve_program_fast {P} prog facts fuel : simpl never.
