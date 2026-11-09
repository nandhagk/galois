(** * Optimistic refinement and its runtime counter

    Hand-written SSA fixtures exercise optimistic cycles and two strict refinement rounds.
    For example, a dependent pair splits one round after its operands split.
    Builds on: AnalysesEqualityRefine and AnalysesEqualityProblemTest. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq.
From Galois.Lattice Require Import LatticePartition.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualitySignature
  AnalysesEqualityRefine.
From Galois.Tests.Analyses.Equality Require Import AnalysesEqualityProblemTest
  AnalysesEqualitySignatureTest.
Import List.ListNotations NumberingSignature NumberingRefine EqualityFixture.

Definition cycle_result := optimistic problem nat_encoding_laws.

Example optimistic_equal_cycle :
  NumberingRefine.equivalent_b problem cycle_result 5 6 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example optimistic_additions :
  NumberingRefine.equivalent_b problem cycle_result 2 3 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example optimistic_impurity_separated :
  NumberingRefine.equivalent_b problem cycle_result 2 4 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example optimistic_other_block_separated :
  NumberingRefine.equivalent_b problem cycle_result 5 7 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example optimistic_checked_fixture : check problem cycle_result = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition separated_cycle_syntax : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.Make cfg nat_encoding (Ssa.values syntax) (Ssa.def_c syntax) (Ssa.home_c syntax)
    (Ssa.params_c syntax)
    (Cost.lift (fun _ => 1%N)
      (fun e => if Nat.eqb (fst e) 0 then [0; 1]
        else if Nat.eqb (snd e) 1 then [6; 5] else [3]))
    (Ssa.guards_c syntax).

Definition separated_cycle_problem :=
  Numbering.of_pure separated_cycle_syntax nat_encoding (Nat.eqb 0).

Example distinct_loop_seeds_stay_separate :
  NumberingRefine.equivalent_b separated_cycle_problem
    (optimistic separated_cycle_problem nat_encoding_laws) 5 6 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition two_round_syntax : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure cfg nat_encoding [0; 1; 2; 3; 4; 5]
    (fun x =>
      match x with
      | 2 => Op 0 [0]
      | 3 => Op 0 [1]
      | 4 => Op 1 [2]
      | 5 => Op 1 [3]
      | _ => Arbitrary
      end)
    (fun _ => 0) (fun _ => []) (fun _ => []) (fun _ => []).

Definition two_round_problem := Numbering.of_pure two_round_syntax nat_encoding (fun _ => true).
Definition round_zero := shape_partition two_round_problem nat_encoding_laws.
Definition round_one := refine_step two_round_problem nat_encoding_laws round_zero.
Definition round_two := refine_step two_round_problem nat_encoding_laws round_one.
Definition round_three := refine_step two_round_problem nat_encoding_laws round_two.

Example two_strict_rounds_then_fixed :
  (partition_leb nat_encoding round_one round_zero,
    partition_leb nat_encoding round_two round_one,
    partition_leb nat_encoding round_three round_two) = (false, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example actual_class_counts :
  (class_count two_round_problem round_zero, class_count two_round_problem round_one,
    class_count two_round_problem round_two) = (4, 5, 6).
Proof.
  vm_compute; reflexivity.
Qed.

Example accepts_after_exactly_two_refinements :
  (check two_round_problem round_zero, check two_round_problem round_one,
    check two_round_problem round_two) = (false, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example same_driver_round_counter :
  (rounds_of two_round_problem (Cost.value (optimistic_c two_round_problem nat_encoding_laws)),
    strict_rounds_of two_round_problem
      (Cost.value (optimistic_c two_round_problem nat_encoding_laws))) = (3, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example optimistic_empty_partition :
  (NumberingRefine.equivalent_b empty_problem
    (optimistic empty_problem nat_encoding_laws) 0 1,
    check empty_problem (optimistic empty_problem nat_encoding_laws)) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** These input sizes count independent addition definitions, excluding their two operands. *)
Definition additions_problem (count : nat) :=
  Numbering.of_pure
    (Ssa.of_pure cfg nat_encoding (0 :: 1 :: seq 2 count)
      (fun x => if Nat.leb 2 x then Op 0 [0; 1] else Arbitrary)
      (fun _ => 0) (fun _ => []) (fun _ => []) (fun _ => @nil (unit * list nat)))
    nat_encoding (fun _ => true).

Definition singleton_problem :=
  Numbering.of_pure
    (Ssa.of_pure cfg nat_encoding [0] (fun _ => @Arbitrary nat nat nat)
      (fun _ => 0) (fun _ => []) (fun _ => []) (fun _ => @nil (unit * list nat)))
    nat_encoding (fun _ => true).

Example singleton_boundary :
  (check singleton_problem (optimistic singleton_problem nat_encoding_laws),
    NumberingRefine.equivalent_b singleton_problem
      (optimistic singleton_problem nat_encoding_laws) 0 1) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example independent_additions_checked :
  (check (additions_problem 4) (optimistic (additions_problem 4) nat_encoding_laws),
    check (additions_problem 8) (optimistic (additions_problem 8) nat_encoding_laws),
    check (additions_problem 16) (optimistic (additions_problem 16) nat_encoding_laws)) =
    (true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example independent_additions_ticks :
  (Cost.ticks (optimistic_c (additions_problem 4) nat_encoding_laws),
    Cost.ticks (optimistic_c (additions_problem 8) nat_encoding_laws),
    Cost.ticks (optimistic_c (additions_problem 16) nat_encoding_laws)) =
    (15320, 26956, 50497)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example raw_unreachable_start_is_rejected :
  Cost.value (finish_c problem nat_encoding_laws (prepare problem) None 1%positive) =
    Rejected problem 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example coarsest_contract_client :
  partition_leb nat_encoding (optimistic problem nat_encoding_laws) discrete = true.
Proof.
  apply (optimistic_coarsest problem nat_encoding_laws discrete); vm_compute; reflexivity.
Qed.

Example certification_contract_client :
  exists result, numbering_certified problem nat_encoding_laws = Some result.
Proof.
  exact (numbering_certified_some problem nat_encoding_laws).
Qed.
