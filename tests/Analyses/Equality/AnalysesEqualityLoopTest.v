(** * Total-query loop reference controls

    Raw unlisted definitions retain their original finite-round classifications.
    For example, an unlisted pure nullary operation is recognized after one round.
    Builds on: AnalysesEqualityLoopReference and AnalysesEqualityProblemTest. *)

From Stdlib Require Import List Bool Arith Lia NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIndex.
From Galois.Program Require Import ProgramSsa.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem
  AnalysesEqualityLoopReference AnalysesEqualityLoopWorklist AnalysesEqualityLoopCorrect.
From Galois.Tests.Analyses.Equality Require Import AnalysesEqualityProblemTest.
Import List.ListNotations.

Definition reference_loop :=
  Numbering.LoopInfo 1 (Cost.lift (fun _ => 1%N) (fun b => Nat.eqb b 1)).

Definition raw_loop_ssa (inventory : list nat) : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure EqualityFixture.cfg nat_encoding inventory
    (fun x =>
      match x with
      | 0 => Op 0 [1]
      | 1 => Op 0 []
      | 3 => Op 1 []
      | 4 => Param 1 0
      | _ => Arbitrary
      end)
    (fun _ => 1) (fun _ => []) (fun _ => []) (fun _ => []).

Definition unlisted_nullary_problem :=
  Numbering.of_pure (raw_loop_ssa [2]) nat_encoding (Nat.eqb 0).

Definition malformed_operand_problem :=
  Numbering.of_pure (raw_loop_ssa [0; 2]) nat_encoding (Nat.eqb 0).

Example unlisted_nullary_is_true :
  NumberingLoopReference.invariant_in_ref unlisted_nullary_problem reference_loop 1 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_inside_operand_uses_its_total_definition :
  NumberingLoopReference.invariant_in_ref malformed_operand_problem reference_loop 0 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example costed_reference_retains_unlisted_query :
  Cost.value (NumberingLoopReference.reference_c unlisted_nullary_problem reference_loop 1) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example costed_reference_retains_malformed_operand :
  Cost.value (NumberingLoopReference.reference_c malformed_operand_problem reference_loop 0) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example impurity_and_parameters_are_not_invariant :
  (Cost.value (NumberingLoopReference.reference_c malformed_operand_problem reference_loop 3),
    Cost.value (NumberingLoopReference.reference_c malformed_operand_problem reference_loop 4)) =
    (false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_inventory_performs_no_reference_round :
  Cost.value (NumberingLoopReference.reference_c
    (Numbering.of_pure (raw_loop_ssa []) nat_encoding (Nat.eqb 0)) reference_loop 1) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example outside_body_initial_observation :
  Cost.value (NumberingLoopReference.reference_c malformed_operand_problem
    (Numbering.LoopInfo 2 (Cost.lift (fun _ => 1%N) (fun b => Nat.eqb b 2))) 0) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reference_agreement_contract :
  Cost.value (NumberingLoopReference.reference_c malformed_operand_problem reference_loop 0) =
    NumberingLoopReference.invariant_in_ref malformed_operand_problem reference_loop 0.
Proof.
  exact (NumberingLoopReference.reference_agrees malformed_operand_problem reference_loop 0).
Qed.

Definition countdown_nodes : FinSet.t nat := FinSet.of_list nat_encoding [0; 1; 2; 3; 4; 5].
Definition countdown_rules : Map.t nat (list nat) :=
  Map.of_list nat_encoding [(0, []); (1, [0; 0]); (2, [1]); (3, [4]); (4, [3])].
Definition countdown_prepared :=
  NumberingLoopWorklist.prepare nat_encoding countdown_nodes countdown_rules.
Definition countdown_result :=
  Cost.value (NumberingLoopWorklist.solve_c nat_encoding countdown_nodes countdown_rules).
Definition countdown_final := NumberingLoopWorklist.last_state countdown_result.

Example repeated_operands_keep_both_user_occurrences :
  Index.find nat_encoding 0 (NumberingLoopWorklist.users countdown_prepared) = [(0, 1); (0, 1)].
Proof.
  vm_compute; reflexivity.
Qed.

Example countdown_chain_and_cycle :
  let marks := NumberingLoopWorklist.marked countdown_final in
  (FinSet.mem nat_encoding 0 marks, FinSet.mem nat_encoding 1 marks,
    FinSet.mem nat_encoding 2 marks, FinSet.mem nat_encoding 3 marks,
    FinSet.mem nat_encoding 4 marks, FinSet.mem nat_encoding 5 marks) =
    (true, true, true, false, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example each_ready_node_is_popped_once :
  NumberingLoopWorklist.processed countdown_final = 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_dependency_count_reaches_zero :
  Map.get nat_encoding 1 (NumberingLoopWorklist.remaining countdown_final) = Some 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example raw_countdown_drains_its_queue :
  match countdown_result with inl _ => false | inr _ => true end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_reference_control :
  (NumberingLoopWorklist.reference nat_encoding countdown_rules 6 1,
    NumberingLoopWorklist.reference nat_encoding countdown_rules 6 2,
    NumberingLoopWorklist.reference nat_encoding countdown_rules 6 3) = (true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example importing_countdown_resource_contract :
  exists final,
    Cost.value (NumberingLoopWorklist.solve_c nat_encoding countdown_nodes countdown_rules) =
      inr final /\
    NumberingLoopWorklist.todo final = [] /\
    NumberingLoopWorklist.state_wf nat_encoding final /\
    NumberingLoopWorklist.processed final <= FinSet.size countdown_nodes.
Proof.
  exact (NumberingLoopWorklist.solve_finishes nat_encoding nat_encoding_laws
    countdown_nodes countdown_rules
    (FinSet.wf_of_list nat_encoding [0; 1; 2; 3; 4; 5])
    (Map.wf_of_list nat_encoding [(0, []); (1, [0; 0]); (2, [1]); (3, [4]); (4, [3])])).
Qed.

Local Lemma countdown_rules_supported :
  NumberingLoopCorrect.rules_supported nat_encoding countdown_nodes countdown_rules.
Proof.
  intros x deps Hget.
  pose proof (proj2 (Map.elements_spec nat_encoding nat_encoding_laws x deps countdown_rules
    (Map.wf_of_list nat_encoding [(0, []); (1, [0; 0]); (2, [1]); (3, [4]); (4, [3])])) Hget)
    as Hin.
  vm_compute in Hin.
  destruct Hin as [Hpair|[Hpair|[Hpair|[Hpair|[Hpair|Hfalse]]]]]; try contradiction;
    injection Hpair as <- <-; vm_compute; reflexivity.
Qed.

Example universal_countdown_reference_agreement :
  forall x,
    FinSet.mem nat_encoding x (NumberingLoopWorklist.marked countdown_final) =
      NumberingLoopWorklist.reference nat_encoding countdown_rules 6 x.
Proof.
  apply (NumberingLoopCorrect.solve_agrees nat_encoding nat_encoding_laws
    countdown_nodes countdown_rules 6).
  - exact (FinSet.wf_of_list nat_encoding [0; 1; 2; 3; 4; 5]).
  - exact (Map.wf_of_list nat_encoding [(0, []); (1, [0; 0]); (2, [1]); (3, [4]); (4, [3])]).
  - exact countdown_rules_supported.
  - vm_compute; lia.
Qed.
