(** * Prepared source and context fixtures

    Preparation retains the existing scalar-evolution syntax and its diagnostic code.
    For example, distinct trees at one source root receive distinct dense node identities.
    Builds on: AnalysesLoopsPrepared, AnalysesLoopsRecognise and AnalysesLoopsCheck. *)

From Stdlib Require Import List NArith ZArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseIntern BaseMap BaseSet.
From Galois.Program Require Import ProgramSsa.
From Galois.Analyses.Loops Require Import
  AnalysesLoopsChrec AnalysesLoopsPrepared AnalysesLoopsRecognise AnalysesLoopsCheck.
Import List.ListNotations Cost.Notations Chrec Recognise ScevPrepared.

Definition prepared_source : scev_expr nat := SAdd 5 (SPhi 1) (SConst 2 7).

Definition prepared_result :=
  Cost.value (prepare_c (scev_expr_encoding nat_encoding) expression_phis_c
    prepared_source ScevPrepared.empty).

Example prepared_descriptor_keeps_source_and_diagnostic :
  original (fst prepared_result) = prepared_source /\
  diagnostic (fst prepared_result) = scev_expr_code nat_encoding prepared_source /\
  dependencies (fst prepared_result) = [1] /\
  node_id (fst prepared_result) = 1%positive.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example actual_source_preparation_establishes_correspondence :
  node_valid (scev_expr_encoding nat_encoding)
    (fun e => Cost.value (expression_phis_c e)) (snd prepared_result) (fst prepared_result).
Proof.
  exact (proj1 (proj2 (proj2 (prepare_correct (scev_expr_encoding nat_encoding)
    (scev_expr_encoding_laws nat_encoding nat_encoding_laws) expression_phis_c
    prepared_source ScevPrepared.empty (empty_wf _))))).
Qed.

Definition same_root_other_source : scev_expr nat := SAdd 5 (SPhi 1) (SConst 2 8).

Example same_root_different_tree_keeps_distinct_identity :
  let second := Cost.value (prepare_c (scev_expr_encoding nat_encoding) expression_phis_c
    same_root_other_source (snd prepared_result)) in
  node_id (fst second) = 2%positive /\ original (fst second) = same_root_other_source.
Proof.
  vm_compute. split; reflexivity.
Qed.

Definition no_phis_result :=
  Cost.value (prepare_c (scev_expr_encoding nat_encoding) expression_phis_c
    (SOutside 0) (snd prepared_result)).

Example empty_support_calls_no_observer :
  Cost.ticks (query_c (fun _ : nat => Cost.tick 100 ;; Cost.ret 1%positive)
    (fst no_phis_result)) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition observation_zero : option (Chrec.t nat) := Some (CInv (IConst 0)).

Definition observed_values :=
  snd (Intern.intern (optional_chrec_encoding nat_encoding) observation_zero Intern.empty).

Definition observed_id (_ : nat) := Cost.ret 1%positive.

Definition source_reference (source : scev_expr nat) entries :=
  compile_reference nat_encoding (source, entries).

Definition registered_context :=
  Cost.value (register_c observed_id (fst prepared_result) Intern.empty).

Example registered_compiler_query_has_immutable_meaning :
  context_meaning scev_expression_phis source_reference (snd prepared_result) observed_values
    (snd registered_context) (fst registered_context) =
    Some (Some (CInv (IAdd (IConst 0) (IWordConst 7)))).
Proof.
  vm_compute. reflexivity.
Qed.

Example unallocated_context_has_no_compiler_answer :
  context_meaning scev_expression_phis source_reference (snd prepared_result) observed_values
    (snd registered_context) 2%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition missing_values :=
  snd (Intern.intern (optional_chrec_encoding nat_encoding) None Intern.empty).

Example allocated_unsupported_answer_is_distinct_from_unallocated :
  context_meaning scev_expression_phis source_reference (snd prepared_result) missing_values
    (snd registered_context) (fst registered_context) = Some None.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_registration_reuses_context_id :
  let repeated := Cost.value (register_c observed_id (fst prepared_result)
    (snd registered_context)) in
  fst repeated = fst registered_context /\ Intern.size (snd repeated) = 1.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example repeated_registration_still_pays_dependency_observation :
  (0 < Cost.ticks (register_c observed_id (fst prepared_result) (snd registered_context)))%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example signature_width_is_independent_of_raw_diagnostic :
  key_bits query_encoding (1%positive, [1%positive]) = 23%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition checker_source_values : Map.t nat (unit * definition unit nat unit) := Map.empty.

Definition checker_ops : scev_ops unit unit :=
  ops_of_pure 8%positive (fun _ => 0%Z) (fun _ => false)
    (fun _ => false) (fun _ => None).

Definition checker_source_reference (source : scev_expr nat) entries :=
  PlanCheck.check_reference nat_encoding (fun _ : unit => Cost.ret false)
    checker_source_values checker_ops (source, entries).

Definition checker_observed_values := Intern.of_list bool_encoding [false; true].

Example registered_checker_query_has_the_same_full_reference_type :
  context_meaning scev_expression_phis checker_source_reference
    (snd prepared_result) checker_observed_values
    (snd registered_context) (fst registered_context) = Some (false, FinSet.empty).
Proof.
  vm_compute. reflexivity.
Qed.

Example source_preparation_does_not_change_an_earlier_query_meaning :
  let later := Cost.value (prepare_c (scev_expr_encoding nat_encoding) expression_phis_c
    same_root_other_source (snd prepared_result)) in
  context_meaning scev_expression_phis source_reference (snd later) observed_values
    (snd registered_context) (fst registered_context) =
    Some (Some (CInv (IAdd (IConst 0) (IWordConst 7)))).
Proof.
  vm_compute. reflexivity.
Qed.
