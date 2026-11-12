(** * Concrete step observations

    Counter and completion machines retain their initial and transition boundaries.
    For example, an administrative transition accepts an empty trace at state one.
    Builds on: Program.SemanticsSig. *)

From Stdlib Require Import List Bool Arith.
From Galois.Base Require Import KeySig.
From Galois.Program Require Import SemanticsSig.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Counter <: SEMANTICS Prog.
  Definition state := nat.
  Definition initial (_ : unit) s := Nat.eqb s 0 = true.
  Definition step (_ : unit) s t := Nat.eqb t (S s) = true.
End Counter.
Definition counter_lstep s (l : list unit) t := (l, t) = ([], S s).

Example counter_initial : Counter.initial tt 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example counter_prefix : counter_lstep 0 [] 1.
Proof.
  vm_compute; reflexivity.
Qed.

(* counter_rejected and counter_rejects_wrong_endpoint were negated steps.
   Their Boolean transition observations retain rejection of (1, 1) and (0, 2). *)
Example counter_rejected : Nat.eqb 1 (S 1) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example counter_rejects_wrong_endpoint : Nat.eqb 2 (S 0) = false.
Proof.
  vm_compute; reflexivity.
Qed.

(* counter_boundary was ~ initial counter 1. *)
Example counter_boundary : Nat.eqb 1 0 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition completion_stepb s (l : list unit) t :=
  (Nat.eqb s 0 && Nat.eqb (length l) 1 && Nat.eqb t 1) ||
  (Nat.eqb s 1 && Nat.eqb (length l) 0 && Nat.eqb t 2).

Example completes_one_step : completion_stepb 1 [] 2 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example rejects_visible_administration : completion_stepb 1 [tt] 2 = false.
Proof.
  vm_compute; reflexivity.
Qed.

(* stable_boundary was 2 <> 1. *)
Example stable_boundary : Nat.eqb 2 1 = false.
Proof.
  vm_compute; reflexivity.
Qed.

(* ProgramStepsTest's counter_local, counter_silent, counter_induction,
   counter_conjunction, counter_monotonicity and counter_quantified are universal
   proof clients of on_steps and reachability. SemanticsSteps retains these laws.
   counter_behaviour is a proof client of SemanticsTraces.same_behaviour_refl.
   Task 3.9 adds no proofs beyond computed examples.

   ProgramRunsTest's one_edge, two_edges, wrong_edge_rejected, empty_history and
   history_has_run use run_edges and Link.taken. CFG_LINK now relates unlabelled
   transitions to one listed edge. It exposes no run_edges history or taken predicate.

   ProgramSimulationTest's identity_counter, composed_counter,
   transports_both_endpoints and preserves_actual_finish use simulation and
   bisimulation transport, which Semantics.v does not export. counter_empty_run
   is a traced_run constructor proof. Its empty event list and endpoint zero
   are unchanged, but it is outside the computed-proof restriction.

   ProgramCompletionTest's completion_laws, completed_behaviour and
   rejects_nondeterministic_administration use administrative completion laws and
   behaviour transport. CfgSig exports no stable/rank completion interface. *)
