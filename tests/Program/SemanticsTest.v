(** * Concrete step observations

    Counter and completion machines keep their initial and transition boundaries.
    For example, a counter starts at zero, and one step from zero reaches one.

    Groups:
    - Counter: the counter starts at zero, steps to its successor, and rejects other states.
    - Completion: one step from state zero completes, and visible administration is rejected.

    Builds on: Program.SemanticsSig. *)

From Stdlib Require Import List Bool Arith.
From Galois.Base Require Import KeySig.
From Galois.Program Require Import SemanticsSig.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := unit. End Prog.

(** A counter machine whose states are numbers, starts at zero, and steps to its successor. *)
Module Counter <: SEMANTICS Prog.
  Definition state := nat.
  Definition initial (_ : unit) s := Nat.eqb s 0 = true.
  Definition step (_ : unit) s t := Nat.eqb t (S s) = true.
End Counter.

(** * Counter *)

Module CounterTests.

  (** The step from state s to t with an empty trace, where t is the successor of s. *)
  Definition counter_lstep s (l : list unit) t := (l, t) = ([], S s).

  Example zero_is_initial : Counter.initial tt 0.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An empty trace takes state zero to its successor, one. *)
  Example empty_trace_steps_to_successor : counter_lstep 0 [] 1.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** One is not the successor of one. *)
  Example one_is_not_its_successor : Nat.eqb 1 (S 1) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A step from zero to two is rejected, because the successor of zero is one. *)
  Example wrong_endpoint_rejected : Nat.eqb 2 (S 0) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** One is not initial. *)
  Example one_is_not_initial : Nat.eqb 1 0 = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CounterTests.

(** * Completion *)

Module CompletionTests.

  (** A step from state zero with one visible action reaches two. *)
  Definition completion_stepb s (l : list unit) t :=
    (Nat.eqb s 0 && Nat.eqb (length l) 1 && Nat.eqb t 1) ||
    (Nat.eqb s 1 && Nat.eqb (length l) 0 && Nat.eqb t 2).

  (** One step from state zero completes to state one. *)
  Example one_step_completes : completion_stepb 1 [] 2 = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A step from state one with a visible action is rejected. *)
  Example visible_administration_rejected : completion_stepb 1 [tt] 2 = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Two is not the same state as one. *)
  Example two_is_not_one : Nat.eqb 2 1 = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CompletionTests.
