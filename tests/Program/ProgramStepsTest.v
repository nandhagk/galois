(** * Step-local law clients

    A counter checks the introduction tactic and reachable invariant principle.
    For example, incrementing zero reaches one silently.
    Builds on: ProgramSteps. *)

From Stdlib Require Import List Arith Lia.
From Galois.Program Require Import ProgramSemantics ProgramSteps.
Import List.ListNotations.

Definition counter : semantics nat unit :=
  Semantics (fun n => n = 0) (fun n l t => l = [] /\ t = S n).

Example counter_local : on_steps counter (fun s _ t => t = S s).
Proof.
  intro_step; exact (proj2 Hstep).
Qed.

Example counter_silent : on_steps counter (fun _ l _ => l = []).
Proof.
  intro_step; exact (proj1 Hstep).
Qed.

Example counter_induction : forall s, reachable_state counter s -> s >= 0.
Proof.
  apply reachable_ind; intros; lia.
Qed.

Example counter_initial : initial counter 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example counter_rejected : ~ step counter 1 [] 1.
Proof.
  vm_compute; intros [_ Hbad]; discriminate.
Qed.

Example counter_boundary : ~ initial counter 1.
Proof.
  vm_compute; discriminate.
Qed.
