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

Example counter_conjunction :
  on_steps counter (fun s l t => t = S s /\ l = []).
Proof.
  apply on_steps_and; [exact counter_local|exact counter_silent].
Qed.

Example counter_monotonicity : on_steps counter (fun s _ t => s < t).
Proof.
  eapply on_steps_mono with (P := fun s _ t => t = S s); [|exact counter_local].
  intros s l t Hnext; subst t; lia.
Qed.

Example counter_quantified :
  on_steps counter (fun s _ t => forall x : nat, s + x < t + x).
Proof.
  apply (proj1 (on_steps_forall counter (fun x s _ t => s + x < t + x))).
  intro x; intro_step; destruct Hstep as [_ ->]; lia.
Qed.

Example counter_behaviour : same_behaviour counter (Endings (fun _ => False)
    (fun _ => False) (fun _ => False)) 0
    counter (Endings (fun _ => False) (fun _ => False) (fun _ => False)) 0.
Proof.
  apply same_behaviour_refl.
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
