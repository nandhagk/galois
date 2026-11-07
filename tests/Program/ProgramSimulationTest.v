(** * Simulation clients

    A counter exercises identity, composition and endpoint-coupled transport.
    For example, its first step reaches one with an empty trace.
    Builds on: ProgramSimulation and ProgramStepsTest. *)

From Stdlib Require Import List.
From Galois.Program Require Import ProgramSemantics ProgramSimulation.
From Galois.Tests.Program Require Import ProgramStepsTest.
Import List.ListNotations.

Definition counter_ends : endings nat :=
  Endings (fun _ => False) (fun _ => False) (fun _ => False).

Example identity_counter :
  bisimulation counter counter_ends counter counter_ends eq.
Proof.
  apply bisimulation_refl.
Qed.

Example composed_counter :
  bisimulation counter counter_ends counter counter_ends
    (fun s u => exists t, s = t /\ t = u).
Proof.
  eapply bisimulation_compose; apply identity_counter.
Qed.

Example transports_both_endpoints :
  same_behaviour counter counter_ends 0 counter counter_ends 0.
Proof.
  eapply behaviour_transport with (R := eq) (t1 := 0) (t2 := 0).
  - apply identity_counter.
  - reflexivity.
  - reflexivity.
  - apply same_behaviour_refl.
Qed.

Example counter_prefix : step counter 0 [] 1.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example counter_rejects_wrong_endpoint : ~ step counter 0 [] 2.
Proof.
  vm_compute; intros [_ Hbad]; discriminate.
Qed.

Example counter_empty_run : exec counter 0 [] 0.
Proof.
  constructor.
Qed.

Definition finite : semantics bool unit :=
  Semantics (fun s => s = false) (fun s l t => s = false /\ l = [tt] /\ t = true).

Definition finite_ends : endings bool :=
  Endings (fun s => s = true) (fun _ => False) (fun _ => False).

Example preserves_actual_finish :
  exists t, exec finite false [tt] t /\ ends_as finite finite_ends EndFinal t.
Proof.
  eapply simulation_finish with (m1 := finite) (e1 := finite_ends) (R := eq) (s := false).
  - apply simulation_refl.
  - reflexivity.
  - exists true; split; [apply exec_one; repeat split; reflexivity|reflexivity].
Qed.
