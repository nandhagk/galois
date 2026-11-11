(** * Pure-region observations and semantic controls

    The fixtures distinguish successful observations, traps and evaluated endpoints.
    For example, observing zero emits [0] and observing None emits no events.
    Builds on: AnalysesEqualityRegion. *)

From Stdlib Require Import List Arith.
From Galois.Program Require Import ProgramSemantics.
From Galois.Analyses.Equality Require Import AnalysesEqualityRegion.
Import List.ListNotations EqualityRegion.

Definition defined : unit -> option nat := fun _ => Some 0.
Definition undefined : unit -> option nat := fun _ => None.

Example defined_step :
  step (region_semantics defined) (tt, None) [0] (tt, Some (Some 0)).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example undefined_step :
  step (region_semantics undefined) (tt, None) [] (tt, Some None).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example cannot_emit_on_trap :
  ~ step (region_semantics undefined) (tt, None) [0] (tt, Some None).
Proof.
  vm_compute; intros [_ [_ [_ Hwrong]]]; discriminate.
Qed.

Example cannot_evaluate_twice :
  ~ step (region_semantics defined) (tt, Some (Some 0)) [0] (tt, Some (Some 0)).
Proof.
  vm_compute; intros [Hbefore _]; discriminate.
Qed.

Example defined_finishes : final (@region_endings unit nat) (tt, Some (Some 0)).
Proof.
  vm_compute; exists 0; reflexivity.
Qed.

Example undefined_traps : trapped (@region_endings unit nat) (tt, Some None).
Proof.
  vm_compute; reflexivity.
Qed.

Example undefined_does_not_finish : ~ final (@region_endings unit nat) (tt, Some None).
Proof.
  vm_compute; intros [c Hdefined]; discriminate.
Qed.

Example no_resource_stop : ~ stopped (@region_endings unit nat) (tt, None).
Proof.
  vm_compute; tauto.
Qed.

Example no_divergence_after_result : ~ diverges (region_semantics defined) (tt, Some (Some 0)).
Proof.
  intro Hdiv; inversion Hdiv as [s events after Hstep Htail]; subst.
  exact (region_result_halts defined tt (Some 0) (ex_intro _ events (ex_intro _ after Hstep))).
Qed.

Example equal_partial_observations_have_same_behaviour :
  same_behaviour (region_semantics undefined) region_endings (tt, None)
    (region_semantics (fun _ => @None nat)) region_endings (tt, None).
Proof.
  apply (region_rewrite_behaviour undefined (fun _ => @None nat) (fun _ => True)).
  - intros [] _; reflexivity.
  - exact I.
Qed.

Example defined_and_undefined_have_different_behaviour :
  ~ same_behaviour (region_semantics defined) region_endings (tt, None)
    (region_semantics undefined) region_endings (tt, None).
Proof.
  intro Hsame.
  assert (Htrap : exists t, exec (region_semantics undefined) (tt, None) [] t /\
    ends_as (region_semantics undefined) region_endings EndTrap t).
  { exists (tt, Some None); split.
    - apply exec_one; exact (region_evaluates undefined tt).
    - reflexivity. }
  apply (same_finish _ _ _ _ _ _ Hsame EndTrap []) in Htrap.
  destruct Htrap as [t [Hrun Htrap]].
  apply region_exec_cases in Hrun; destruct Hrun as [[<- _]|Hstep].
  - discriminate Htrap.
  - destruct Hstep as [_ [_ [Hresult _]]]; change (snd t = Some None) in Htrap.
    change (snd t = Some (Some 0)) in Hresult; congruence.
Qed.

Example replacement_client_keeps_traps :
  replacement_laws (region_semantics undefined) region_endings
    (region_semantics (fun _ => @None nat)) region_endings
    (region_relation (fun _ => True)) (fun _ => True) undefined (fun _ => @None nat).
Proof.
  constructor.
  - intros Hequal; exact (bisim_ends _ _ _ _ _
      (region_bisimulation undefined (fun _ => @None nat) (fun _ => True) Hequal)).
  - intros Hequal; exact (bisim_forth _ _ _ _ _
      (region_bisimulation undefined (fun _ => @None nat) (fun _ => True) Hequal)).
  - intros Hequal; exact (bisim_back _ _ _ _ _
      (region_bisimulation undefined (fun _ => @None nat) (fun _ => True) Hequal)).
Qed.
