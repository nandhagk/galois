(** * Simulations and behaviour transport

    Simulations preserve the traces and ending tags of their matching endpoints.
    For example, the identity relation gives a bisimulation on any semantics.
    Builds on: ProgramSemantics. *)

From Stdlib Require Import List.
From Galois.Program Require Import ProgramSemantics.

(** A forward simulation preserves each step and every ending at its matched endpoint. *)
Record simulation {S T O} (m1 : semantics S O) (e1 : endings S)
    (m2 : semantics T O) (e2 : endings T) (R : S -> T -> Prop) : Prop := {
  simulation_ends : forall s t k, R s t ->
    ends_as m1 e1 k s -> ends_as m2 e2 k t;
  simulation_step : forall s t l s', R s t -> step m1 s l s' ->
    exists t', step m2 t l t' /\ R s' t'
}.
Arguments simulation_ends {S T O m1 e1 m2 e2 R}.
Arguments simulation_step {S T O m1 e1 m2 e2 R}.

(** Identity preserves every step and ending of a semantics. *)
Theorem simulation_refl {S O} (m : semantics S O) e :
  simulation m e m e eq.
Proof.
  constructor.
  - intros s t k -> Hend; exact Hend.
  - intros s t l s' -> Hstep; exists s'; split; [exact Hstep|reflexivity].
Qed.

(** Finite source runs have matching target runs and related endpoints. *)
Theorem simulation_exec {S T O} (m1 : semantics S O) e1 (m2 : semantics T O) e2 R :
  simulation m1 e1 m2 e2 R ->
  forall s tr s', exec m1 s tr s' -> forall t, R s t ->
    exists t', exec m2 t tr t' /\ R s' t'.
Proof.
  intros Hsim s tr s' Hrun.
  induction Hrun as [s|s l s' tr u Hstep Hrun IH]; intros t Hrel.
  - exists t; split; [constructor|exact Hrel].
  - destruct (simulation_step Hsim s t l s' Hrel Hstep) as [t' [Hhead Hrel']].
    destruct (IH t' Hrel') as [v [Htail Hlast]].
    exists v; split; [econstructor; eassumption|exact Hlast].
Qed.

(** Every finite source trace is a target trace from the specified matching state. *)
Theorem simulation_prefix {S T O} (m1 : semantics S O) e1 (m2 : semantics T O) e2 R :
  simulation m1 e1 m2 e2 R -> forall s t tr, R s t ->
    (exists s', exec m1 s tr s') -> exists t', exec m2 t tr t'.
Proof.
  intros Hsim s t tr Hrel [s' Hrun].
  destruct (simulation_exec m1 e1 m2 e2 R Hsim s tr s' Hrun t Hrel) as [t' [Ht _]].
  exists t'; exact Ht.
Qed.

(** A source finish is preserved at the endpoint selected by the matching run. *)
Theorem simulation_finish {S T O} (m1 : semantics S O) e1 (m2 : semantics T O) e2 R :
  simulation m1 e1 m2 e2 R -> forall s t tr k, R s t ->
    (exists s', exec m1 s tr s' /\ ends_as m1 e1 k s') ->
    exists t', exec m2 t tr t' /\ ends_as m2 e2 k t'.
Proof.
  intros Hsim s t tr k Hrel [s' [Hrun Hend]].
  destruct (simulation_exec m1 e1 m2 e2 R Hsim s tr s' Hrun t Hrel) as [t' [Ht Hlast]].
  exists t'; split; [exact Ht|eapply simulation_ends; eassumption].
Qed.

(** Reversing a bisimulation reverses its matching relation. *)
Theorem bisimulation_sym {S T O} (m1 : semantics S O) e1 (m2 : semantics T O) e2 R :
  bisimulation m1 e1 m2 e2 R -> bisimulation m2 e2 m1 e1 (fun t s => R s t).
Proof.
  intro Hbis; destruct Hbis as [Hends Hforth Hback]; constructor.
  - intros t s k Hrel; symmetry; apply Hends; exact Hrel.
  - intros t s l t' Hrel Hstep; exact (Hback s t l t' Hrel Hstep).
  - intros t s l s' Hrel Hstep; exact (Hforth s t l s' Hrel Hstep).
Qed.

(** Bisimulations compose through the same intermediate matching state. *)
Theorem bisimulation_compose {S T U O} (m1 : semantics S O) e1
    (m2 : semantics T O) e2 (m3 : semantics U O) e3 R Q :
  bisimulation m1 e1 m2 e2 R -> bisimulation m2 e2 m3 e3 Q ->
  bisimulation m1 e1 m3 e3 (fun s u => exists t, R s t /\ Q t u).
Proof.
  intros [Hends1 Hforth1 Hback1] [Hends2 Hforth2 Hback2]; constructor.
  - intros s u k [t [Hst Htu]].
    rewrite (Hends1 s t k Hst); exact (Hends2 t u k Htu).
  - intros s u l s' [t [Hst Htu]] Hstep.
    destruct (Hforth1 s t l s' Hst Hstep) as [t' [Ht Hst']].
    destruct (Hforth2 t u l t' Htu Ht) as [u' [Hu Htu']].
    exists u'; split; [exact Hu|exists t'; split; assumption].
  - intros s u l u' [t [Hst Htu]] Hstep.
    destruct (Hback2 t u l u' Htu Hstep) as [t' [Ht Htu']].
    destruct (Hback1 s t l t' Hst Ht) as [s' [Hs Hst']].
    exists s'; split; [exact Hs|exists t'; split; assumption].
Qed.

(** Identity matches every state and every observation of a semantics. *)
Theorem bisimulation_refl {S O} (m : semantics S O) e :
  bisimulation m e m e eq.
Proof.
  constructor.
  - intros s t k ->; reflexivity.
  - intros s t l s' -> Hstep; exists s'; split; [exact Hstep|reflexivity].
  - intros s t l t' -> Hstep; exists t'; split; [exact Hstep|reflexivity].
Qed.

(** Behaviour equality transports through both endpoints of the same bisimulation. *)
Theorem behaviour_transport {S T O} (m1 : semantics S O) e1
    (m2 : semantics T O) e2 R s1 s2 t1 t2 :
  bisimulation m1 e1 m2 e2 R -> R s1 t1 -> R s2 t2 ->
  same_behaviour m2 e2 t1 m2 e2 t2 -> same_behaviour m1 e1 s1 m1 e1 s2.
Proof.
  intros Hbis Hfirst Hlast Hsame.
  eapply same_behaviour_trans.
  - eapply bisimilar_same_behaviour; eassumption.
  - eapply same_behaviour_trans; [exact Hsame|].
    apply same_behaviour_sym; eapply bisimilar_same_behaviour; eassumption.
Qed.
