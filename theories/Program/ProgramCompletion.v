(** * Bounded administrative completion

    Silent administrative steps complete each visible target step at a stable endpoint.
    For example, a pending store update can finish before the next visible transition.
    Builds on: ProgramSemantics. *)

From Stdlib Require Import List Arith Lia.
From Galois.Program Require Import ProgramSemantics.
Import List.ListNotations.

Module Completion.

(** Administrative runs take silent steps only from unstable states. *)
Inductive admin_steps {T O} (m : semantics T O) (stable : T -> Prop) :
    T -> nat -> T -> Prop :=
  | AdminRefl : forall r, admin_steps m stable r 0 r
  | AdminStep : forall r u n t,
      ~ stable r -> step m r [] u -> admin_steps m stable u n t ->
      admin_steps m stable r (S n) t.
Arguments AdminRefl {T O m stable}.
Arguments AdminStep {T O m stable}.

(** Administrative completion is a finite silent run of the target semantics. *)
Theorem admin_exec {T O} (m : semantics T O) stable r n t :
  admin_steps m stable r n t -> exec m r [] t.
Proof.
  intro Hsteps; induction Hsteps as [r|r u n t Hunstable Hstep Htail IH].
  - constructor.
  - eapply exec_step with (l := []) (tr := []); eassumption.
Qed.

(** A stable state admits only the empty administrative completion. *)
Theorem admin_stable {T O} (m : semantics T O) stable r n t :
  stable r -> admin_steps m stable r n t -> n = 0 /\ t = r.
Proof.
  intros Hstable Hsteps; destruct Hsteps as [r|r u n t Hunstable Hstep Htail].
  - split; reflexivity.
  - contradiction.
Qed.

(** Completion laws pair each visible head with its actual stable administrative endpoint. *)
Record laws {S T O} (m1 : semantics S O) (e1 : endings S)
    (m2 : semantics T O) (e2 : endings T) (stable : T -> Prop) (rank : T -> nat)
    (R : S -> T -> Prop) : Prop := Laws {
  relation_stable : forall s t, R s t -> stable t;
  declared_ends : forall s t k, R s t -> k <> EndStuck ->
    (ends_as m1 e1 k s <-> ends_as m2 e2 k t);
  administrative_step : forall t tr t', ~ stable t -> step m2 t tr t' ->
    tr = [] /\ rank t' < rank t;
  administrative_deterministic : forall t u v, ~ stable t ->
    step m2 t [] u -> step m2 t [] v -> u = v;
  no_intermediate_ends : forall t k, ~ stable t -> k <> EndStuck -> ~ ends_as m2 e2 k t;
  forth : forall s t tr s', R s t -> step m1 s tr s' ->
    exists u n v, step m2 t tr u /\ admin_steps m2 stable u n v /\ stable v /\ R s' v;
  back : forall s t tr u, R s t -> step m2 t tr u ->
    exists s' n v, step m1 s tr s' /\ admin_steps m2 stable u n v /\ stable v /\ R s' v
}.
Arguments relation_stable {S T O m1 e1 m2 e2 stable rank R}.
Arguments declared_ends {S T O m1 e1 m2 e2 stable rank R}.
Arguments administrative_step {S T O m1 e1 m2 e2 stable rank R}.
Arguments administrative_deterministic {S T O m1 e1 m2 e2 stable rank R}.
Arguments no_intermediate_ends {S T O m1 e1 m2 e2 stable rank R}.
Arguments forth {S T O m1 e1 m2 e2 stable rank R}.
Arguments back {S T O m1 e1 m2 e2 stable rank R}.

(** Closure relates a source state to a target that completes to its matching stable state. *)
Definition closure {S T O} (m : semantics T O) stable (R : S -> T -> Prop) s t : Prop :=
  exists n u, admin_steps m stable t n u /\ stable u /\ R s u.

Section Completion.

Context {S T O : Type} (m1 : semantics S O) (e1 : endings S)
  (m2 : semantics T O) (e2 : endings T) (stable : T -> Prop) (rank : T -> nat)
  (R : S -> T -> Prop) (H : laws m1 e1 m2 e2 stable rank R).

Local Lemma running_agrees s t : R s t -> (running m1 s <-> running m2 t).
Proof.
  intro HR; split; intros [tr [u Hstep]].
  - destruct (forth H s t tr u HR Hstep) as [v [n [w [Hhead Htail]]]].
    exists tr, v; exact Hhead.
  - destruct (back H s t tr u HR Hstep) as [v [n [w [Hhead Htail]]]].
    exists tr, v; exact Hhead.
Qed.

Local Lemma endings_agree s t k : R s t -> (ends_as m1 e1 k s <-> ends_as m2 e2 k t).
Proof.
  intro HR; destruct k.
  - exact (declared_ends H s t EndFinal HR ltac:(discriminate)).
  - exact (declared_ends H s t EndTrap HR ltac:(discriminate)).
  - exact (declared_ends H s t EndStop HR ltac:(discriminate)).
  - pose proof (running_agrees s t HR) as Hrunning.
    pose proof (declared_ends H s t EndFinal HR ltac:(discriminate)) as Hfinal.
    pose proof (declared_ends H s t EndTrap HR ltac:(discriminate)) as Htrap.
    pose proof (declared_ends H s t EndStop HR ltac:(discriminate)) as Hstop.
    change ((~ running m1 s /\ ~ final e1 s /\ ~ trapped e1 s /\ ~ stopped e1 s) <->
      (~ running m2 t /\ ~ final e2 t /\ ~ trapped e2 t /\ ~ stopped e2 t)).
    cbn [ends_as] in Hfinal, Htrap, Hstop; tauto.
Qed.

Local Lemma administrative_not_ending t u :
  ~ stable t -> step m2 t [] u -> forall k, ~ ends_as m2 e2 k t.
Proof.
  intros Hunstable Hstep k Hend; destruct k.
  - exact (no_intermediate_ends H t EndFinal Hunstable ltac:(discriminate) Hend).
  - exact (no_intermediate_ends H t EndTrap Hunstable ltac:(discriminate) Hend).
  - exact (no_intermediate_ends H t EndStop Hunstable ltac:(discriminate) Hend).
  - destruct Hend as [Hnot_running Hother]; apply Hnot_running; exists [], u; exact Hstep.
Qed.

Local Lemma closure_ending_relation s t k :
  closure m2 stable R s t -> ends_as m2 e2 k t -> R s t.
Proof.
  intros [n [u [Hsteps [Hstable HR]]]] Hend.
  destruct Hsteps as [t|t v n u Hunstable Hstep Htail].
  - exact HR.
  - exfalso; exact (administrative_not_ending t v Hunstable Hstep k Hend).
Qed.

(** Silent completion is a stuttering simulation on arbitrary related states. *)
Theorem stutters :
  stuttering m1 e1 m2 e2 (closure m2 stable R) (fun _ _ => 0) (fun _ t => rank t).
Proof.
  constructor.
  - intros s t k [n [u [Hsteps [Hstable HR]]]] Hend; exists u; split.
    + exact (admin_exec m2 stable t n u Hsteps).
    + exact (proj1 (endings_agree s u k HR) Hend).
  - intros s t k HE Hend; exists s; split; [constructor|].
    exact (proj2 (endings_agree s t k (closure_ending_relation s t k HE Hend)) Hend).
  - intros s t tr s' [n [u [Hsteps [Hstable HR]]]] Hstep.
    destruct (forth H s u tr s' HR Hstep) as [v [n' [w [Hhead [Htail [Hw HR']]]]]].
    right; exists u, v; split; [exact (admin_exec m2 stable t n u Hsteps)|].
    split; [exact Hhead|]; exists n', w; repeat split; assumption.
  - intros s t tr t' [n [u [Hsteps [Hstable HR]]]] Hstep.
    destruct Hsteps as [t|t v n u Hunstable Hfirst Htail].
    + destruct (back H s t tr t' HR Hstep) as [s' [n' [w [Hhead [Htail [Hw HR']]]]]].
      right; exists s, s'; split; [constructor|]; split; [exact Hhead|].
      exists n', w; repeat split; assumption.
    + destruct (administrative_step H t tr t' Hunstable Hstep) as [-> Hrank].
      assert (Heq : v = t') by
        (eapply administrative_deterministic; [exact H|exact Hunstable|exact Hfirst|
          exact Hstep]).
      subst v; left; split; [reflexivity|]; split; [|exact Hrank].
      exists n, u; repeat split; assumption.
Qed.

(** Completion preserves ending tags, finite prefixes and diverging prefixes. *)
Theorem behaviour s t : R s t -> same_behaviour m1 e1 s m2 e2 t.
Proof.
  intro HR; eapply stuttering_same_behaviour; [exact stutters|].
  exists 0, t; split; [constructor|]; split; [exact (relation_stable H s t HR)|exact HR].
Qed.

End Completion.

End Completion.
Import Completion.
