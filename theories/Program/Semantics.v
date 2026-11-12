(** * Program semantics

    Finite traced runs compose and step-local laws apply at reachable sources.
    For example, concatenating two runs retains their event order.
    Builds on: Program.SemanticsSig and Stdlib.List. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig.
From Galois.Program Require Import SemanticsSig.

(** Finite runs concatenate through the same intermediate state. *)
Theorem traced_run_app {S O} (step : S -> list O -> S -> Prop) s u t tr1 tr2 :
  traced_run step s tr1 u -> traced_run step u tr2 t ->
  traced_run step s (tr1 ++ tr2) t.
Proof.
  intros Hrun; induction Hrun as [s|s l s' tr u Hstep Hrun IH]; intro Htail.
  - exact Htail.
  - rewrite <- app_assoc; econstructor; [exact Hstep|apply IH; exact Htail].
Qed.

(** Every individual step is a finite run with the same events. *)
Theorem traced_run_one {S O} (step : S -> list O -> S -> Prop) s l t :
  step s l t -> traced_run step s l t.
Proof.
  intro Hstep; rewrite <- (app_nil_r l); econstructor; [exact Hstep|constructor].
Qed.

Module SemanticsSteps (P : TYPE) (M : SEMANTICS P) (T : TRACES P M).
  Definition on_steps p (Q : M.state -> list T.event -> M.state -> Prop) : Prop :=
    forall s l t, reachable (M.initial p) (M.step p) s -> T.lstep p s l t -> Q s l t.

  (** Pointwise implication transports a step-local law. *)
  Lemma on_steps_mono p Q R :
    (forall s l t, Q s l t -> R s l t) -> on_steps p Q -> on_steps p R.
  Proof.
    intros Himp HQ s l t Hreach Hstep; apply Himp, HQ; assumption.
  Qed.

  (** Two step-local laws hold on the same transition. *)
  Lemma on_steps_and p Q R :
    on_steps p Q -> on_steps p R -> on_steps p (fun s l t => Q s l t /\ R s l t).
  Proof.
    intros HQ HR s l t Hreach Hstep; split; [apply HQ|apply HR]; assumption.
  Qed.

  (** Universal quantification retains the same reachable source and transition. *)
  Lemma on_steps_forall {X} p (Q : X -> M.state -> list T.event -> M.state -> Prop) :
    (forall x, on_steps p (Q x)) <-> on_steps p (fun s l t => forall x, Q x s l t).
  Proof.
    split.
    - intros H s l t Hreach Hstep x; exact (H x s l t Hreach Hstep).
    - intros H x s l t Hreach Hstep; exact (H s l t Hreach Hstep x).
  Qed.
End SemanticsSteps.

Module SemanticsTraces (P : TYPE) (M : SEMANTICS P) (T : TRACES P M).
  (** A state has the same finite and diverging behaviours as itself. *)
  Lemma same_behaviour_refl p s : T.same_behaviour p s s.
  Proof.
    unfold T.same_behaviour; split; [intros; reflexivity|].
    split; intros; reflexivity.
  Qed.

  (** Observable behaviour equality can be reversed. *)
  Lemma same_behaviour_sym p s t :
    T.same_behaviour p s t -> T.same_behaviour p t s.
  Proof.
    intros [Hfinish [Hprefix Hdiv]]; split.
    - intros k tr; symmetry; apply Hfinish.
    - split.
      + intro tr; symmetry; apply Hprefix.
      + intro tr; symmetry; apply Hdiv.
  Qed.

  (** Behaviour equality composes through the same intermediate state. *)
  Lemma same_behaviour_trans p s t u :
    T.same_behaviour p s t -> T.same_behaviour p t u -> T.same_behaviour p s u.
  Proof.
    intros [Hfinish12 [Hprefix12 Hdiv12]] [Hfinish23 [Hprefix23 Hdiv23]]; split.
    - intros k tr; transitivity
        (exists v, traced_run (T.lstep p) t tr v /\ T.ends_as p k v).
      + apply Hfinish12.
      + apply Hfinish23.
    - split.
      + intro tr; transitivity (exists v, traced_run (T.lstep p) t tr v).
        * apply Hprefix12.
        * apply Hprefix23.
      + intro tr; transitivity (T.diverges_after p t tr).
        * apply Hdiv12.
        * apply Hdiv23.
  Qed.
End SemanticsTraces.
