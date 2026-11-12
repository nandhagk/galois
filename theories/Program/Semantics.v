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
