(** * Step-local contracts

    Step-local laws apply to transitions whose source is reachable.
    For example, a counter invariant extends from zero to every increment.
    Builds on: ProgramSemantics. *)

From Stdlib Require Import List.
From Galois.Program Require Import ProgramSemantics.

(** A step-local predicate holds for every step from a reachable source. *)
Definition on_steps {S O} (m : semantics S O) (P : S -> list O -> S -> Prop) : Prop :=
  forall s l s', reachable_state m s -> step m s l s' -> P s l s'.

(** Pointwise implication transports a step-local law. *)
Theorem on_steps_mono {S O} (m : semantics S O) P Q :
  (forall s l s', P s l s' -> Q s l s') -> on_steps m P -> on_steps m Q.
Proof.
  intros Himp HP s l s' Hreach Hstep; apply Himp, HP; assumption.
Qed.

(** Two step-local laws hold together on the same transition. *)
Theorem on_steps_and {S O} (m : semantics S O) P Q :
  on_steps m P -> on_steps m Q -> on_steps m (fun s l s' => P s l s' /\ Q s l s').
Proof.
  intros HP HQ s l s' Hreach Hstep; split; [apply HP|apply HQ]; assumption.
Qed.

(** Universal quantification commutes with the step-local premises. *)
Theorem on_steps_forall {S O X} (m : semantics S O) (P : X -> S -> list O -> S -> Prop) :
  (forall x, on_steps m (P x)) <-> on_steps m (fun s l s' => forall x, P x s l s').
Proof.
  split.
  - intros H s l s' Hreach Hstep x; exact (H x s l s' Hreach Hstep).
  - intros H x s l s' Hreach Hstep; exact (H s l s' Hreach Hstep x).
Qed.

(** Every transition from a reachable state reaches a reachable state. *)
Theorem reachable_step {S O} (m : semantics S O) :
  on_steps m (fun _ _ s' => reachable_state m s').
Proof.
  exact (reachable_state_step m).
Qed.

(** Initial establishment and reachable-step preservation prove a reachable invariant. *)
Theorem reachable_ind {S O} (m : semantics S O) (I : S -> Prop) :
  (forall s, initial m s -> I s) ->
  (forall s l s', reachable_state m s -> I s -> step m s l s' -> I s') ->
  forall s, reachable_state m s -> I s.
Proof.
  intros Hinitial Hstep s [s0 [tr [Hinit Hrun]]].
  assert (Hreach : reachable_state m s0).
  { exists s0, nil; split; [exact Hinit|constructor]. }
  pose proof (Hinitial s0 Hinit) as HI.
  clear Hinit; revert Hreach HI.
  induction Hrun as [s|s l s' tr t Hfirst Hrun IH]; intros Hreach HI.
  - exact HI.
  - apply IH.
    + eapply reachable_state_step; eassumption.
    + eapply Hstep; eassumption.
Qed.

(** [intro_step] unfolds a head [on_steps m P] and introduces fresh names
    [s l s' Hs Hstep] for its source, events, target, reachability and step.
    It leaves [P s l s'] and performs no search or simplification. *)
Ltac intro_step :=
  unfold on_steps;
  let s := fresh "s" in
  let l := fresh "l" in
  let t := fresh "s'" in
  let Hs := fresh "Hs" in
  let Hstep := fresh "Hstep" in
  intros s l t Hs Hstep.
