(** * Pure regions over partial observations

    A pure region observes the supplied denotation once and records its result.
    For example, an undefined observation takes a silent step to a trap.
    Builds on: ProgramSemantics and ProgramSimulation. *)

From Stdlib Require Import List.
From Galois.Program Require Import ProgramSemantics ProgramSimulation.
Import List.ListNotations.

Module EqualityRegion.

(** None is unevaluated and Some None records an undefined observation. *)
Definition region_state (S C : Type) := (S * option (option C))%type.

(** A region preserves its state and emits the successful payload, if any. *)
Definition region_semantics {S C} (den : S -> option C) :
    semantics (region_state S C) C :=
  Semantics (fun _ => True)
    (fun before events after =>
      snd before = None /\ fst after = fst before /\
      snd after = Some (den (fst before)) /\
      events = match den (fst before) with
               | Some c => [c]
               | None => []
               end).

(** Defined results finish normally and undefined results trap without resource stops. *)
Definition region_endings {S C} : endings (region_state S C) :=
  Endings (fun st => exists c, snd st = Some (Some c))
    (fun st => snd st = Some None) (fun _ => False).

(** Related region states are identical and carry an admissible underlying state. *)
Definition region_relation {S C} (adm : S -> Prop) (a b : region_state S C) : Prop :=
  a = b /\ adm (fst a).

(** Admissible equality of the supplied observations preserves each actual region step. *)
Theorem region_step_agrees {S C} (den1 den2 : S -> option C) adm a b events :
  (forall s, adm s -> den1 s = den2 s) -> adm (fst a) ->
  (step (region_semantics den1) a events b <->
    step (region_semantics den2) a events b).
Proof.
  intros Hequal Hadm.
  change ((snd a = None /\ fst b = fst a /\ snd b = Some (den1 (fst a)) /\
      events = match den1 (fst a) with Some c => [c] | None => [] end) <->
    (snd a = None /\ fst b = fst a /\ snd b = Some (den2 (fst a)) /\
      events = match den2 (fst a) with Some c => [c] | None => [] end)).
  now rewrite (Hequal _ Hadm).
Qed.

(** Equal observations give the same enabled transitions at every admissible state. *)
Theorem region_running_agrees {S C} (den1 den2 : S -> option C) adm a :
  (forall s, adm s -> den1 s = den2 s) -> adm (fst a) ->
  (running (region_semantics den1) a <-> running (region_semantics den2) a).
Proof.
  intros Hequal Hadm; split; intros [events [b Hstep]]; exists events, b.
  - apply (region_step_agrees den1 den2 adm a b events Hequal Hadm); exact Hstep.
  - apply (region_step_agrees den1 den2 adm a b events Hequal Hadm); exact Hstep.
Qed.

(** Equal partial observations give a bisimulation preserving payloads and ending tags. *)
Theorem region_bisimulation {S C} (den1 den2 : S -> option C) (adm : S -> Prop) :
  (forall s, adm s -> den1 s = den2 s) ->
  bisimulation (region_semantics den1) region_endings
    (region_semantics den2) region_endings (region_relation adm).
Proof.
  intro Hequal; constructor.
  - intros a b k [-> Hadm]; destruct k; cbn [ends_as]; try reflexivity.
    unfold stuck; now rewrite (region_running_agrees den1 den2 adm b Hequal Hadm).
  - intros a b events after [-> Hadm] Hstep; exists after; split.
    + apply (region_step_agrees den1 den2 adm b after events Hequal Hadm); exact Hstep.
    + split; [reflexivity|].
      destruct Hstep as [_ [Hstate _]]; now rewrite Hstate.
  - intros a b events after [-> Hadm] Hstep; exists after; split.
    + apply (region_step_agrees den1 den2 adm b after events Hequal Hadm); exact Hstep.
    + split; [reflexivity|].
      destruct Hstep as [_ [Hstate _]]; now rewrite Hstate.
Qed.

(** Replacing an equal partial observation preserves all region behaviours. *)
Theorem region_rewrite_behaviour {S C} (den1 den2 : S -> option C) (adm : S -> Prop) s :
  (forall s, adm s -> den1 s = den2 s) -> adm s ->
  same_behaviour (region_semantics den1) region_endings (s, None)
    (region_semantics den2) region_endings (s, None).
Proof.
  intros Hequal Hadm; eapply bisimilar_same_behaviour.
  - apply region_bisimulation; exact Hequal.
  - split; [reflexivity|exact Hadm].
Qed.

(** A result state has no successor because evaluation cannot happen twice. *)
Theorem region_result_halts {S C} (den : S -> option C) s result :
  ~ running (region_semantics den) (s, Some result).
Proof.
  intros [events [after [Hbefore _]]]; discriminate.
Qed.

(** Region ending predicates are disjoint and halt for every supplied observation. *)
Theorem region_endings_wf {S C} (den : S -> option C) :
  endings_wf (region_semantics den) region_endings.
Proof.
  constructor.
  - intros [s result] [c Hresult]; cbn in Hresult; subst result; apply region_result_halts.
  - intros [s result] Hresult; cbn in Hresult; subst result; apply region_result_halts.
  - intros s Hstop; contradiction.
  - intros [s result] [c Hresult] Htrap; cbn in Hresult, Htrap; congruence.
  - intros s Hfinal Hstop; contradiction.
  - intros s Htrap Hstop; contradiction.
Qed.

(** Every unevaluated region takes its prescribed step, including an undefined observation. *)
Theorem region_evaluates {S C} (den : S -> option C) s :
  step (region_semantics den) (s, None)
    (match den s with Some c => [c] | None => [] end) (s, Some (den s)).
Proof.
  repeat split; reflexivity.
Qed.

(** A finite region run is empty or consists of its single prescribed evaluation step. *)
Theorem region_exec_cases {S C} (den : S -> option C) a events b :
  exec (region_semantics den) a events b ->
  (a = b /\ events = []) \/ step (region_semantics den) a events b.
Proof.
  intro Hrun; induction Hrun as [a|a first after rest b Hstep Hrun IH].
  - left; split; reflexivity.
  - destruct IH as [[Heq Hempty]|Hsecond].
    + subst b rest; rewrite app_nil_r; now right.
    + destruct Hstep as [_ [_ [Hresult _]]].
      destruct Hsecond as [Hbefore _]; congruence.
Qed.

(** Replacement clients supply local step and ending diagrams conditional on observation equality.
    The observations may live over a separate state and payload domain. *)
Record replacement_laws {S1 S2 O S C}
    (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop)
    (adm : S -> Prop) (den1 den2 : S -> option C) : Prop := {
  replacement_ends : (forall s, adm s -> den1 s = den2 s) ->
    forall s t k, R s t -> (ends_as m1 e1 k s <-> ends_as m2 e2 k t);
  replacement_forth : (forall s, adm s -> den1 s = den2 s) ->
    forall s t events s', R s t -> step m1 s events s' ->
    exists t', step m2 t events t' /\ R s' t';
  replacement_back : (forall s, adm s -> den1 s = den2 s) ->
    forall s t events t', R s t -> step m2 t events t' ->
    exists s', step m1 s events s' /\ R s' t'
}.

Arguments replacement_ends {S1 S2 O S C m1 e1 m2 e2 R adm den1 den2}.
Arguments replacement_forth {S1 S2 O S C m1 e1 m2 e2 R adm den1 den2}.
Arguments replacement_back {S1 S2 O S C m1 e1 m2 e2 R adm den1 den2}.

(** Local replacement diagrams transfer partial observation equality to whole-program behaviour. *)
Theorem replacement_behaviour {S1 S2 O S C}
    (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop)
    adm (den1 den2 : S -> option C) s t :
  replacement_laws m1 e1 m2 e2 R adm den1 den2 ->
  (forall u, adm u -> den1 u = den2 u) -> R s t ->
  same_behaviour m1 e1 s m2 e2 t.
Proof.
  intros Hreplacement Hequal Hrelated.
  apply (bisimilar_same_behaviour m1 e1 m2 e2 R s t); [|exact Hrelated].
  constructor.
  - exact (replacement_ends Hreplacement Hequal).
  - exact (replacement_forth Hreplacement Hequal).
  - exact (replacement_back Hreplacement Hequal).
Qed.

End EqualityRegion.
