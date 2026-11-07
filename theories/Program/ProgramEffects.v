(** * Instruction effects and silent runs

    Conservative flags describe observations, heap dependence and frame changes.
    For example, a finite run through non-observing instructions has an empty trace.
    Builds on: ProgramSteps. *)

From Stdlib Require Import List Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Program Require Import ProgramSemantics ProgramSteps.

Module Effects.

(** Costed effect flags over-approximate instruction dependencies and actions. *)
Record t (I : Type) := Make {
  reads_c : I -> Cost.t bool;
  writes_c : I -> Cost.t bool;
  may_trap_c : I -> Cost.t bool;
  may_diverge_c : I -> Cost.t bool;
  may_stop_c : I -> Cost.t bool;
  allocates_c : I -> Cost.t bool;
  frees_c : I -> Cost.t bool;
  calls_c : I -> Cost.t bool;
  observes_c : I -> Cost.t bool
}.
Arguments Make {I}.
Arguments reads_c {I}.
Arguments writes_c {I}.
Arguments may_trap_c {I}.
Arguments may_diverge_c {I}.
Arguments may_stop_c {I}.
Arguments allocates_c {I}.
Arguments frees_c {I}.
Arguments calls_c {I}.
Arguments observes_c {I}.

Definition reads {I} (ef : t I) i := Cost.value (reads_c ef i).
Definition writes {I} (ef : t I) i := Cost.value (writes_c ef i).
Definition may_trap {I} (ef : t I) i := Cost.value (may_trap_c ef i).
Definition may_diverge {I} (ef : t I) i := Cost.value (may_diverge_c ef i).
Definition may_stop {I} (ef : t I) i := Cost.value (may_stop_c ef i).
Definition allocates {I} (ef : t I) i := Cost.value (allocates_c ef i).
Definition frees {I} (ef : t I) i := Cost.value (frees_c ef i).
Definition calls {I} (ef : t I) i := Cost.value (calls_c ef i).
Definition observes {I} (ef : t I) i := Cost.value (observes_c ef i).

(** Pure instruction flags charge one primitive tick per query. *)
Definition of_pure {I} reads writes trap diverge stop alloc free calls observe : t I :=
  Make (Cost.lift (fun _ => 1%N) reads) (Cost.lift (fun _ => 1%N) writes)
    (Cost.lift (fun _ => 1%N) trap) (Cost.lift (fun _ => 1%N) diverge)
    (Cost.lift (fun _ => 1%N) stop) (Cost.lift (fun _ => 1%N) alloc)
    (Cost.lift (fun _ => 1%N) free) (Cost.lift (fun _ => 1%N) calls)
    (Cost.lift (fun _ => 1%N) observe).

End Effects.

Module EffectsLink.

(** Concrete instructions, heaps and depths belong to the semantic link. *)
Record t (S I H : Type) := Make {
  instr_at : S -> option I;
  heap : S -> H;
  heap_agree : S -> S -> Prop;
  depth : S -> nat
}.
Arguments Make {S I H}.
Arguments instr_at {S I H}.
Arguments heap {S I H}.
Arguments heap_agree {S I H}.
Arguments depth {S I H}.

End EffectsLink.

(** Divergence within a frame never crosses below its depth after a transition. *)
CoInductive diverges_within {S O} (m : semantics S O) (depth : S -> nat) (d : nat) :
    S -> Prop :=
  | within_step : forall s l s', step m s l s' -> d <= depth s' ->
      diverges_within m depth d s' -> diverges_within m depth d s.
Arguments within_step {S O m depth d}.

(** Flags cover reachable transitions and endings with the legacy framing domains.
    Instruction and comparison-state quantifiers commute past [on_steps].
    Ending clauses retain reachable state-pair domains without requiring a step. *)
Record effects_laws {S O I H} (m : semantics S O) (en : endings S) (ef : Effects.t I)
    (ev : EffectsLink.t S I H) : Prop := {
  silent : forall i, on_steps m (fun s l _ => EffectsLink.instr_at ev s = Some i ->
    Effects.observes ef i = false -> l = nil);
  trap_covered : forall s i, reachable_state m s -> EffectsLink.instr_at ev s = Some i ->
    trapped en s -> Effects.may_trap ef i = true;
  stop_covered : forall s i, reachable_state m s -> EffectsLink.instr_at ev s = Some i ->
    stopped en s -> Effects.may_stop ef i = true;
  heap_frame : forall i, on_steps m (fun s _ s' => EffectsLink.instr_at ev s = Some i ->
    Effects.writes ef i = false -> Effects.allocates ef i = false -> Effects.frees ef i = false ->
    EffectsLink.heap ev s' = EffectsLink.heap ev s);
  reads_frame : forall t i, on_steps m (fun s l s' => EffectsLink.instr_at ev s = Some i ->
    Effects.reads ef i = false -> EffectsLink.heap_agree ev s t ->
    exists t', step m t l t' /\ EffectsLink.heap_agree ev s' t');
  trap_frame : forall s t i, reachable_state m s -> reachable_state m t ->
    EffectsLink.instr_at ev s = Some i -> EffectsLink.instr_at ev t = Some i ->
    Effects.reads ef i = false -> EffectsLink.heap_agree ev s t ->
    (trapped en s <-> trapped en t);
  stop_frame : forall s t i, reachable_state m s -> reachable_state m t ->
    EffectsLink.instr_at ev s = Some i -> EffectsLink.instr_at ev t = Some i ->
    Effects.reads ef i = false -> EffectsLink.heap_agree ev s t ->
    (stopped en s <-> stopped en t);
  frame_frame : forall i, on_steps m (fun s _ s' => EffectsLink.instr_at ev s = Some i ->
    Effects.calls ef i = false -> EffectsLink.depth ev s' = EffectsLink.depth ev s);
  call_returns : forall i, on_steps m (fun s _ s' => EffectsLink.instr_at ev s = Some i ->
    Effects.calls ef i = true -> Effects.may_diverge ef i = false ->
    EffectsLink.depth ev s' = Datatypes.S (EffectsLink.depth ev s) ->
    ~ diverges_within m (EffectsLink.depth ev) (EffectsLink.depth ev s') s')
}.
Arguments silent {S O I H m en ef ev}.
Arguments trap_covered {S O I H m en ef ev}.
Arguments stop_covered {S O I H m en ef ev}.
Arguments heap_frame {S O I H m en ef ev}.
Arguments reads_frame {S O I H m en ef ev}.
Arguments trap_frame {S O I H m en ef ev}.
Arguments stop_frame {S O I H m en ef ev}.
Arguments frame_frame {S O I H m en ef ev}.
Arguments call_returns {S O I H m en ef ev}.

(** A restricted run whose running states have non-observing instructions emits no event. *)
Theorem silent_exec_in {S O I H} (m : semantics S O) (en : endings S) (ef : Effects.t I)
    (ev : EffectsLink.t S I H) (P : S -> Prop) s s' tr :
  effects_laws m en ef ev -> reachable_state m s -> exec_in m P s tr s' ->
  (forall t, P t -> running m t ->
    exists i, EffectsLink.instr_at ev t = Some i /\ Effects.observes ef i = false) ->
  tr = nil.
Proof.
  intros Hlaws Hreachable Hrun Hquiet; revert Hreachable.
  induction Hrun as [s HP|s l s' tr t HP Hstep Hrun IH]; intro Hreachable.
  - reflexivity.
  - destruct (Hquiet s HP (ex_intro _ l (ex_intro _ s' Hstep))) as [i [Hinstr Hsilent]].
    rewrite (silent Hlaws i s l s' Hreachable Hstep Hinstr Hsilent).
    cbn; apply IH; eapply reachable_state_step; eassumption.
Qed.
