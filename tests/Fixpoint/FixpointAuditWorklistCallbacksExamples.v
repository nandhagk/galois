(** * Declared worklist callback examples

    Small cyclic clients exercise the original results and their recorded callback branches.
    For example, a widening point records a widen call when a value changes.
    Builds on: FixpointAuditWorklistCallbacksAdequacy and FixpointFIX2a. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsHeap CollectionsAuditCost
  CollectionsAuditEncoding CollectionsAuditEncodingAdequacy.
From Galois.Order Require Import OrderLattice OrderBasic.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditWorklistCallbacks
  FixpointAuditWorklistCallbacksAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointFIX2a.
Import List.ListNotations.

(** * A symbolic callback source with one unit of work per invocation *)

Definition fx_fixture_source (sch : scheduler nat) :
    fx_declared_callback_source nat nat bool unit :=
  FxDeclaredCallbackSource nat nat bool unit
    (fun x code body => code = encode nat_encoding x /\ body = [tt])
    (fun c code body => code = encode nat_encoding c /\ body = [tt])
    (fun c x body => x = System.target worklist_cycle c /\ body = [tt])
    (fun x p body => p = priority sch x /\ body = [tt])
    (fun x point body => point = widening_point sch x /\ body = [tt])
    (fun c q body => q = System.rhs worklist_cycle c /\ body = [tt])
    (fun k a q body => q = k a /\ body = [tt])
    (fun a b result body => result = leb bool_lattice a b /\ body = [tt])
    (fun a b result body => result = join bool_lattice a b /\ body = [tt])
    (fun a b result body => result = widen bool_lattice a b /\ body = [tt]).

Definition fx_fixture_budget : fx_declared_callback_budget nat nat bool unit :=
  FxDeclaredCallbackBudget nat nat bool unit (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1).

Lemma fx_fixture_source_laws sch :
  fx_declared_source_laws nat_encoding nat_encoding bool_lattice sch worklist_cycle
    (fx_fixture_source sch).
Proof.
  unfold fx_declared_source_laws, fx_fixture_source; cbn; repeat split;
    intros; exists [tt]; auto.
Qed.

Lemma fx_fixture_bounded sch :
  fx_declared_callback_bounded (fx_fixture_source sch) fx_fixture_budget.
Proof.
  unfold fx_declared_callback_bounded, fx_fixture_source, fx_fixture_budget; cbn.
  repeat split; intros; destruct H as [_ ->]; reflexivity.
Qed.

Definition fx_fixture_index : sys_index nat nat :=
  index_system nat_encoding worklist_cycle worklist_static.

Definition fx_widen_schedule : scheduler nat := Scheduler (fun _ => 1%positive) (fun _ => true).

Definition fx_fixture_run (sch : scheduler nat) (mode : strategy) (fuel : positive) :=
  run_worklist_declared_model nat_encoding nat_encoding bool_lattice sch mode worklist_cycle
    fx_fixture_index fuel.

Definition fx_fixture_has_join (events : audit_trace (fx_declared_call nat nat bool)) : bool :=
  existsb (fun event => match event with
    | AuditCall (FxJoin _ _ _) =>
      true
    | _ =>
      false
    end) events.

Definition fx_fixture_has_widen (events : audit_trace (fx_declared_call nat nat bool)) : bool :=
  existsb (fun event => match event with
    | AuditCall (FxWiden _ _ _) =>
      true
    | _ =>
      false
    end) events.

Definition fx_fixture_has_continuation
    (events : audit_trace (fx_declared_call nat nat bool)) : bool :=
  existsb (fun event => match event with
    | AuditCall (FxContinuation _ _ _ _) =>
      true
    | _ =>
      false
    end) events.

Definition fx_fixture_has_unchanged (events : audit_trace (fx_declared_call nat nat bool)) : bool :=
  existsb (fun event => match event with
    | AuditCall (FxLeb _ _ true) =>
      true
    | _ =>
      false
    end) events.

(** Joining completes the cyclic client with join, continuation and unchanged calls. *)
Example fx_fixture_joining_calls :
  let '(out, events) := fx_fixture_run worklist_schedule Joining 8 in
  option_map cycle_observation out = Some [true; true; false] /\
  fx_fixture_has_join events = true /\ fx_fixture_has_widen events = false /\
  fx_fixture_has_continuation events = true /\ fx_fixture_has_unchanged events = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Widening selects the widen callback at a widening point and reaches the same fixture values. *)
Example fx_fixture_widening_calls :
  let '(out, events) := fx_fixture_run fx_widen_schedule Widening 8 in
  option_map cycle_observation out = Some [true; true; false] /\
  fx_fixture_has_widen events = true /\ fx_fixture_has_join events = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** A non-widening point follows the joining callback even in widening mode. *)
Example fx_fixture_widening_fallback :
  let '(out, events) := fx_fixture_run worklist_schedule Widening 8 in
  option_map cycle_observation out = Some [true; true; false] /\
  fx_fixture_has_join events = true /\ fx_fixture_has_widen events = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Insufficient fuel keeps the original pending outcome while retaining the nonempty trace. *)
Example fx_fixture_exhaustion :
  let '(out, events) := fx_fixture_run worklist_schedule Joining 1 in
  out = None /\ events <> [].
Proof.
  vm_compute; split; [reflexivity|discriminate].
Qed.

(** The concrete source and budget instantiate the same-execution callback theorem. *)
Example fx_fixture_source_bound sch mode fuel :
  let '(out, events) := fx_fixture_run sch mode fuel in
  exists bodies,
    fx_declared_trace_source (fx_fixture_source sch) events bodies /\
    out = run_worklist nat_encoding nat_encoding bool_lattice sch mode worklist_cycle
      (Declared worklist_static fx_fixture_index) fuel /\
    fx_declared_model_work nat_encoding events + fx_declared_body_work (fun _ => 1) bodies <=
      fx_declared_run_input_budget nat_encoding nat_encoding bool_lattice sch mode worklist_cycle
        worklist_static fx_fixture_index fuel +
      fx_declared_external_trace_budget fx_fixture_budget events.
Proof.
  pose proof fx_declared_external_source_holds as Hsource.
  unfold fx_declared_external_source_statement in Hsource.
  unfold fx_fixture_run; apply (Hsource nat nat bool unit nat_encoding nat_encoding bool_lattice
    sch mode worklist_cycle worklist_static fx_fixture_index fuel (fx_fixture_source sch)
    fx_fixture_budget).
  - apply index_system_laws.
  - apply fx_fixture_source_laws.
  - apply fx_fixture_bounded.
Qed.

Definition fx_fixture_bodies (events : audit_trace (fx_declared_call nat nat bool)) :
    list (list (list unit)) :=
  map (fun event => match event with
    | AuditCall (FxPush _ _ _ _ nested)
    | AuditCall (FxPop _ _ nested) =>
      map (fun _ => [tt]) (fx_queue_encoder_entries nested)
    | AuditCall _ =>
      [[tt]]
    | _ =>
      []
    end) events.

(** A finite, nonempty execution satisfies the receipt relation at every recorded call. *)
Example fx_fixture_concrete_receipts :
  let '(_, events) := fx_fixture_run worklist_schedule Joining 1 in
  fx_declared_trace_source (fx_fixture_source worklist_schedule) events (fx_fixture_bodies events).
Proof.
  vm_compute; repeat (constructor || reflexivity || eexists).
Qed.

Definition fx_fixture_continuations (events : audit_trace (fx_declared_call nat nat bool)) :=
  flat_map (fun event => match event with
    | AuditCall (FxContinuation _ value _ (Query.Ret result)) =>
      [(value, result)]
    | _ =>
      []
    end) events.

Definition fx_fixture_pops (events : audit_trace (fx_declared_call nat nat bool)) :=
  flat_map (fun event => match event with
    | AuditCall (FxPop before (Some (_, c, after)) _) =>
      [(PQueue.live_count before, c, PQueue.live_count after)]
    | _ =>
      []
    end) events.

(** The first pop retains its queue transition and the continuation's actual argument and result. *)
Example fx_fixture_first_step_operands :
  let '(_, events) := fx_fixture_run worklist_schedule Joining 1 in
  fx_fixture_pops events = [(3, 0, 2)] /\ fx_fixture_continuations events = [(false, false)] /\
  Nat.ltb 0 (fx_declared_model_work nat_encoding events) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** * A source-shaped receipt for an actual queue encoder call *)

Definition fx_fixture_nat_encoder_source :
    fx_declared_callback_source nat nat bool audit_nat_encoding_event :=
  FxDeclaredCallbackSource nat nat bool audit_nat_encoding_event
    (fun _ _ _ => False)
    (fun c code body => exists work, audit_nat_encode_run c code body work /\
      work = audit_nat_events_work body)
    (fun _ _ _ => False) (fun _ _ _ => False) (fun _ _ _ => False)
    (fun _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False)
    (fun _ _ _ _ => False) (fun _ _ _ _ => False).

Definition fx_fixture_queue_entries (events : audit_trace (fx_declared_call nat nat bool)) :=
  flat_map (fun event => match event with
    | AuditCall (FxPush _ _ _ _ nested)
    | AuditCall (FxPop _ _ nested) =>
      fx_queue_encoder_entries nested
    | _ =>
      []
    end) events.

(** The first run captures the real encoder body for a recorded constraint-key call. *)
Example fx_fixture_actual_nat_encoder_receipt :
  let '(_, events) := fx_fixture_run worklist_schedule Joining 1 in
  In (FxEncodeEntry 1 (fst (audit_nat_encode 1))) (fx_fixture_queue_entries events) /\
  fx_queue_encoder_source fx_fixture_nat_encoder_source
    (FxEncodeEntry 1 (fst (audit_nat_encode 1))) (snd (audit_nat_encode 1)) /\
  fst (audit_nat_encode 1) = encode nat_encoding 1 /\
  snd (audit_nat_encode 1) =
    [AuditNatFrame 1; AuditNatFrame 0; AuditPositiveSuccFrame 1%positive 2%positive] /\
  0 < audit_nat_events_work (snd (audit_nat_encode 1)).
Proof.
  split.
  - vm_compute; tauto.
  - split.
    + cbn [fx_queue_encoder_source fx_fixture_nat_encoder_source].
      destruct (audit_nat_encode_run_total 1) as [code [body [work Hrun]]].
      pose proof (audit_nat_encode_run_correct 1 code body work Hrun) as Hcorrect.
      destruct Hcorrect as [_ [Hresult [Hwork _]]].
      rewrite <- Hresult; cbn; exists work; split; [exact Hrun|].
      unfold audit_nat_events_work; exact Hwork.
    + split; [apply audit_nat_encode_erases|].
      vm_compute; split; [reflexivity|lia].
Qed.
