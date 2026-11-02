(** * Numbered callback execution examples

    A reached numbered constraint retains its label, RHS, target and unary encoder work.
    For example, an absent index invokes the original fallback constraint.
    Builds on: numbered machine adequacy and the recursive Nat encoder client. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditMap CollectionsAuditEncoding
    CollectionsAuditEncodingAdequacy.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist FixpointNested
  FixpointObserve FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditNestedMachine
  FixpointAuditObserveNumber FixpointAuditObserveNumberCallbacks FixpointAuditObserveNumberMachine
  FixpointAuditObserveNumberMachineAdequacy FixpointAuditObserveNumberExecute
  FixpointAuditObserveNumberExecuteAdequacy FixpointAuditObserveExecute
  FixpointAuditObserveExecuteAdequacy FixpointIndex FixpointAuditNestedCallbacks.
From Galois.Tests.Fixpoint Require Import FixpointFIX5 FixpointAuditNestedExamples.
Import List.ListNotations.

(** * Reached callbacks from an absent occurrence *)

Definition fx_number_client_plan : NestedPlan.t nat nat :=
  NestedPlan.Make NestedEnd Map.empty Map.empty FinSet.empty.

Definition fx_number_client_ready : NestedState.t nat nat nested_test_value :=
  NestedState.Make Map.empty [3] [] FinSet.empty false.

Definition fx_number_client_step :=
  fx_number_machine_step nat_encoding fx_nested_client_lattice fx_number_client_plan Joining
    fx_nested_client_cycle 3 (observation_number 0 (System.constraints fx_nested_client_cycle))
    fx_number_client_ready.

Definition fx_number_client_encoding_three (events : list audit_nat_encoding_event) : bool :=
  match events with
  | [AuditNatFrame 3; AuditNatFrame 2; AuditNatFrame 1; AuditNatFrame 0;
     AuditPositiveSuccFrame 1 2; AuditPositiveSuccFrame 2 3;
     AuditPositiveSuccFrame 3 4; AuditPositiveSuccFrame 1 2] => true
  | _ => false
  end.

Definition fx_number_client_rhs_seen (event : fx_number_machine_event nat nat nested_test_value) :
  bool :=
  match event with
  | FxNumberMachineRhs 3 3 (Query.Ask 3 _) [AuditMapGet 3 4%positive _ None encoding _] =>
      fx_number_client_encoding_three encoding
  | _ => false
  end.

Definition fx_number_client_target_seen (event : fx_number_machine_event nat nat
  nested_test_value) : bool :=
  match event with
  | FxNumberMachineTarget 3 3 3 [AuditMapGet 3 4%positive _ None encoding _] =>
      fx_number_client_encoding_three encoding
  | _ => false
  end.

Definition fx_number_client_continuation_seen (event : fx_number_machine_event nat nat
  nested_test_value) : bool :=
  match event with
  | FxNumberMachineNested events => existsb fx_nested_test_query_continuation events
  | _ => false
  end.

Definition fx_number_client_get_seen (event : fx_number_machine_event nat nat nested_test_value) :
  bool :=
  match event with
  | FxNumberMachineNested events => existsb (fun nested =>
      match nested with
      | FxNestedQuery calls => existsb (fun call =>
          match call with
          | AuditCall (FxGet 3 4%positive _ _ _) => true
          | _ => false
          end) calls
      | _ => false
      end) events
  | _ => false
  end.

(** Both reached callbacks use fallback 3, and both label maps retain all eight unary/carry
  frames. *)
Example fx_number_client_actual_calls :
  let '(out, events) := fx_number_client_step in
  (match out with
  | Some _ => true
  | None => false
  end) = true /\
  existsb fx_number_client_rhs_seen events = true /\
  existsb fx_number_client_target_seen events = true /\
  existsb fx_number_client_continuation_seen events = true /\
  existsb fx_number_client_get_seen events = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The actual reached RHS and target bodies each cost one, and the key-three source costs
  sixteen. *)
Example fx_number_client_actual_body_work :
  fx_source_rhs fx_nested_test_source 3 (System.rhs fx_nested_client_cycle 3) [inr tt] /\
  fx_source_target fx_nested_test_source 3 (System.target fx_nested_client_cycle 3) [inr tt] /\
  fx_one_body_work fx_nested_test_weight [inr tt] + fx_one_body_work fx_nested_test_weight [inr
    tt] = 2 /\
  fx_source_encode_x fx_nested_test_source 3 (fst (fx_nested_test_encode 3))
    (snd (fx_nested_test_encode 3)) /\
  fx_one_body_work fx_nested_test_weight (snd (fx_nested_test_encode 3)) = 16.
Proof.
  repeat split; try reflexivity; apply fx_nested_test_encoder_source_receipt.
Qed.

(** The actual ready step supplies ordered source bodies and the combined same-execution bound. *)
Example fx_number_client_step_source :
  let '(out, events) := fx_number_client_step in
  exists bodies, Forall2 (fx_number_machine_event_source fx_nested_test_source) events bodies /\
    out = nested_step nat_encoding fx_nested_client_lattice fx_number_client_plan Joining
      (observation_system fx_nested_client_cycle 3) fx_number_client_ready /\
    fx_number_machine_work events + fx_declared_body_work fx_nested_test_weight bodies <=
      fx_number_machine_step_budget nat_encoding fx_nested_client_lattice fx_number_client_plan
        Joining
        fx_nested_client_cycle 3 (observation_number 0 (System.constraints fx_nested_client_cycle))
        fx_number_client_ready +
      fold_right (fun e n => fx_number_machine_external_budget fx_nested_test_budget e + n) 0
        events.
Proof.
  unfold fx_number_client_step.
  pose proof fx_number_machine_step_source as Hsource.
  unfold fx_number_machine_step_source_statement in Hsource.
  apply (Hsource nat nat nested_test_value (audit_nat_encoding_event + unit)%type nat_encoding
    fx_nested_client_lattice fx_number_client_plan Joining fx_nested_client_cycle 3
    fx_nested_test_source fx_nested_test_budget fx_number_client_ready).
  - change (In 3 [3]); left; reflexivity.
  - apply fx_nested_test_machine_source_laws.
Qed.

Lemma fx_number_receipt_at X C A B (source : fx_declared_callback_source X C A B)
    events groups n event :
  Forall2 (fx_number_machine_event_source source) events groups ->
  nth_error events n = Some event ->
  exists group, nth_error groups n = Some group /\ fx_number_machine_event_source source event
    group.
Proof.
  intros Hgroups; revert n event; induction Hgroups as [|head group events groups Hhead Hrest IH];
    intros [|n] event Hnth; cbn in Hnth; try discriminate.
  - inversion Hnth; subst event; exists group; auto.
  - apply IH; exact Hnth.
Qed.

(** The theorem's same-step receipts include the reached original RHS and target bodies. *)
Example fx_number_client_reached_body_receipts :
  let '(_, events) := fx_number_client_step in
  exists groups rhs_events target_events,
    Forall2 (fx_number_machine_event_source fx_nested_test_source) events groups /\
    In (FxNumberMachineRhs 3 3 (System.rhs fx_nested_client_cycle 3) rhs_events) events /\
    In (FxNumberMachineTarget 3 3 (System.target fx_nested_client_cycle 3) target_events) events /\
    nth_error groups 1 = Some [[inr tt]] /\ nth_error groups 3 = Some [[inr tt]].
Proof.
  pose proof fx_number_client_step_source as Hsource.
  destruct fx_number_client_step as [out events] eqn:Hrun.
  destruct Hsource as [groups [Hgroups _]].
  assert (Hevents : events = snd fx_number_client_step) by (rewrite Hrun; reflexivity).
  set (rhs_events :=
    match nth_error events 1 with
    | Some (FxNumberMachineRhs _ _ _ captured) => captured
    | _ => []
    end).
  set (target_events :=
    match nth_error events 3 with
    | Some (FxNumberMachineTarget _ _ _ captured) => captured
    | _ => []
    end).
  assert (Hrhs_at : nth_error events 1 =
    Some (FxNumberMachineRhs 3 3 (System.rhs fx_nested_client_cycle 3) rhs_events)).
  { unfold rhs_events; rewrite Hevents; unfold fx_number_client_step; vm_compute; reflexivity. }
  assert (Htarget_at : nth_error events 3 =
    Some (FxNumberMachineTarget 3 3 (System.target fx_nested_client_cycle 3) target_events)).
  { unfold target_events; rewrite Hevents; unfold fx_number_client_step; vm_compute; reflexivity. }
  assert (Hrhs : In (FxNumberMachineRhs 3 3 (System.rhs fx_nested_client_cycle 3) rhs_events)
    events)
    by (eapply nth_error_In; exact Hrhs_at).
  assert (Htarget : In (FxNumberMachineTarget 3 3 (System.target fx_nested_client_cycle 3)
    target_events) events)
    by (eapply nth_error_In; exact Htarget_at).
  destruct (fx_number_receipt_at nat nat nested_test_value (audit_nat_encoding_event + unit)%type
    fx_nested_test_source events groups 1 _ Hgroups Hrhs_at) as [rhs_group [Hrhs_group Hrhs_body]].
  cbn [fx_number_machine_event_source fx_nested_test_source fx_source_rhs] in Hrhs_body.
  destruct Hrhs_body as [body [-> [_ ->]]].
  destruct (fx_number_receipt_at nat nat nested_test_value (audit_nat_encoding_event + unit)%type
    fx_nested_test_source events groups 3 _ Hgroups Htarget_at) as [target_group [Htarget_group
      Htarget_body]].
  cbn [fx_number_machine_event_source fx_nested_test_source fx_source_target] in Htarget_body.
  destruct Htarget_body as [body [-> [_ ->]]].
  exists groups, rhs_events, target_events; repeat split; assumption.
Qed.

(** * The same reached calls inside a whole numbered execution *)

Definition fx_number_client_schedule : list (ObservationComponent.t nat nat) :=
  [ObservationComponent.Make [3]
    (NestedPlan.Make (NestedVisit 3 NestedEnd) Map.empty (Map.set nat_encoding 3 [3] Map.empty)
      FinSet.empty) [3] [3]].

Definition fx_number_client_execution :=
  fx_number_execute nat_encoding fx_nested_client_lattice Joining fx_nested_client_cycle 3
    (observation_number 0 (System.constraints fx_nested_client_cycle)) fx_number_client_schedule
      true 3.

Definition fx_number_execution_rhs_seen (event : fx_number_execute_event nat nat
  nested_test_value) : bool :=
  match event with
  | FxNumberExecuteMachine events => existsb fx_number_client_rhs_seen events
  | _ => false
  end.

Definition fx_number_execution_target_seen (event : fx_number_execute_event nat nat
  nested_test_value) : bool :=
  match event with
  | FxNumberExecuteMachine events => existsb fx_number_client_target_seen events
  | _ => false
  end.

Definition fx_number_execution_get_seen (event : fx_number_execute_event nat nat
  nested_test_value) : bool :=
  match event with
  | FxNumberExecuteMachine events => existsb fx_number_client_get_seen events
  | _ => false
  end.

(** The fuelled whole execution reaches both fallback callbacks and its key-three query lookup. *)
Example fx_number_client_execution_actual_calls :
  let '(out, events) := fx_number_client_execution in
  out = None /\ existsb fx_number_execution_rhs_seen events = true /\
  existsb fx_number_execution_target_seen events = true /\
  existsb fx_number_execution_get_seen events = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The whole execution has receipts and the derived bound under the genuine unary source laws. *)
Example fx_number_client_execution_source :
  let '(out, events) := fx_number_client_execution in
  exists groups, Forall2 (fx_number_execute_event_source fx_nested_test_source) events groups /\
    out = observation_execute nat_encoding fx_nested_client_lattice Joining
      (observation_system fx_nested_client_cycle 3) fx_number_client_schedule true 3 /\
    fx_number_execute_work events + fx_declared_body_work fx_nested_test_weight groups <=
      fx_number_execute_budget nat_encoding fx_nested_client_lattice Joining
        fx_nested_client_cycle 3
        (observation_number 0 (System.constraints fx_nested_client_cycle))
          fx_number_client_schedule true 3 +
      fold_right (fun e n => fx_number_execute_external_budget fx_nested_test_budget e + n) 0
        events.
Proof.
  unfold fx_number_client_execution.
  pose proof fx_number_execute_source as Hsource; unfold fx_number_execute_source_statement in
    Hsource.
  apply (Hsource nat nat nested_test_value (audit_nat_encoding_event + unit)%type nat_encoding
    fx_nested_client_lattice Joining fx_nested_client_cycle 3 fx_nested_test_source
      fx_nested_test_budget
    fx_number_client_schedule true 3%positive).
  - change (In 3 [3]); left; reflexivity.
  - apply fx_nested_test_machine_source_laws.
Qed.

(** * The unnumbered execution uses the same genuine callback source *)

Lemma fx_observe_client_schedule_within :
  fx_observe_schedule_targets_within nat_encoding (System.constraints fx_nested_client_cycle)
    fx_number_client_schedule.
Proof.
  intros component x c Hin Htarget.
  cbn [fx_number_client_schedule] in Hin; destruct Hin as [<-|Hin]; [|contradiction].
  unfold index_get in Htarget; cbn [ObservationComponent.code NestedPlan.targets] in Htarget.
  destruct (Nat.eq_dec x 3) as [->|Hneq].
  - rewrite Map.get_set_same in Htarget; cbn in Htarget.
    change (In c [3]); exact Htarget.
  - rewrite Map.get_set_other in Htarget by exact Hneq.
    rewrite Map.get_empty in Htarget; contradiction.
Qed.

(** A nonempty unnumbered run gets actual callback receipts from its constrained schedule. *)
Example fx_observe_client_execution_source :
  let '(out, events) := fx_observe_execute nat_encoding fx_nested_client_lattice Joining
    fx_nested_client_cycle fx_number_client_schedule true 3 in
  exists groups, Forall2 (fx_observe_event_source fx_nested_test_source) events groups /\
    out = observation_execute nat_encoding fx_nested_client_lattice Joining fx_nested_client_cycle
      fx_number_client_schedule true 3 /\
    fx_observe_work nat_encoding events + fx_declared_body_work fx_nested_test_weight groups <=
      fx_observe_execute_input_budget nat_encoding fx_nested_client_lattice Joining
        fx_nested_client_cycle
        fx_number_client_schedule true 3 +
      fold_right (fun e n => fx_observe_event_external_budget fx_nested_test_budget e + n) 0 events.
Proof.
  pose proof fx_observe_execute_source as Hsource; unfold fx_observe_execute_source_statement in
    Hsource.
  apply (Hsource nat nat nested_test_value (audit_nat_encoding_event + unit)%type nat_encoding
    nat_encoding
    fx_nested_client_lattice Joining fx_nested_client_cycle fx_nested_test_source
      fx_nested_test_budget
    fx_number_client_schedule true 3%positive).
  - apply fx_nested_test_machine_source_laws.
  - apply fx_observe_client_schedule_within.
Qed.

Lemma fx_number_declared_receipt_at X C A B (source : fx_declared_callback_source X C A B)
    events groups n event :
  fx_declared_trace_source source events groups -> nth_error events n = Some event ->
  exists group, nth_error groups n = Some group /\ fx_declared_event_source source event group.
Proof.
  intros Hgroups; revert n event; induction Hgroups as [|head group events groups Hhead Hrest IH];
    intros [|n] event Hnth; cbn in Hnth; try discriminate.
  - inversion Hnth; subst event; exists group; auto.
  - apply IH; exact Hnth.
Qed.

(** The reached query's actual key-three encoder body is present in the theorem's receipt group. *)
Example fx_number_client_reached_encoder_body :
  let '(_, events) := fx_number_client_step in
  exists groups outer body,
    Forall2 (fx_number_machine_event_source fx_nested_test_source) events groups /\
    nth_error groups 2 = Some outer /\ In body outer /\
    fx_source_encode_x fx_nested_test_source 3 4%positive body /\
    fx_one_body_work fx_nested_test_weight body = 16.
Proof.
  pose proof fx_number_client_step_source as Hsource.
  destruct fx_number_client_step as [out events] eqn:Hrun.
  destruct Hsource as [groups [Hgroups _]].
  assert (Hevents : events = snd fx_number_client_step) by (rewrite Hrun; reflexivity).
  set (calls :=
    match nth_error events 2 with
    | Some (FxNumberMachineNested [FxNestedQuery captured]) => captured
    | _ => []
    end).
  assert (Hquery_at : nth_error events 2 = Some (FxNumberMachineNested [FxNestedQuery calls])).
  { unfold calls; rewrite Hevents; unfold fx_number_client_step; vm_compute; reflexivity. }
  destruct (fx_number_receipt_at nat nat nested_test_value (audit_nat_encoding_event + unit)%type
    fx_nested_test_source events groups 2 _ Hgroups Hquery_at) as [outer [Houter Houter_source]].
  cbn [fx_number_machine_event_source] in Houter_source.
  destruct Houter_source as [nested_groups [Hnested ->]].
  inversion Hnested as [|nested nested_group remaining remaining_groups Hnested_group Hnil];
    subst nested remaining; inversion Hnil; subst remaining_groups; subst nested_groups.
  cbn [fx_nested_machine_event_source] in Hnested_group.
  destruct Hnested_group as [query_groups [Hquery ->]].
  set (trace :=
    match nth_error calls 1 with
    | Some (AuditCall (FxGet _ _ _ _ captured)) => captured
    | _ => []
    end).
  assert (Hget_at : nth_error calls 1 = Some (AuditCall (FxGet 3 4%positive Map.empty None trace))).
  { unfold trace; unfold calls; rewrite Hevents; unfold fx_number_client_step; vm_compute;
    reflexivity. }
  destruct (fx_number_declared_receipt_at nat nat nested_test_value (audit_nat_encoding_event +
    unit)%type
    (fx_number_passthrough_source fx_nested_test_source) calls query_groups 1 _ Hquery Hget_at)
    as [key_group [Hkey Hkey_source]].
  cbn [fx_declared_event_source fx_declared_call_source fx_number_passthrough_source] in
    Hkey_source.
  destruct Hkey_source as [body [-> Hbody]].
  assert (Hin : In body (concat query_groups)).
  { apply in_concat; exists [body]; split; [eapply nth_error_In; exact Hkey|now left]. }
  assert (Hsource_body : fx_source_encode_x fx_nested_test_source 3 4%positive body) by exact Hbody.
  cbn [fx_nested_test_source fx_source_encode_x fx_nested_test_encode_source] in Hbody.
  destruct Hbody as [encoding [work [Hencoding ->]]].
  pose proof (audit_nat_encode_run_correct 3 4%positive encoding work Hencoding) as [_ [Hresult
    [Hwork _]]].
  assert (Hactual : audit_nat_events_work (snd (audit_nat_encode 3)) = 16) by (vm_compute;
    reflexivity).
  rewrite <- Hresult in Hactual; cbn [snd] in Hactual; unfold audit_nat_events_work in Hactual.
  exists groups, (concat query_groups), (map inl encoding); repeat split; try assumption.
  - cbn [concat] in Houter; rewrite app_nil_r in Houter; exact Houter.
  - rewrite fx_nested_test_encode_work; lia.
Qed.
