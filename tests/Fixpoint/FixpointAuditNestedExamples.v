(** * Counted nested solver observations

    These examples exercise the parser and counted machine on small inputs.
    For example, a malformed closing token stops parsing before the trailing vertex.
    Builds on: FixpointFIX5 and the nested audit models. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditEncoding CollectionsAuditEncodingAdequacy
  CollectionsAuditEncoderBudget.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphWto.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointNested
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks
    FixpointAuditScheduleWrapper
  FixpointAuditNestedPlan FixpointAuditNestedMachine FixpointAuditNested
    FixpointAuditNestedCallbacks
  FixpointAuditNestedCallbacksAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointFIX5.
Import List.ListNotations.

(** A component body and its following sibling retain their order. *)
Example fx_nested_plan_component :
  fst (@fx_nested_tree nat nat [WOpen 1; WVertex 2; WClose; WVertex 3]) =
    NestedComponent 1 (NestedVisit 2 NestedEnd) (NestedVisit 3 NestedEnd).
Proof.
  vm_compute; reflexivity.
Qed.

(** An unmatched closing token terminates the current parse immediately. *)
Example fx_nested_plan_malformed :
  fst (@fx_nested_tree nat nat [WClose; WVertex 3]) = NestedEnd.
Proof.
  vm_compute; reflexivity.
Qed.

(** Zero parser fuel preserves the unconsumed token stream. *)
Example fx_nested_parse_zero :
  fst (@fx_nested_parse nat nat 0 [WVertex 3]) = (NestedEnd, [WVertex 3]).
Proof.
  reflexivity.
Qed.

(** The empty tree contains no heads. *)
Example fx_nested_heads_empty : fst (@fx_nested_heads nat nat NestedEnd) = [].
Proof.
  reflexivity.
Qed.

(** Joining and widening use distinct callbacks at a component head. *)
Example fx_nested_raise_modes :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  fst (fx_nested_raise nat_encoding nested_test_lattice plan Joining 1 TestBottom TestMiddle) =
    TestMiddle /\
  fst (fx_nested_raise nat_encoding nested_test_lattice plan Widening 1 TestBottom TestMiddle) =
    TestTop.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A completed empty machine preserves its empty assignment at one fuel unit. *)
Example fx_nested_empty_loop :
  let plan := nested_prepare nat_encoding nested_test_empty nested_test_empty_static in
  fst (fx_nested_loop nat_encoding nested_test_lattice plan Joining nested_test_empty 1
    (nested_start plan)) = inr Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

(** A nonempty cycle remains pending with only one transition. *)
Example fx_nested_cycle_fuel_boundary :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  match fst (fx_nested_loop nat_encoding nested_test_lattice plan Joining nested_test_cycle 1
    (nested_start plan)) with
  | inl _ => true
  | inr _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** * A nonempty same-execution callback client *)

Definition fx_nested_client_cycle : System.t nat nat nested_test_value :=
  System.Make [3] (fun c => c) (fun _ => Query.Ask 3 Query.Ret).

Definition fx_nested_client_static : System.static fx_nested_client_cycle.
Proof.
  refine (System.Static (fun _ => [3]) (fun _ => []) _ _);
    intros c assignment x Hin; exact Hin.
Defined.

Definition fx_nested_client_lattice : lattice nested_test_value :=
  {| leb := fun _ _ => false;
      bot := TestBottom;
      join := fun _ value => value;
      widen := fun _ value => value;
      narrow := fun value _ => value |}.

Definition fx_nested_test_weight (event : audit_nat_encoding_event + unit) : nat :=
  match event with
  | inl _ => 2
  | inr _ => 1
  end.

Definition fx_nested_test_encode x : positive * list (audit_nat_encoding_event + unit) :=
  let '(code, events) := audit_nat_encode x in (code, map inl events).

Definition fx_nested_test_encode_source x code
    (body : list (audit_nat_encoding_event + unit)) : Prop :=
  exists events work, audit_nat_encode_run x code events work /\ body = map inl events.

Definition fx_nested_test_index_callbacks :
    fx_index_external_model nat nat (audit_nat_encoding_event + unit) :=
  FxIndexExternalModel nat nat (audit_nat_encoding_event + unit)
    fx_nested_test_encode
    (fun c => (System.target fx_nested_client_cycle c, [inr tt]))
    (fun c => (side_targets fx_nested_client_static c, [inr tt]))
    (fun c => (deps fx_nested_client_static c, [inr tt])).

Definition fx_nested_test_index_budget :
    fx_index_external_budget nat nat (audit_nat_encoding_event + unit) :=
  FxIndexExternalBudget nat nat (audit_nat_encoding_event + unit) fx_nested_test_weight
    audit_nat_input_budget (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition fx_nested_test_index_source :
    fx_index_external_source nat nat (audit_nat_encoding_event + unit) :=
  FxIndexExternalSource nat nat (audit_nat_encoding_event + unit)
    fx_nested_test_encode_source
    (fun c out body => out = System.target fx_nested_client_cycle c /\ body = [inr tt])
    (fun c out body => out = side_targets fx_nested_client_static c /\ body = [inr tt])
    (fun c out body => out = deps fx_nested_client_static c /\ body = [inr tt]).

Definition fx_nested_test_source :
    fx_declared_callback_source nat nat nested_test_value (audit_nat_encoding_event + unit) :=
  FxDeclaredCallbackSource nat nat nested_test_value (audit_nat_encoding_event + unit)
    fx_nested_test_encode_source
    (fun _ _ _ => False)
    (fun c out body => out = System.target fx_nested_client_cycle c /\ body = [inr tt])
    (fun _ _ _ => False)
    (fun _ _ _ => False)
    (fun c out body => out = System.rhs fx_nested_client_cycle c /\ body = [inr tt])
    (fun k a out body => k = @Query.Ret nat nested_test_value /\
      out = Query.Ret a /\ body = [inr tt])
    (fun a b out body => out = leb fx_nested_client_lattice a b /\ body = [inr tt])
    (fun a b out body => out = join fx_nested_client_lattice a b /\ body = [inr tt])
    (fun a b out body => out = widen fx_nested_client_lattice a b /\ body = [inr tt]).

Definition fx_nested_test_budget :
    fx_declared_callback_budget nat nat nested_test_value (audit_nat_encoding_event + unit) :=
  FxDeclaredCallbackBudget nat nat nested_test_value (audit_nat_encoding_event + unit)
    fx_nested_test_weight audit_nat_input_budget (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1).

Lemma fx_nested_test_index_erases :
  fx_index_external_erases nat_encoding fx_nested_client_cycle fx_nested_client_static
    fx_nested_test_index_callbacks.
Proof.
  unfold fx_index_external_erases; repeat split; intros; try reflexivity.
  unfold fx_nested_test_index_callbacks, fx_nested_test_encode; cbn [fxi_encode].
  destruct (audit_nat_encode x) as [code events] eqn:Hrun.
  pose proof (audit_nat_encode_erases x) as Herase; rewrite Hrun in Herase; exact Herase.
Qed.

Lemma fx_nested_test_encode_work events :
  fx_one_body_work fx_nested_test_weight (map inl events) = 2 * length events.
Proof.
  induction events as [|event rest IH].
  - reflexivity.
  - change (2 + fx_one_body_work fx_nested_test_weight (map inl rest) =
      2 * S (length rest)).
    rewrite IH; lia.
Qed.

Lemma fx_nested_test_encode_source_total x :
  exists body, fx_nested_test_encode_source x (encode nat_encoding x) body.
Proof.
  destruct (audit_nat_encode_run_total x) as [code [events [work Hrun]]].
  pose proof (audit_nat_encode_run_correct x code events work Hrun) as [Hcode _].
  subst code; exists (map inl events), events, work; auto.
Qed.

Lemma fx_nested_test_encode_source_bound x code body :
  fx_nested_test_encode_source x code body ->
  fx_one_body_work fx_nested_test_weight body <= audit_nat_input_budget x.
Proof.
  intros [events [work [Hrun ->]]].
  pose proof (audit_nat_encode_run_correct x code events work Hrun) as [_ [_ [Hwork Hbound]]].
  rewrite fx_nested_test_encode_work, <- Hwork; exact Hbound.
Qed.

(** Encoding three records unary frames and the two-frame positive carry. *)
Example fx_nested_test_encoder_carry :
  fx_nested_test_encode 3 =
    (4%positive,
      [inl (AuditNatFrame 3); inl (AuditNatFrame 2); inl (AuditNatFrame 1);
      inl (AuditNatFrame 0); inl (AuditPositiveSuccFrame 1 2);
      inl (AuditPositiveSuccFrame 2 3); inl (AuditPositiveSuccFrame 3 4);
      inl (AuditPositiveSuccFrame 1 2)]).
Proof.
  vm_compute; reflexivity.
Qed.

(** The actual carry receipt costs sixteen source-frame units rather than one. *)
Example fx_nested_test_encoder_carry_work :
  fx_one_body_work fx_nested_test_weight (snd (fx_nested_test_encode 3)) = 16.
Proof.
  vm_compute; reflexivity.
Qed.

(** The machine encoder relation accepts the same source-indexed carry derivation. *)
Example fx_nested_test_encoder_source_receipt :
  fx_source_encode_x fx_nested_test_source 3 (fst (fx_nested_test_encode 3))
    (snd (fx_nested_test_encode 3)).
Proof.
  destruct (audit_nat_encode_run_total 3) as [code [events [work Hrun]]].
  pose proof (audit_nat_encode_run_correct 3 code events work Hrun) as [_ [Hrun_eq _]].
  unfold fx_nested_test_source, fx_nested_test_encode; cbn [fx_source_encode_x].
  rewrite <- Hrun_eq; cbn; exists events, work; auto.
Qed.

(** The cyclic index execution retains the carry frame at a real trie-read call. *)
Example fx_nested_test_index_carry_receipt :
  let '(_, _, events) := fx_dep_graph_build nat_encoding fx_nested_client_cycle
    fx_nested_client_static fx_nested_test_index_callbacks in
  existsb (fun event =>
    match event with
    | FxDepIndexEvent (FxiRead 3 4%positive _ _ body _) =>
      existsb (fun item =>
        match item with
        | inl (AuditPositiveSuccFrame 3 4) => true
        | _ => false
        end) body
    | _ => false
    end) events = true.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma fx_nested_test_index_bounded :
  fx_index_external_bounded fx_nested_test_index_callbacks fx_nested_test_index_budget.
Proof.
  unfold fx_index_external_bounded; repeat split.
  - intros [event|[]]; cbn [fx_nested_test_index_budget fx_nested_test_weight fxi_body_weight]; lia.
  - intro x; unfold fx_nested_test_index_callbacks, fx_nested_test_encode,
      fx_nested_test_index_budget, fxi_body_work; cbn [fxi_encode fxi_encode_bound fxi_body_weight].
    destruct (audit_nat_encode x) as [code events] eqn:Hrun; cbn [snd].
    change (fx_one_body_work fx_nested_test_weight (map inl events) <= audit_nat_input_budget x).
    destruct (audit_nat_encode_run_total x) as [out [body [work Hbody]]].
    pose proof (audit_nat_encode_run_correct x out body work Hbody) as [_ [Hcounted _]].
    rewrite Hrun in Hcounted; inversion Hcounted; subst body out.
    apply fx_nested_test_encode_source_bound with (code := code).
    exists events, work; auto.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
Qed.

Lemma fx_nested_test_index_source_laws :
  fx_dep_source_laws fx_nested_test_index_callbacks fx_nested_test_index_source.
Proof.
  unfold fx_dep_source_laws; repeat split; intros.
  - destruct (audit_nat_encode_run_total x) as [code [events [work Hrun]]].
    pose proof (audit_nat_encode_run_correct x code events work Hrun) as [_ [Hcounted _]].
    unfold fx_nested_test_index_callbacks, fx_nested_test_index_source, fx_nested_test_encode;
      cbn [fxi_encode fxi_encode_source]; rewrite <- Hcounted; cbn.
    exists events, work; auto.
Qed.

Lemma fx_nested_client_reachable q : fx_declared_query_reachable fx_nested_client_cycle q ->
  q = Query.Ask 3 Query.Ret \/ exists a, q = Query.Ret a.
Proof.
  intro Hreachable; induction Hreachable as [c Hin|x k a Hask IH|x a next Hside IH].
  - left; reflexivity.
  - destruct IH as [Hask_shape|[result Hask_shape]].
    + inversion Hask_shape; subst k; right; eauto.
    + discriminate Hask_shape.
  - destruct IH as [Hside_shape|[result Hside_shape]]; discriminate Hside_shape.
Qed.

Lemma fx_nested_client_continuation x k :
  fx_declared_query_reachable fx_nested_client_cycle (Query.Ask x k) ->
  k = @Query.Ret nat nested_test_value.
Proof.
  intro Hreachable; destruct (fx_nested_client_reachable _ Hreachable) as [Hask|[a Hret]].
  - now inversion Hask.
  - discriminate Hret.
Qed.

Lemma fx_nested_test_machine_source_laws :
  fx_nested_machine_source_laws nat_encoding fx_nested_client_lattice fx_nested_client_cycle
    fx_nested_test_source fx_nested_test_budget.
Proof.
  unfold fx_nested_machine_source_laws; repeat split; intros;
    try solve [apply fx_nested_test_encode_source_total];
    try solve [apply fx_nested_test_encode_source_bound; exact H];
    cbv [fx_nested_test_source fx_nested_test_budget fx_source_encode_x fx_source_target
      fx_source_rhs
      fx_source_continuation fx_source_leb fx_source_join fx_source_widen
      fx_budget_target fx_budget_rhs fx_budget_continuation fx_budget_leb fx_budget_join
      fx_budget_widen fx_budget_encode_x fx_body_weight] in *;
    try solve [exists [inr tt]; split; reflexivity];
    try solve [destruct H as [x Hreachable];
      pose proof (fx_nested_client_continuation x k Hreachable) as Hk;
      subst k; exists [inr tt]; repeat split; reflexivity];
    try solve [apply fx_nested_test_encode_source_bound; exact H];
    try (destruct H as [_ Hbody]; destruct Hbody as [_ Hbody] || idtac;
      subst body; reflexivity).
  all: eapply fx_nested_test_encode_source_bound; exact H.
Qed.

Definition fx_nested_test_phase_nonempty (event : fx_nested_whole_event nat nat nested_test_value
  (audit_nat_encoding_event + unit))
    : bool :=
  match event with
  | FnWholeDependency events => negb (Nat.eqb (length events) 0)
  | FnWholePrepare events => negb (Nat.eqb (length events) 0)
  | FnWholeWto events => negb (Nat.eqb (length events) 0)
  | FnWholePlan events => negb (Nat.eqb (length events) 0)
  | FnWholeMachine events => negb (Nat.eqb (length events) 0)
  | FnWholeCase _ => true
  end.

(** Every phase of the nonempty cyclic run retains an actual nonempty trace. *)
Example fx_nested_cycle_counted_phases :
  let '(out, events) := fx_nested_run_counted nat_encoding fx_nested_client_lattice Joining
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 1 in
  out = None /\ map fx_nested_test_phase_nonempty events = [true; true; true; true; true; true].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The concrete callback client supplies source receipts for that same cyclic execution. *)
Example fx_nested_cycle_callback_receipts :
  let '(out, events) := fx_nested_run_counted nat_encoding fx_nested_client_lattice Joining
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 1 in
  exists bodies, fx_nested_trace_source fx_nested_test_index_source fx_nested_test_source events
    bodies /\
    out = nested_run nat_encoding nat_encoding fx_nested_client_lattice Joining
      fx_nested_client_cycle
      fx_nested_client_static 1 /\
    fx_nested_whole_work nat_encoding fx_nested_test_index_budget events +
      fx_declared_body_work (fx_body_weight fx_nested_test_budget) bodies <=
    fx_nested_run_input_budget nat_encoding fx_nested_client_lattice Joining fx_nested_client_cycle
      fx_nested_client_static fx_nested_test_index_budget 1 +
      fx_nested_external_trace_budget fx_nested_test_budget events.
Proof.
  apply fx_nested_external_source; [apply fx_nested_test_index_erases|apply
    fx_nested_test_index_bounded|
    apply fx_nested_test_index_source_laws|apply fx_nested_test_machine_source_laws].
Qed.

Definition fx_nested_test_is_join (event : fx_nested_event nat nat nested_test_value) : bool :=
  match event with
  | FxNestedJoin _ _ _ => true
  | _ => false
  end.

Definition fx_nested_test_is_widen (event : fx_nested_event nat nat nested_test_value) : bool :=
  match event with
  | FxNestedWiden _ _ _ => true
  | _ => false
  end.

Definition fx_nested_test_is_mark (event : fx_nested_event nat nat nested_test_value) : bool :=
  match event with
  | FxNestedSetAdd _ _ _ _ => true
  | _ => false
  end.

Definition fx_nested_test_is_remove (event : fx_nested_event nat nat nested_test_value) : bool :=
  match event with
  | FxNestedSetRemove _ _ _ _ => true
  | _ => false
  end.

(** Changed updates join and mark enclosing components, while an unchanged update does neither. *)
Example fx_nested_update_changed_and_unchanged :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  let state := nested_start plan in
  let changed := snd (fx_nested_update nat_encoding nested_test_lattice plan Joining (2,
    TestMiddle) state) in
  let unchanged := snd (fx_nested_update nat_encoding nested_test_lattice plan Joining (2,
    TestBottom) state) in
  (existsb fx_nested_test_is_join changed, existsb fx_nested_test_is_mark changed,
    existsb fx_nested_test_is_join unchanged, existsb fx_nested_test_is_mark unchanged) =
    (true, true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** Widening uses widening at a head and a join at a non-head. *)
Example fx_nested_update_widening_branches :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  let state := nested_start plan in
  let head := snd (fx_nested_update nat_encoding nested_test_lattice plan Widening (1, TestMiddle)
    state) in
  let nonhead := snd (fx_nested_update nat_encoding nested_test_lattice plan Widening (0,
    TestMiddle) state) in
  (existsb fx_nested_test_is_widen head, existsb fx_nested_test_is_join nonhead) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** Entering a component removes its head from the dirty set. *)
Example fx_nested_component_entry_receipt :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  let state := NestedState.Make Map.empty []
    [NestedFrame.Make (NestedComponent 1 NestedEnd NestedEnd) None] FinSet.empty false in
  existsb fx_nested_test_is_remove
    (snd (fx_nested_step nat_encoding nested_test_lattice plan Joining nested_test_cycle state)) =
      true.
Proof.
  vm_compute; reflexivity.
Qed.

(** A restarted dirty component clears its head; a clean component has no removal. *)
Example fx_nested_restart_dirty_and_clean :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  let frame := NestedFrame.Make NestedEnd (Some (1, NestedVisit 1 NestedEnd)) in
  let dirty := NestedState.Make Map.empty [] [frame] (FinSet.add nat_encoding 1 FinSet.empty)
    false in
  let clean := NestedState.Make Map.empty [] [frame] FinSet.empty false in
  (existsb fx_nested_test_is_remove
      (snd (fx_nested_step nat_encoding nested_test_lattice plan Joining nested_test_cycle dirty)),
    existsb fx_nested_test_is_remove
      (snd (fx_nested_step nat_encoding nested_test_lattice plan Joining nested_test_cycle
        clean))) =
    (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition fx_nested_test_query_continuation (event : fx_nested_event nat nat nested_test_value) :
  bool :=
  match event with
  | FxNestedQuery events =>
    existsb (fun event =>
      match event with
      | AuditCall (FxContinuation _ _ _ _) => true
      | _ => false
      end) events
  | _ => false
  end.

Definition fx_nested_test_query_side (event : fx_nested_event nat nat nested_test_value) : bool :=
  match event with
  | FxNestedQuery events =>
    existsb (fun event =>
      match event with
      | AuditConstruct 1 _ => true
      | _ => false
      end) events
  | _ => false
  end.

(** A ready query retains its actual continuation call and side-contribution branch. *)
Example fx_nested_query_continuation_and_side :
  let plan := nested_prepare nat_encoding nested_test_side nested_test_side_static in
  let read_state := NestedState.Make Map.empty [1] [] FinSet.empty false in
  let side_state := NestedState.Make Map.empty [0] [] FinSet.empty false in
  (existsb fx_nested_test_query_continuation
      (snd (fx_nested_step nat_encoding nested_test_lattice plan Joining nested_test_side
        read_state)),
    existsb fx_nested_test_query_side
      (snd (fx_nested_step nat_encoding nested_test_lattice plan Joining nested_test_side
        side_state))) =
    (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition fx_nested_test_empty_callbacks :
    fx_index_external_model nat nat (audit_nat_encoding_event + unit) :=
  FxIndexExternalModel nat nat (audit_nat_encoding_event + unit)
    fx_nested_test_encode
    (fun c => (System.target nested_test_empty c, [inr tt]))
    (fun c => (side_targets nested_test_empty_static c, [inr tt]))
    (fun c => (deps nested_test_empty_static c, [inr tt])).

(** The whole empty system completes at the exact one-unit fuel boundary. *)
Example fx_nested_empty_counted :
  fst (fx_nested_run_counted nat_encoding nested_test_lattice Joining nested_test_empty
    nested_test_empty_static fx_nested_test_empty_callbacks 1) = Some Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

(** Both binary-fuel branches preserve a pending result on the nonempty cycle. *)
Example fx_nested_binary_fuel_branches :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  let state := nested_start plan in
  (
    match fst (fx_nested_loop nat_encoding nested_test_lattice plan Joining nested_test_cycle 2
      state) with
    | inl _ => true
    | inr _ => false
    end,
    match fst (fx_nested_loop nat_encoding nested_test_lattice plan Joining nested_test_cycle 3
      state) with
    | inl _ => true
    | inr _ => false
    end
  ) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition fx_nested_test_whole_continuation
    (event : fx_nested_whole_event nat nat nested_test_value (audit_nat_encoding_event + unit)) :
    bool :=
  match event with
  | FnWholeMachine events => existsb fx_nested_test_query_continuation events
  | _ => false
  end.

(** Both portfolios retain an actual query continuation in the complete cyclic phase trace. *)
Example fx_nested_cycle_whole_query_branches :
  let joining := snd (fx_nested_run_counted nat_encoding fx_nested_client_lattice Joining
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 12) in
  let widening := snd (fx_nested_run_counted nat_encoding fx_nested_client_lattice Widening
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 12) in
  (existsb fx_nested_test_whole_continuation joining,
    existsb fx_nested_test_whole_continuation widening) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition fx_nested_test_whole_write_three
    (event : fx_nested_whole_event nat nat nested_test_value (audit_nat_encoding_event + unit)) :
    bool :=
  match event with
  | FnWholeMachine events =>
    existsb (fun event =>
      match event with
      | FxNestedValueSet 3 _ 4%positive _ _ _ => true
      | _ => false
      end) events
  | _ => false
  end.

(** Both actual machine executions encode the nontrivial key at a write. *)
Example fx_nested_cycle_whole_machine_encode_three :
  let joining := snd (fx_nested_run_counted nat_encoding fx_nested_client_lattice Joining
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 12) in
  let widening := snd (fx_nested_run_counted nat_encoding fx_nested_client_lattice Widening
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 12) in
  (existsb fx_nested_test_whole_write_three joining,
    existsb fx_nested_test_whole_write_three widening) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** The two portfolios execute their respective lattice callbacks on this cycle. *)
Example fx_nested_cycle_whole_join_and_widen :
  let joining := snd (fx_nested_run_counted nat_encoding fx_nested_client_lattice Joining
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 12) in
  let widening := snd (fx_nested_run_counted nat_encoding fx_nested_client_lattice Widening
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 12) in
  let has_event test events := existsb (fun event =>
    match event with
    | FnWholeMachine machine => existsb test machine
    | _ => false
    end) events in
  (has_event fx_nested_test_is_join joining, has_event fx_nested_test_is_widen widening) =
    (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** The widening cycle's actual query execution also has the specified callback receipts. *)
Example fx_nested_cycle_widening_callback_receipts :
  let '(out, events) := fx_nested_run_counted nat_encoding fx_nested_client_lattice Widening
    fx_nested_client_cycle fx_nested_client_static fx_nested_test_index_callbacks 12 in
  exists bodies, fx_nested_trace_source fx_nested_test_index_source fx_nested_test_source events
    bodies /\
    out = nested_run nat_encoding nat_encoding fx_nested_client_lattice Widening
      fx_nested_client_cycle
      fx_nested_client_static 12 /\
    fx_nested_whole_work nat_encoding fx_nested_test_index_budget events +
      fx_declared_body_work (fx_body_weight fx_nested_test_budget) bodies <=
    fx_nested_run_input_budget nat_encoding fx_nested_client_lattice Widening fx_nested_client_cycle
      fx_nested_client_static fx_nested_test_index_budget 12 +
      fx_nested_external_trace_budget fx_nested_test_budget events.
Proof.
  apply fx_nested_external_source; [apply fx_nested_test_index_erases|apply
    fx_nested_test_index_bounded|
    apply fx_nested_test_index_source_laws|apply fx_nested_test_machine_source_laws].
Qed.
