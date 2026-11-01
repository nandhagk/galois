(** * Nested solver callback source receipts

    Graph, plan and machine source relations describe callback operands and body witnesses.
    For example, a non-widening update has no widening-body receipt.
    Builds on: FixpointAuditNested and the declared callback source model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphAuditDfs GraphAuditWto.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointNested FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks
  FixpointAuditScheduleWrapper FixpointAuditNestedPlan FixpointAuditNestedMachine
  FixpointAuditNested.
Import List.ListNotations.

Definition fx_nested_entries {X}
    (events : list (audit_set_event X (fx_encoder_entry X))) : list (fx_encoder_entry X) :=
  flat_map (fun event =>
    match event with
    | AuditSetAdd _ _ _ _ body _ => body
    | AuditSetMem _ _ _ _ body _ => body
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

(** The supplied encoder body satisfies the declared unknown-key source relation for its key and
    code. *)
Definition fx_nested_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry X) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry x code => fx_source_encode_x source x code body
  end.

(** Target, map and set-encoding plan events relate their bodies to their sources; other plan
    events require no bodies. *)
Definition fx_nested_plan_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_nested_plan_event X C) (bodies : list (list B)) : Prop :=
  match event with
  | FnpTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FnpMembersSet x _ code _ _ _
  | FnpTargetRead x code _ _ _
  | FnpTargetWrite x code _ _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FnpHeadsSet _ _ events =>
      Forall2 (fx_nested_entry_source source) (fx_nested_entries events) bodies
  | _ => bodies = []
  end.

(** Query, RHS, target, lattice and encoding machine events relate their bodies to their sources;
    other machine events require no bodies. *)
Definition fx_nested_machine_event_source {X C A B}
    (source : fx_declared_callback_source X C A B) (event : fx_nested_event X C A)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxNestedQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FxNestedRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FxNestedTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxNestedLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | FxNestedJoin a b out => exists body, bodies = [body] /\ fx_source_join source a b out body
  | FxNestedWiden a b out => exists body, bodies = [body] /\ fx_source_widen source a b out body
  | FxNestedMapGet x code _ _ _
  | FxNestedTargetsGet x code _ _ _
  | FxNestedValueSet x _ code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxNestedSetMem _ _ _ events
  | FxNestedSetAdd _ _ _ events
  | FxNestedSetRemove _ _ _ events =>
      Forall2 (fx_nested_entry_source source) (fx_nested_entries events) bodies
  | _ => bodies = []
  end.

(** Each graph target or encoder capture in the WTO event requires its dependency-event body to
    satisfy the supplied source relation. *)
Definition fx_nested_wto_event_source {X C B} (source : fx_index_external_source X C B)
    (event : audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B))) : Prop :=
  Forall (fun capture =>
    match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body => fx_dep_body_source source body
    | AuditGraphEncodeCapture _ _ _ _ _ body => fx_dep_body_source source body
    end) (snd event).

(** Dependency, preparation and WTO events use embedded index sources and empty body groups, plan
    and machine events use their source groups, and case events require none. *)
Definition fx_nested_whole_event_source {X C A B D}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (event : fx_nested_whole_event X C A B)
    (bodies : list (list D)) : Prop :=
  match event with
  | FnWholeDependency events => fx_dep_body_source index_source events /\ bodies = []
  | FnWholePrepare events => Forall (fx_dep_prepare_source index_source) events /\ bodies = []
  | FnWholeWto events => Forall (fx_nested_wto_event_source index_source) events /\ bodies = []
  | FnWholePlan events => exists groups,
      Forall2 (fx_nested_plan_event_source source) events groups /\ bodies = concat groups
  | FnWholeMachine events => exists groups,
      Forall2 (fx_nested_machine_event_source source) events groups /\ bodies = concat groups
  | FnWholeCase _ => bodies = []
  end.

(** Whole-run events and their callback-body groups correspond in order. *)
Definition fx_nested_trace_source {X C A B D}
    (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (events : list (fx_nested_whole_event X C A B))
    (bodies : list (list (list D))) : Prop :=
  Forall2 (fx_nested_whole_event_source index_source source) events bodies.

Definition fx_nested_entries_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entries : list (fx_encoder_entry X)) : nat :=
  fold_right (fun entry total =>
    match entry with
    | FxEncodeEntry x _ => fx_budget_encode_x budget x + total
    end) 0 entries.

Definition fx_nested_plan_external_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (event : fx_nested_plan_event X C) : nat :=
  match event with
  | FnpTarget c _ => fx_budget_target budget c
  | FnpMembersSet x _ _ _ _ _
  | FnpTargetRead x _ _ _ _
  | FnpTargetWrite x _ _ _ _ _ => fx_budget_encode_x budget x
  | FnpHeadsSet _ _ events => fx_nested_entries_budget budget (fx_nested_entries events)
  | _ => 0
  end.

Definition fx_nested_machine_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_nested_event X C A) : nat :=
  match event with
  | FxNestedQuery events => fx_declared_external_trace_budget budget events
  | FxNestedRhs c _ => fx_budget_rhs budget c
  | FxNestedTarget c _ => fx_budget_target budget c
  | FxNestedLeb a b _ => fx_budget_leb budget a b
  | FxNestedJoin a b _ => fx_budget_join budget a b
  | FxNestedWiden a b _ => fx_budget_widen budget a b
  | FxNestedMapGet x _ _ _ _
  | FxNestedTargetsGet x _ _ _ _
  | FxNestedValueSet x _ _ _ _ _ => fx_budget_encode_x budget x
  | FxNestedSetMem _ _ _ events
  | FxNestedSetAdd _ _ _ events
  | FxNestedSetRemove _ _ _ events => fx_nested_entries_budget budget (fx_nested_entries events)
  | _ => 0
  end.

Definition fx_nested_external_trace_budget {X C A B D}
    (budget : fx_declared_callback_budget X C A D) (events : list (fx_nested_whole_event X C A
  B)) : nat :=
  fold_right (fun event total => total +
    match event with
    | FnWholePlan plan => fold_right (fun e n => fx_nested_plan_external_budget budget e + n) 0 plan
    | FnWholeMachine machine =>
        fold_right (fun e n => fx_nested_machine_external_budget budget e + n) 0 machine
    | _ => 0
    end) 0 events.

(** Encoder, target, right-hand-side, reachable continuation and lattice callbacks have source
    witnesses and bounded bodies. *)

Definition fx_nested_machine_source_laws {X C A D} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall k a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body) /\
  (forall a b, exists body, fx_source_join source a b (join L a b) body) /\
  (forall a b, exists body, fx_source_widen source a b (widen L a b) body) /\
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) /\
  (forall c out body, fx_source_rhs source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_rhs budget c) /\
  (forall k a out body, fx_source_continuation source k a out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_continuation budget k a) /\
  (forall a b out body, fx_source_leb source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_leb budget a b) /\
  (forall a b out body, fx_source_join source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_join budget a b) /\
  (forall a b out body, fx_source_widen source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_widen budget a b).

(** The same execution has source receipts and a phase bound plus per-invocation bodies. *)

(** With index erasure and bounds and dependency and machine source laws, nested execution
    returns its original result, source receipts and a work bound. *)
Definition fx_nested_external_source_statement : Prop :=
  forall X C A B D (EX : encoding X) (EC : encoding C) (L : lattice A) mode
    (S : System.t X C A) (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    fuel,
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
    fx_dep_source_laws cb index_source -> fx_nested_machine_source_laws EX L S source budget ->
    let '(out, events) := fx_nested_run_counted EX L mode S SS cb fuel in
    exists bodies, fx_nested_trace_source index_source source events bodies /\
      out = nested_run EX EC L mode S SS fuel /\
      fx_nested_whole_work EC ib events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_nested_run_input_budget EX L mode S SS ib fuel + fx_nested_external_trace_budget
  budget events.
