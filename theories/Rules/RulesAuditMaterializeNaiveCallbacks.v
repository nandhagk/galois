(** * Literal callback bodies for the naive total solver

    Generated queries, continuations and lattice calls have fixed source instances.
    For example, continuation receipts retain their actual ask-all capture and input value.
    Builds on: the materialization system, query and finite-powerset models. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditEncoding CollectionsAuditFinSet
  CollectionsAuditElements.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklistCallbacks FixpointAuditSchedule
  FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesAuditRelations
  RulesAuditMaterializePrelude RulesAuditMaterializeJobs RulesAuditMaterializeNaiveBodies
  RulesAuditMaterializeNaiveQuery RulesAuditMaterializePowerset RulesAuditMaterializeSystem.
Import List.ListNotations.

(** * Generated callback bodies and receipts *)

(** The internal constraint encoder expands the actual nat/predicate pair encoding. *)
Definition mat_constraint_encoder {P} (prog : program P) (c : rconstraint P) : mat_run positive :=
  mat_mark 160 (
    match c with
    | FromFact p => code <- mat_encode (penc prog) p;; mat_return (xI code)
    | FromRule i h =>
        let '(code, events) :=
          audit_pair_encode audit_nat_encode (rules_encoder (penc prog)) (i, h) in
        (xO code, MatImported _ 161 (code, events)
          (audit_pair_events_work audit_nat_events_work (@length (rules_encode_entry P)) events)
          (1 + i + Pos.size_nat code) ::
          flat_map (fun event =>
            match event with
            | AuditPairSecond p encoded _ => [MatEncode P (penc prog) p encoded]
            | _ => []
            end) events)
    end).

Definition mat_positive_body_work (events : list mat_frame) : nat :=
  fold_right (fun frame n => S (mat_frame_work frame) + n) 0 events.

Definition mat_index_source_event_work {P}
    (event : fx_index_nested_event P (rconstraint P) mat_frame) : nat :=
  match event with
  | FxiTarget _ _ body | FxiSides _ _ body | FxiDeps _ _ body => 3 + mat_positive_body_work body
  | FxiDistinctBuild _ _ body => 3 + audit_finset_source_work mat_positive_body_work body
  | FxiDistinctElements _ _ body => 3 + audit_set_elements_work body
  | FxiRead _ _ _ _ enc trie =>
      8 + mat_positive_body_work enc + audit_trie_get_trace_source_work trie
  | FxiWrite _ _ _ _ _ enc trie =>
      8 + mat_positive_body_work enc + audit_trie_update_trace_source_work trie
  | FxiCase _ => 3
  end.

Definition mat_dep_source_weight {P} (event : fx_dep_event P (rconstraint P) mat_frame) : nat :=
  16 +
    match event with
    | FxDepIndexEvent nested => mat_index_source_event_work nested
    | FxDepEncode _ _ body => mat_positive_body_work body
    | FxDepCase _ => 0
    | FxDepListWork size => 1 + size
    end.

(** A body event is either a local materialization frame or a scheduler query. *)
Inductive mat_naive_body_event (P : Type) : Type :=
  | MatNaiveLocal (event : mat_frame)
  | MatNaiveScheduleQuery
      (event : audit_rpo_schedule_event P (fx_dep_event P (rconstraint P) mat_frame)).

Arguments MatNaiveLocal {P} _.
Arguments MatNaiveScheduleQuery {P} _.

Definition mat_naive_body_weight {P} (event : mat_naive_body_event P) : nat :=
  match event with
  | MatNaiveLocal local => S (mat_frame_work local)
  | MatNaiveScheduleQuery nested => S (audit_rpo_schedule_event_work mat_dep_source_weight nested)
  end.

(** A local receipt pairs the source result with exactly its wrapped frame sequence. *)
Definition mat_local_receipt {P A} (run : mat_run A) (result : A)
    (body : list (mat_naive_body_event P)) : Prop :=
  exists local, run = (result, local) /\ body = map MatNaiveLocal local.

Section GeneratedBackend.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : mat_level_context P) (lower : database P) (k : nat)
  (cached : FinSet.t P * FinSet.t positive) (ri : Map.t nat (rule P)) (fi : database P)
  (schedule : fx_rpo_result P (rconstraint P) mat_frame).

(** Every library-owned callback is the fixed generated body at this captured source invocation. *)
Definition mat_naive_declared_source :
    fx_declared_callback_source P (rconstraint P) (relation prog facts) (mat_naive_body_event P) :=
  {|
    (** Variable encoding records the concrete predicate encoder run. *)
    fx_source_encode_x := fun x result body =>
      mat_local_receipt (mat_encode (penc prog) x) result body;
    (** Constraint encoding records the concrete tagged encoder run. *)
    fx_source_encode_c := fun c result body =>
      mat_local_receipt (mat_constraint_encoder prog c) result body;
    (** Target lookup records the generated target callback run. *)
    fx_source_target := fun c result body => mat_local_receipt (mat_target_source c) result body;
    (** Priority receipts retain the scheduler position lookup frames. *)
    fx_source_priority := fun x result body => exists local,
      audit_rpo_schedule_priority (fx_dep_encoder (mat_index_callbacks prog st k ri))
        (fx_rpo_positions schedule) x = (result, local) /\
      body = map MatNaiveScheduleQuery local;
    (** Widening-point receipts retain the scheduler head lookup frames. *)
    fx_source_widening_point := fun x result body => exists local,
      audit_rpo_schedule_widening (fx_dep_encoder (mat_index_callbacks prog st k ri))
        (fx_rpo_heads schedule) x = (result, local) /\ body = map MatNaiveScheduleQuery local;
    (** Right-hand-side receipts retain the generated query body. *)
    fx_source_rhs := fun c result body =>
      mat_local_receipt (mat_rhs_source prog facts st lower k cached ri fi c) result body;
    (** Continuation receipts retain the generated capture and its local frames. *)
    fx_source_continuation := fun native value result body => exists local,
      mat_generated_continuation_source prog facts st lower k cached ri native value result
        local /\
      body = map MatNaiveLocal local;
    (** Ordering receipts retain the finite-relation inclusion callback. *)
    fx_source_leb := fun a b result body =>
      mat_local_receipt (mat_relation_leb prog facts a b) result body;
    (** Join receipts retain the finite-relation join callback. *)
    fx_source_join := fun a b result body =>
      mat_local_receipt (mat_relation_join prog facts a b) result body;
    (** Widening receipts retain the finite-relation widening callback. *)
    fx_source_widen := fun a b result body =>
      mat_local_receipt (mat_relation_widen prog facts a b) result body |}.

(** The proposed FX source laws require the fixed cache, rule index, fact index and schedule. *)
Definition mat_naive_declared_source_laws_statement : Prop :=
  cached = fst (mat_setup_cached prog facts) -> ri = index_rules_from 0 (rules prog) ->
  fi = facts_by_pred prog facts -> schedule = mat_rpo_source prog facts st lower k ri ->
  fx_declared_source_laws (penc prog) (rconstraint_encoding (penc prog))
    (relation_lattice prog facts)
    (rpo_scheduler (penc prog) (mat_compiled_system prog facts st lower k)
      (mat_compiled_static prog facts st lower k))
    (mat_compiled_system prog facts st lower k) mat_naive_declared_source.

End GeneratedBackend.

(** The proposed weight condition requires a positive allowance for every body event. *)
Definition mat_naive_body_positive_statement : Prop :=
  forall P (event : mat_naive_body_event P),
    1 <= mat_naive_body_weight event.

(** The literal index weights are the fixed FX instance, not a separately chosen price. *)
Definition mat_index_weight_instance_statement : Prop :=
  forall P (prog : program P) st k ri event,
    mat_index_source_event_work event =
      fxi_event_work (mat_index_callback_budget prog st k ri) event.
