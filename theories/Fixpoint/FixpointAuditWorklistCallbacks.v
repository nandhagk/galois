(** * FixpointAuditWorklistCallbacks model

    Source witnesses for the actual callback occurrences in one declared-worklist run.
    Callback relations describe individual source calls and their bodies, not a whole-run
    bound or a client assertion of the desired result. The observer is mathematical and
    its evaluation cost is excluded. Concrete library-owned clients must supply their real
    source rules; source-correspondence and bounds remain future theorem obligations.
    For example, a queue pop records the callback body reached by that operation.
    Builds on: FixpointAuditWorklist and the counted collection models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditQueue.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget.
Import List.ListNotations.

Record fx_declared_callback_source (X C A B : Type) := FxDeclaredCallbackSource {
  fx_source_encode_x : X -> positive -> list B -> Prop;
  fx_source_encode_c : C -> positive -> list B -> Prop;
  fx_source_target : C -> X -> list B -> Prop;
  fx_source_priority : X -> positive -> list B -> Prop;
  fx_source_widening_point : X -> bool -> list B -> Prop;
  fx_source_rhs : C -> Query.t X A -> list B -> Prop;
  fx_source_continuation : (A -> Query.t X A) -> A -> Query.t X A -> list B -> Prop;
  fx_source_leb : A -> A -> bool -> list B -> Prop;
  fx_source_join : A -> A -> A -> list B -> Prop;
  fx_source_widen : A -> A -> A -> list B -> Prop
}.

Arguments fx_source_encode_x {X C A B} _ _ _ _.

Arguments fx_source_encode_c {X C A B} _ _ _ _.

Arguments fx_source_target {X C A B} _ _ _ _.

Arguments fx_source_priority {X C A B} _ _ _ _.

Arguments fx_source_widening_point {X C A B} _ _ _ _.

Arguments fx_source_rhs {X C A B} _ _ _ _.

Arguments fx_source_continuation {X C A B} _ _ _ _ _.

Arguments fx_source_leb {X C A B} _ _ _ _ _.

Arguments fx_source_join {X C A B} _ _ _ _ _.

Arguments fx_source_widen {X C A B} _ _ _ _ _.

Definition fx_queue_encoder_entries {C} (events : list (audit_queue_nested_event C (positive * list
  (fx_encoder_entry C)))) : list (fx_encoder_entry C) :=
  flat_map (fun event => flat_map snd (snd (snd event))) events.

(** A constraint-key queue encoding receipt satisfies the declared encoder source relation. *)
Definition fx_queue_encoder_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry C) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry c code => fx_source_encode_c source c code body
  end.

(** The recorded call's arguments and results are related to the supplied source through callback
    body witnesses or queue-entry body groups. *)
Definition fx_declared_call_source {X C A B} (source : fx_declared_callback_source X C A B)
    (call : fx_declared_call X C A) (bodies : list (list B)) : Prop :=
  match call with
  | FxTarget c result => exists body, bodies = [body] /\ fx_source_target source c result body
  | FxPriority x result => exists body, bodies = [body] /\ fx_source_priority source x result body
  | FxWideningPoint x result => exists body, bodies = [body] /\ fx_source_widening_point source x
    result body
  | FxRhs c result => exists body, bodies = [body] /\ fx_source_rhs source c result body
  | FxContinuation _ value k result => exists body, bodies = [body] /\ fx_source_continuation source
    k value result body
  | FxLeb a b result => exists body, bodies = [body] /\ fx_source_leb source a b result body
  | FxJoin a b result => exists body, bodies = [body] /\ fx_source_join source a b result body
  | FxWiden a b result => exists body, bodies = [body] /\ fx_source_widen source a b result body
  | FxGet x code _ _ _
  | FxSet x code _ _ _ _
  | FxReaders x code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxPush _ _ _ _ nested
  | FxPop _ _ nested =>
      Forall2 (fx_queue_encoder_source source) (fx_queue_encoder_entries nested) bodies
  end.

(** A callback event requires its call's source relation, while a non-call event requires an
    empty body list. *)
Definition fx_declared_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : audit_event (fx_declared_call X C A)) (bodies : list (list B)) : Prop :=
  match event with
  | AuditCall call => fx_declared_call_source source call bodies
  | _ => bodies = []
  end.

(** Declared events and their callback-body groups correspond in order. *)
Definition fx_declared_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (events : audit_trace (fx_declared_call X C A)) (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_declared_event_source source) events bodies.

Definition fx_declared_body_work {B} (weight : B -> nat) (bodies : list (list (list B))) : nat :=
  fold_right (fun event n => fold_right (fun body m => fold_right (fun x k => weight x + k) 0 body +
    m) 0 event + n) 0 bodies.

(** Reachable queries begin at a declared right-hand side and follow ask continuations or sides. *)
Inductive fx_declared_query_reachable {X C A} (S : System.t X C A) : Query.t X A -> Prop :=
  | FxReachableRhs : forall c, In c (System.constraints S) ->
      fx_declared_query_reachable S (System.rhs S c)
  | FxReachableAsk : forall x k a, fx_declared_query_reachable S (Query.Ask x k) ->
      fx_declared_query_reachable S (k a)
  | FxReachableSide : forall x a next, fx_declared_query_reachable S (Query.Side x a next) ->
      fx_declared_query_reachable S next.

(** Each encoder, target, scheduler, right-hand-side and lattice callback has a source witness,
    as does each reachable query continuation. *)

Definition fx_declared_source_laws {X C A B} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (sch : scheduler X) (S : System.t X C A)
    (source : fx_declared_callback_source X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_encode_c source c (encode EC c) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall x, exists body, fx_source_priority source x (priority sch x) body) /\
  (forall x, exists body, fx_source_widening_point source x (widening_point sch x) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall (k : A -> Query.t X A) a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body) /\
  (forall a b, exists body, fx_source_join source a b (join L a b) body) /\
  (forall a b, exists body, fx_source_widen source a b (widen L a b) body).

Record fx_declared_callback_budget (X C A B : Type) := FxDeclaredCallbackBudget {
  fx_body_weight : B -> nat;
  fx_budget_encode_x : X -> nat;
  fx_budget_encode_c : C -> nat;
  fx_budget_target : C -> nat;
  fx_budget_priority : X -> nat;
  fx_budget_widening_point : X -> nat;
  fx_budget_rhs : C -> nat;
  fx_budget_continuation : (A -> Query.t X A) -> A -> nat;
  fx_budget_leb : A -> A -> nat;
  fx_budget_join : A -> A -> nat;
  fx_budget_widen : A -> A -> nat
}.

Arguments fx_body_weight {X C A B} _ _.

Arguments fx_budget_encode_x {X C A B} _ _.

Arguments fx_budget_encode_c {X C A B} _ _.

Arguments fx_budget_target {X C A B} _ _.

Arguments fx_budget_priority {X C A B} _ _.

Arguments fx_budget_widening_point {X C A B} _ _.

Arguments fx_budget_rhs {X C A B} _ _.

Arguments fx_budget_continuation {X C A B} _ _ _.

Arguments fx_budget_leb {X C A B} _ _ _.

Arguments fx_budget_join {X C A B} _ _ _.

Arguments fx_budget_widen {X C A B} _ _ _.

Definition fx_one_body_work {B} (weight : B -> nat) (body : list B) : nat :=
  fold_right (fun e n => weight e + n) 0 body.

(** Every accepted declared callback body fits the budget associated with that callback's inputs. *)
Definition fx_declared_callback_bounded {X C A B}
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B) :
      Prop :=
  (forall x result body, fx_source_encode_x source x result body -> fx_one_body_work (fx_body_weight
    budget) body <= fx_budget_encode_x budget x) /\
  (forall c result body, fx_source_encode_c source c result body -> fx_one_body_work (fx_body_weight
    budget) body <= fx_budget_encode_c budget c) /\
  (forall c result body, fx_source_target source c result body -> fx_one_body_work (fx_body_weight
    budget) body <= fx_budget_target budget c) /\
  (forall x result body, fx_source_priority source x result body -> fx_one_body_work (fx_body_weight
    budget) body <= fx_budget_priority budget x) /\
  (forall x result body, fx_source_widening_point source x result body -> fx_one_body_work
    (fx_body_weight budget) body <= fx_budget_widening_point budget x) /\
  (forall c result body, fx_source_rhs source c result body -> fx_one_body_work (fx_body_weight
    budget) body <= fx_budget_rhs budget c) /\
  (forall k a result body, fx_source_continuation source k a result body -> fx_one_body_work
    (fx_body_weight budget) body <= fx_budget_continuation budget k a) /\
  (forall a b result body, fx_source_leb source a b result body -> fx_one_body_work (fx_body_weight
    budget) body <= fx_budget_leb budget a b) /\
  (forall a b result body, fx_source_join source a b result body -> fx_one_body_work (fx_body_weight
    budget) body <= fx_budget_join budget a b) /\
  (forall a b result body, fx_source_widen source a b result body -> fx_one_body_work
    (fx_body_weight budget) body <= fx_budget_widen budget a b).

Definition fx_queue_entry_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entry : fx_encoder_entry C) : nat :=
  match entry with
  | FxEncodeEntry c _ => fx_budget_encode_c budget c
  end.

Definition fx_declared_external_call_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (call : fx_declared_call X C A) : nat :=
  match call with
  | FxTarget c _ => fx_budget_target budget c
  | FxPriority x _ => fx_budget_priority budget x
  | FxWideningPoint x _ => fx_budget_widening_point budget x
  | FxRhs c _ => fx_budget_rhs budget c
  | FxContinuation _ a k _ => fx_budget_continuation budget k a
  | FxLeb a b _ => fx_budget_leb budget a b
  | FxJoin a b _ => fx_budget_join budget a b
  | FxWiden a b _ => fx_budget_widen budget a b
  | FxGet x _ _ _ _
  | FxSet x _ _ _ _ _
  | FxReaders x _ _ _ _ => fx_budget_encode_x budget x
  | FxPush _ _ _ _ nested
  | FxPop _ _ nested =>
      fold_right (fun entry n => fx_queue_entry_budget budget entry + n) 0 (fx_queue_encoder_entries
        nested)
  end.

Definition fx_declared_external_trace_budget {X C A B} (budget : fx_declared_callback_budget X C A
  B)
    (events : audit_trace (fx_declared_call X C A)) : nat :=
  fold_right (fun event n =>
    match event with
    | AuditCall call => fx_declared_external_call_budget budget call + n
    | _ => n
    end) 0 events.

(** Future theorem: the very same whole execution has callback-body witnesses in event
    order. Its external allowance is the sum over actual call operands, not a premise
    asserting the solver's result or its desired whole-run bound. *)

(** With index laws and declared callback source laws and bounds, the declared worklist has its
    original result, source receipts and a work bound. *)
Definition fx_declared_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S) ix fuel
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    sys_index_laws EX S SS ix ->
    fx_declared_source_laws EX EC L sch S source ->
    fx_declared_callback_bounded source budget ->
    let '(out, events) := run_worklist_declared_model EX EC L sch mode S ix fuel in
    exists bodies,
      fx_declared_trace_source source events bodies /\
      out = run_worklist EX EC L sch mode S (Declared SS ix) fuel /\
      fx_declared_model_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_declared_run_input_budget EX EC L sch mode S SS ix fuel +
          fx_declared_external_trace_budget budget events.
