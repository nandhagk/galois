(** * Complete declared-worklist atomic model

    This model fixes the execution equations for the complete fuel worklist
    operation with declared dependencies. For example, exhausted fuel returns None without
    inventing an additional empty-pop probe. External dictionary bodies have entry charges;
    their recursive implementation costs require their separately certified adapters.
    Builds on: FixpointWorklist, CollectionsAuditQueue and CostVocabulary. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsHeap CollectionsAuditQueue.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointTotal.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

Inductive fx_encoder_entry (X : Type) := FxEncodeEntry (key : X) (code : positive).

Arguments FxEncodeEntry {X} _ _.

Definition fx_index_encoder {X} (EX : encoding X) (x : X) : positive * list (fx_encoder_entry X) :=
  let code := encode EX x in (code, [FxEncodeEntry x code]).

(** Actual typed operands and results identify every external entry and internal primitive. *)

Inductive fx_declared_call (X C A : Type) : Type :=
  | FxTarget (constraint : C) (result : X)
  | FxPriority (unknown : X) (result : positive)
  | FxWideningPoint (unknown : X) (result : bool)
  | FxRhs (constraint : C) (result : Query.t X A)
  | FxContinuation (unknown : X) (value : A) (continuation : A -> Query.t X A)
      (result : Query.t X A)
  | FxLeb (left right : A) (result : bool)
  | FxJoin (left right result : A)
  | FxWiden (left right result : A)
  | FxGet (unknown : X) (code : positive) (before : assignment X A) (raw : option A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxSet (unknown : X) (code : positive) (value : A) (before after : assignment X A)
      (body : audit_trace (audit_trie_call (X * A)))
  | FxReaders (unknown : X) (code : positive) (before : Map.t X (list C))
      (raw : option (list C)) (body : audit_trace (audit_trie_call (X * list C)))
  | FxPush (priority : positive) (constraint : C) (before after : PQueue.t C)
      (body : list (audit_queue_nested_event C (positive * list (fx_encoder_entry C))))
  | FxPop (before : PQueue.t C) (result : option (positive * C * PQueue.t C))
      (body : list (audit_queue_nested_event C (positive * list (fx_encoder_entry C)))).

Arguments FxTarget {X C A} _ _.

Arguments FxPriority {X C A} _ _.

Arguments FxWideningPoint {X C A} _ _.

Arguments FxRhs {X C A} _ _.

Arguments FxContinuation {X C A} _ _ _ _.

Arguments FxLeb {X C A} _ _ _.

Arguments FxJoin {X C A} _ _ _.

Arguments FxWiden {X C A} _ _ _.

Arguments FxGet {X C A} _ _ _ _ _.

Arguments FxSet {X C A} _ _ _ _ _ _.

Arguments FxReaders {X C A} _ _ _ _ _.

Arguments FxPush {X C A} _ _ _ _ _.

Arguments FxPop {X C A} _ _ _.

Definition fx_queue_internal_charge {C B} (_ : encoding C)
    (body : list (audit_queue_nested_event C (positive * list B))) : nat :=
  audit_queue_recorded_internal_source_work body.

Section DeclaredModel.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

(** Lookup retains its single actual encoding and the missing-entry branch. *)

Definition fx_model_lookup (values : assignment X A) (x : X) :
    A * audit_trace (fx_declared_call X C A) :=
  let code := encode EX x in
  let '(raw, body) := audit_map_code_get code values in
  (
    match raw with
    | Some a => a
    | None => bot L
    end,
   [AuditCall (FxGet x code values raw body); AuditCase 0 []]).

(** The actual query continuation and assignment lookup execute once per Ask occurrence. *)

Fixpoint fx_model_query (q : Query.t X A) (values : assignment X A) :
    (A * list X * list (X * A)) * audit_trace (fx_declared_call X C A) :=
  match q with
  | Query.Ret a =>
      ((a, [], []), [AuditCase 1 []])
  | Query.Ask x k =>
      let '(value, lookup_events) := fx_model_lookup values x in
      let next := k value in
      let '(result, body) := fx_model_query next values in
      let '(a, reads, sides) := result in
      ((a, x :: reads, sides), [AuditCase 1 []] ++ lookup_events ++
        [AuditCall (FxContinuation x value k next)] ++ body ++ [AuditConstruct 0 []])
  | Query.Side x a next =>
      let '(result, body) := fx_model_query next values in
      let '(r, reads, sides) := result in
      ((r, reads, (x, a) :: sides), [AuditCase 1 []] ++ body ++ [AuditConstruct 1 []])
  end.

(** Left-fold enqueue retains each target, priority and actual persistent queue subrun. *)

Fixpoint fx_model_enqueue (constraints : list C) (queue : PQueue.t C) :
    PQueue.t C * audit_trace (fx_declared_call X C A) :=
  match constraints with
  | [] =>
      (queue, [AuditCase 2 []])
  | c :: rest =>
      let x := System.target S c in
      let p := priority sch x in
      let '(next, queue_events) := audit_queue_recorded_push (fx_index_encoder EC) p c queue in
      let '(out, tail) := fx_model_enqueue rest next in
      (out, [AuditCase 2 []; AuditCall (FxTarget c x); AuditCall (FxPriority x p);
        AuditCall (FxPush p c queue next queue_events)] ++ tail)
  end.

(** The selected join/widen branch follows the original mode and scheduler. *)

Definition fx_model_raise (x : X) (old value : A) :
    A * audit_trace (fx_declared_call X C A) :=
  match mode with
  | Joining =>
      let result := join L old value in
      (result, [AuditCase 3 []; AuditCall (FxJoin old value result)])
  | Widening =>
      let point := widening_point sch x in
      if point then
        let result := widen L old value in
        (result, [AuditCase 3 []; AuditCall (FxWideningPoint x point); AuditCase 11 [];
          AuditCall (FxWiden old value result)])
      else
        let result := join L old value in
        (result, [AuditCase 3 []; AuditCall (FxWideningPoint x point); AuditCase 11 [];
          AuditCall (FxJoin old value result)])
  end.

(** Unchanged updates perform one lookup and comparison and no reader lookup or enqueue. *)

Definition fx_model_update (xa : X * A) (mq : assignment X A * PQueue.t C) :
    (assignment X A * PQueue.t C) * audit_trace (fx_declared_call X C A) :=
  let '(values, queue) := mq in
  let '(x, value) := xa in
  let '(old, lookup_events) := fx_model_lookup values x in
  let unchanged := leb L value old in
  if unchanged then
    ((values, queue), lookup_events ++ [AuditCall (FxLeb value old unchanged); AuditCase 4 []])
  else
    let '(raised, raise_events) := fx_model_raise x old value in
    let write_code := encode EX x in
    let '(next_values, write_body) := audit_trie_set write_code (x, raised) values in
    let reader_code := encode EX x in
    let '(raw, reader_body) := audit_map_code_get reader_code (readers ix) in
    let constraints :=
      match raw with
      | Some cs => cs
      | None => []
      end in
    let '(next_queue, enqueue_events) := fx_model_enqueue constraints queue in
    ((next_values, next_queue), lookup_events ++
      [AuditCall (FxLeb value old unchanged); AuditCase 4 []] ++ raise_events ++
      [AuditCall (FxSet x write_code raised values next_values write_body);
       AuditCall (FxReaders x reader_code (readers ix) raw reader_body); AuditCase 5 []] ++
      enqueue_events).

(** Target and side updates use the actual left-fold intermediate assignment and queue. *)

Fixpoint fx_model_updates (updates : list (X * A)) (mq : assignment X A * PQueue.t C) :
    (assignment X A * PQueue.t C) * audit_trace (fx_declared_call X C A) :=
  match updates with
  | [] =>
      (mq, [AuditCase 6 []])
  | update :: rest =>
      let '(next, head) := fx_model_update update mq in
      let '(out, tail) := fx_model_updates rest next in
      (out, [AuditCase 6 []] ++ head ++ tail)
  end.

(** A successful pop invokes exactly one rhs, one query run and its target-plus-side updates. *)

Definition fx_model_step (state : Engine.t X C A) :
    outcome X C A * audit_trace (fx_declared_call X C A) :=
  let '(popped, pop_events) := audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state)
    in
  let prefix := [AuditCall (FxPop (Engine.queue state) popped pop_events); AuditCase 7 []] in
  match popped with
  | None =>
      (Done (Engine.current state), prefix)
  | Some (_, c, queue) =>
      let rhs := System.rhs S c in
      let '(result, query_events) := fx_model_query rhs (Engine.current state) in
      let '(value, _, sides) := result in
      let target := System.target S c in
      let '(next, update_events) :=
        fx_model_updates ((target, value) :: sides) (Engine.current state, queue) in
      let '(values, next_queue) := next in
      (Pending (Engine.State values next_queue (Engine.recorded state)), prefix ++
        [AuditCall (FxRhs c rhs)] ++ query_events ++ [AuditCall (FxTarget c target)] ++
        update_events ++ [AuditConstruct 2 []])
  end.

(** Binary fuel uses the original then_run branches and does not charge skipped step bodies. *)

Fixpoint fx_model_loop (fuel : positive) (state : Engine.t X C A) :
    outcome X C A * audit_trace (fx_declared_call X C A) :=
  match fuel with
  | xH =>
      let '(out, events) := fx_model_step state in
      (out, AuditCase 8 [] :: events)
  | xO rest =>
      let '(first, first_events) := fx_model_loop rest state in
      match first with
      | Done values =>
          (Done values, AuditCase 8 [] :: first_events ++ [AuditCase 9 []])
      | Pending next =>
          let '(out, second_events) := fx_model_loop rest next in
          (out, AuditCase 8 [] :: first_events ++ [AuditCase 9 []] ++ second_events)
      end
  | xI rest =>
      let '(first, first_events) := fx_model_loop rest state in
      let '(second, second_events) :=
        match first with
        | Done values =>
            (Done values, [AuditCase 9 []])
        | Pending next =>
            let '(out, events) := fx_model_loop rest next in
            (out, AuditCase 9 [] :: events)
        end in
      match second with
      | Done values =>
          (Done values, AuditCase 8 [] :: first_events ++ second_events ++ [AuditCase 9 []])
      | Pending next =>
          let '(out, final_events) := fx_model_step next in
          (out, AuditCase 8 [] :: first_events ++ second_events ++
            [AuditCase 9 []] ++ final_events)
      end
  end.

(** This fixes the complete run_worklist call, including initial enqueue and final option branch. *)

Definition run_worklist_declared_model (fuel : positive) :
    option (assignment X A) * audit_trace (fx_declared_call X C A) :=
  let '(queue, initialization_events) :=
    fx_model_enqueue (System.constraints S) PQueue.empty in
  let '(result, body) := fx_model_loop fuel (Engine.State Map.empty queue Map.empty) in
  (
    match result with
    | Done values => Some values
    | Pending _ => None
    end,
   initialization_events ++ [AuditConstruct 3 []] ++ body ++ [AuditCase 10 []]).

(** Every core model helper must erase to the same original engine computation. *)

(** Erasing counted lookup, query, queue and worklist events recovers the corresponding original
    operations. *)
Definition fx_declared_model_erasure_statement : Prop :=
  (forall values x, fst (fx_model_lookup values x) = lookup EX L values x) /\
  (forall q values, fst (fx_model_query q values) = Query.run q (lookup EX L values)) /\
  (forall cs queue, fst (fx_model_enqueue cs queue) = enqueue EC sch S cs queue) /\
  (forall x old value, fst (fx_model_raise x old value) =
    update_value L sch mode x old value) /\
  (forall xa mq, fst (fx_model_update xa mq) =
    engine_update EX EC L sch mode S (Declared SS ix) Map.empty xa mq) /\
  (forall updates mq, fst (fx_model_updates updates mq) =
    engine_updates EX EC L sch mode S (Declared SS ix) Map.empty updates mq) /\
  (forall state, fst (fx_model_step state) =
    step_outcome EX EC L sch mode S (Declared SS ix) state) /\
  (forall fuel state, fst (fx_model_loop fuel state) =
    loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel state) /\
  (forall fuel, fst (run_worklist_declared_model fuel) =
    run_worklist EX EC L sch mode S (Declared SS ix) fuel).

(** Charges include the same invocation's fixed queue body and actual encoded map keys. *)

Definition fx_declared_call_charge (call : fx_declared_call X C A) : nat :=
  match call with
  | FxGet _ code _ _ body =>
      audit_encoding_weight (Pos.size_nat code) + audit_get_weight code +
        audit_trie_get_trace_source_work body
  | FxReaders _ code _ _ body =>
      audit_encoding_weight (Pos.size_nat code) + audit_get_weight code +
        audit_trie_get_trace_source_work body
  | FxSet _ code _ _ _ body =>
      audit_encoding_weight (Pos.size_nat code) + audit_set_weight code +
        audit_trie_update_trace_source_work body
  | FxPush _ _ _ _ body
  | FxPop _ _ body =>
      1 + fx_queue_internal_charge EC body + audit_queue_recorded_body_work (fun _ => 1) body
  | _ =>
      1
  end.

(** The sum is a deterministic measure of the fixed operation trace, with no price argument. *)

Fixpoint fx_declared_model_work (events : audit_trace (fx_declared_call X C A)) : nat :=
  match events with
  | [] =>
      0
  | AuditCall call :: rest =>
      fx_declared_call_charge call + fx_declared_model_work rest
  | _ :: rest =>
      1 + fx_declared_model_work rest
  end.

(** This explicit primitive excess budget gives two or three actual key bits per map access. *)

Fixpoint fx_declared_primitive_budget (events : audit_trace (fx_declared_call X C A)) : nat :=
  match events with
  | [] =>
      0
  | AuditCall (FxGet _ code _ _ body) :: rest =>
      1 + 2 * Pos.size_nat code + audit_trie_get_trace_source_work body +
        fx_declared_primitive_budget rest
  | AuditCall (FxReaders _ code _ _ body) :: rest =>
      1 + 2 * Pos.size_nat code + audit_trie_get_trace_source_work body +
        fx_declared_primitive_budget rest
  | AuditCall (FxSet _ code _ _ _ body) :: rest =>
      1 + 3 * Pos.size_nat code + audit_trie_update_trace_source_work body +
        fx_declared_primitive_budget rest
  | AuditCall (FxPush _ _ _ _ body) :: rest
  | AuditCall (FxPop _ _ body) :: rest =>
      fx_queue_internal_charge EC body + audit_queue_recorded_body_work (fun _ => 1) body +
        fx_declared_primitive_budget rest
  | _ :: rest =>
      fx_declared_primitive_budget rest
  end.

(** This component contract covers the entire declared fuel run, not other solver portfolios. *)

(** The declared run returns the original result with the stated work equation, and the separate
    counts of AuditCall events containing FxPop and FxRhs are each bounded by Pos.to_nat fuel. *)
Definition run_worklist_declared_model_cost_statement : Prop :=
  forall fuel,
    let '(out, events) := run_worklist_declared_model fuel in
    out = run_worklist EX EC L sch mode S (Declared SS ix) fuel /\
    fx_declared_model_work events = audit_work events + fx_declared_primitive_budget events /\
    List.length (filter (fun event =>
      match event with
      | AuditCall (FxPop _ _ _) => true
      | _ => false
      end) events) <= Pos.to_nat fuel /\
    List.length (filter (fun event =>
      match event with
      | AuditCall (FxRhs _ _) => true
      | _ => false
      end) events) <= Pos.to_nat fuel.

(** Total execution stops on the same empty pop or recurses on the same successful-step state. *)

Inductive fx_declared_total_engine_run : Engine.t X C A -> assignment X A ->
    audit_trace (fx_declared_call X C A) -> Prop :=
  | FxTotalEngineStop : forall state values events,
      fx_model_step state = (Done values, events) ->
      fx_declared_total_engine_run state values events
  | FxTotalEngineContinue : forall state next values head tail,
      fx_model_step state = (Pending next, head) ->
      fx_declared_total_engine_run next values tail ->
      fx_declared_total_engine_run state values (head ++ tail).

(** Accessibility supplies an actual finite modeled execution, not a presumed whole-work bound. *)

(** An accessible starting state has a run in the declared total-engine relation. *)
Definition fx_declared_total_engine_total_statement : Prop :=
  forall start,
    Acc (engine_rel EX EC L sch mode S (Declared SS ix)) start ->
    exists values events, fx_declared_total_engine_run start values events.

(** A total execution retains the original successful steps and its actual final empty pop. *)

(** A declared engine run matches terminating original steps and values, with one more pop than
    steps, one RHS call per step and the stated work equation. *)
Definition fx_declared_total_engine_erases_statement : Prop :=
  forall start values events,
    fx_declared_total_engine_run start values events ->
    exists steps final,
      engine_steps EX EC L sch mode S (Declared SS ix) steps start final /\
      engine_step EX EC L sch mode S (Declared SS ix) final = None /\
      Engine.current final = values /\
      List.length (filter (fun event =>
        match event with
        | AuditCall (FxPop _ _ _) => true
        | _ => false
        end) events) = Datatypes.S steps /\
      List.length (filter (fun event =>
        match event with
        | AuditCall (FxRhs _ _) => true
        | _ => false
        end) events) = steps /\
      fx_declared_model_work events = audit_work events + fx_declared_primitive_budget events.

End DeclaredModel.

(** The total-solver execution witness uses that call's exact prepared index and returned map. *)

(** With lattice laws and termination, the total solver has a declared engine run producing its
    returned map. *)
Definition total_solver_map_model_execution_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (sch : scheduler X) (mode : strategy) (S : System.t X C A)
    (SS : System.static S) (HT : terminates L SS sch mode),
    exists events,
      fx_declared_total_engine_run EX EC L sch mode S (index_system EX S SS)
        (initial_state EC sch S) (proj1_sig (total_solver_map EX EC L HL sch mode S SS HT))
        events.
