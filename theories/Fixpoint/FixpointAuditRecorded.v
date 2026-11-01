(** * Recorded-reader worklist source model

    This proposal retains the actual duplicate read occurrences and persistent reader maps.
    For example, two reads of the same unknown execute two recorded updates.
    Builds on: FixpointWorklist and the counted queue, trie, set and enumeration models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsHeap CollectionsAuditQueue.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet
  CollectionsAuditQueue CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointAuditWorklist.
Import List.ListNotations.

Definition fx_index_set_nested_work {X} (event : audit_set_event X (fx_encoder_entry X)) : nat :=
  match event with
  | AuditSetAdd _ _ _ _ enc trie
  | AuditSetRemove _ _ _ _ enc trie =>
      List.length enc + audit_trie_update_trace_source_work trie
  | AuditSetMem _ _ _ _ enc trie => List.length enc + audit_trie_get_trace_source_work trie
  | AuditSetFold _ _ => 0
  end.

(** An event retains the exact persistent reader map and all actual nested primitive subruns. *)

Inductive fx_recorded_event (X C A : Type) : Type :=
  | FxRecordedBase (events : audit_trace (fx_declared_call X C A))
  | FxRecordedRead (unknown : X) (constraint : C) (before : Map.t X (FinSet.t C))
      (lookup_code : positive) (raw : option (FinSet.t C))
      (lookup_events : audit_trace (audit_trie_call (X * FinSet.t C)))
      (old_set new_set : FinSet.t C) (add_events : list (audit_set_event C (fx_encoder_entry C)))
      (set_code : positive) (after : Map.t X (FinSet.t C))
      (set_events : audit_trace (audit_trie_call (X * FinSet.t C)))
  | FxRecordedReaders (unknown : X) (before : Map.t X (FinSet.t C))
      (code : positive) (raw : option (FinSet.t C))
      (lookup_events : audit_trace (audit_trie_call (X * FinSet.t C)))
      (set : FinSet.t C) (readers : list C) (elements_events : list (audit_set_elements_event C))
  | FxRecordedWrite (unknown : X) (code : positive) (value : A)
      (before after : assignment X A) (body : audit_trace (audit_trie_call (X * A)))
  | FxRecordedCompare (value old : A) (unchanged : bool)
  | FxRecordedCase (site : nat).

Arguments FxRecordedBase {X C A} _.

Arguments FxRecordedRead {X C A} _ _ _ _ _ _ _ _ _ _ _ _.

Arguments FxRecordedReaders {X C A} _ _ _ _ _ _ _ _.

Arguments FxRecordedWrite {X C A} _ _ _ _ _ _.

Arguments FxRecordedCompare {X C A} _ _ _.

Arguments FxRecordedCase {X C A} _.

(** One read performs the original map lookup, set insertion and map write once each. *)

Definition fx_recorded_read_one {X C A} (EX : encoding X) (EC : encoding C) (c : C) (x : X)
    (before : Map.t X (FinSet.t C)) : Map.t X (FinSet.t C) * fx_recorded_event X C A :=
  let lookup_code := encode EX x in
  let '(raw, lookup_events) := audit_map_code_get lookup_code before in
  let old_set :=
    match raw with
    | Some set => set
    | None => FinSet.empty
    end in
  let '(new_set, add_events) := audit_finset_add (fx_index_encoder EC) c old_set in
  let set_code := encode EX x in
  let '(after, set_events) := audit_trie_set set_code (x, new_set) before in
  (after, FxRecordedRead x c before lookup_code raw lookup_events old_set new_set add_events
    set_code after set_events).

(** The real left fold retains every read occurrence, including duplicate unknowns. *)

Fixpoint fx_record_reads_counted {X C A} (EX : encoding X) (EC : encoding C) (c : C)
    (reads : list X) (before : Map.t X (FinSet.t C)) :
    Map.t X (FinSet.t C) * list (fx_recorded_event X C A) :=
  match reads with
  | [] => (before, [FxRecordedCase 0])
  | x :: rest =>
      let '(next, event) := @fx_recorded_read_one X C A EX EC c x before in
      let '(out, tail) := @fx_record_reads_counted X C A EX EC c rest next in
      (out, FxRecordedCase 0 :: event :: tail)
  end.

(** Reader lookup retains the exact set and its actual enumeration subrun. *)

Definition fx_recorded_readers_counted {X C A} (EX : encoding X)
    (before : Map.t X (FinSet.t C)) (x : X) : list C * fx_recorded_event X C A :=
  let code := encode EX x in
  let '(raw, lookup_events) := audit_map_code_get code before in
  let set :=
    match raw with
    | Some value => value
    | None => FinSet.empty
    end in
  let '(readers, elements_events) := audit_finset_elements set in
  (readers, FxRecordedReaders x before code raw lookup_events set readers elements_events).

(** Reader-map updates erase to the actual recorded dependency operation. *)

(** Discarding recorded-read events returns the original reader map after the same reads. *)
Definition fx_record_reads_erasure_statement : Prop :=
  forall X C (EX : encoding X) (EC : encoding C) c reads before,
    fst (@fx_record_reads_counted X C unit EX EC c reads before) = record_reads EX EC c reads
      before.

(** Every read occurrence contributes one update, even when values repeat. *)

(** The recorded-read event count is one plus twice the number of input reads, including
    duplicates. *)
Definition fx_record_reads_count_statement : Prop :=
  forall X C (EX : encoding X) (EC : encoding C) c reads before,
    List.length (snd (@fx_record_reads_counted X C unit EX EC c reads before)) =
      Datatypes.S (2 * List.length reads).

(** A recorded-reader enumeration returns the original engine reader list. *)

(** Discarding recorded-reader events returns the original engine reader list. *)
Definition fx_recorded_readers_erasure_statement : Prop :=
  forall X C A (EX : encoding X) (S : System.t X C A) before x,
    fst (@fx_recorded_readers_counted X C A EX before x) =
      engine_readers EX (Recorded : dependencies S) before x.

Section RecordedEngine.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).

(** The original update branches on the actual old value and enumerates recorded readers. *)

Definition fx_recorded_update (r : Map.t X (FinSet.t C)) (xa : X * A)
    (mq : assignment X A * PQueue.t C) :
    (assignment X A * PQueue.t C) * list (fx_recorded_event X C A) :=
  let '(values, queue) := mq in
  let '(x, value) := xa in
  let '(old, lookup_events) := @fx_model_lookup X C A EX L values x in
  let unchanged := leb L value old in
  if unchanged then
    ((values, queue), [FxRecordedBase lookup_events; FxRecordedCompare value old unchanged;
      FxRecordedCase 1])
  else
    let '(raised, raise_events) := @fx_model_raise X C A L sch mode x old value in
    let code := encode EX x in
    let '(next_values, write_events) := audit_trie_set code (x, raised) values in
    let '(readers, reader_event) := @fx_recorded_readers_counted X C A EX r x in
    let '(next_queue, enqueue_events) := fx_model_enqueue EC sch S readers queue in
    ((next_values, next_queue),
     [FxRecordedBase lookup_events; FxRecordedCompare value old unchanged; FxRecordedCase 1;
      FxRecordedBase raise_events; FxRecordedWrite x code raised values next_values write_events;
      reader_event; FxRecordedBase enqueue_events]).

(** Updates follow the actual left fold and retain every intermediate assignment and queue. *)

Fixpoint fx_recorded_updates (r : Map.t X (FinSet.t C)) (updates : list (X * A))
    (mq : assignment X A * PQueue.t C) :
    (assignment X A * PQueue.t C) * list (fx_recorded_event X C A) :=
  match updates with
  | [] => (mq, [FxRecordedCase 2])
  | update :: rest =>
      let '(next, head) := fx_recorded_update r update mq in
      let '(out, tail) := fx_recorded_updates r rest next in
      (out, FxRecordedCase 2 :: head ++ tail)
  end.

(** Each successful step records exactly the reads returned by that same query run. *)

Definition fx_recorded_step (state : Engine.t X C A) :
    outcome X C A * list (fx_recorded_event X C A) :=
  let '(popped, pop_events) := audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state)
    in
  let prefix := [FxRecordedBase [AuditCall (FxPop (Engine.queue state) popped pop_events)];
                 FxRecordedCase 3] in
  match popped with
  | None => (Done (Engine.current state), prefix)
  | Some (_, c, queue) =>
      let rhs := System.rhs S c in
      let '(result, query_events) := @fx_model_query X C A EX L rhs (Engine.current state) in
      let '(value, reads, sides) := result in
      let '(recorded, read_events) :=
        @fx_record_reads_counted X C A EX EC c reads (Engine.recorded state) in
      let target := System.target S c in
      let '(next, update_events) :=
        fx_recorded_updates recorded ((target, value) :: sides) (Engine.current state, queue) in
      let '(values, next_queue) := next in
      (Pending (Engine.State values next_queue recorded),
       prefix ++ [FxRecordedBase [AuditCall (FxRhs c rhs)]; FxRecordedBase query_events] ++
       read_events ++ [FxRecordedBase [AuditCall (FxTarget c target)]] ++ update_events ++
       [FxRecordedCase 8])
  end.

(** Binary fuel follows the same continuation branches as the original recorded worklist. *)

Fixpoint fx_recorded_loop (fuel : positive) (state : Engine.t X C A) :
    outcome X C A * list (fx_recorded_event X C A) :=
  match fuel with
  | xH =>
      let '(out, events) := fx_recorded_step state in (out, FxRecordedCase 4 :: events)
  | xO rest =>
      let '(first, first_events) := fx_recorded_loop rest state in
      match first with
      | Done values => (Done values, FxRecordedCase 4 :: first_events ++ [FxRecordedCase 5])
      | Pending next =>
          let '(out, second_events) := fx_recorded_loop rest next in
          (out, FxRecordedCase 4 :: first_events ++ [FxRecordedCase 5] ++ second_events)
      end
  | xI rest =>
      let '(first, first_events) := fx_recorded_loop rest state in
      let '(second, second_events) :=
        match first with
        | Done values => (Done values, [FxRecordedCase 5])
        | Pending next =>
            let '(out, events) := fx_recorded_loop rest next in (out, FxRecordedCase 5 :: events)
        end in
      match second with
      | Done values =>
          (Done values, FxRecordedCase 4 :: first_events ++ second_events ++ [FxRecordedCase 5])
      | Pending next =>
          let '(out, final_events) := fx_recorded_step next in
          (out, FxRecordedCase 4 :: first_events ++ second_events ++ [FxRecordedCase 5] ++
            final_events)
      end
  end.

(** Initialization and fuel exhaustion retain the actual recorded worklist result. *)

Definition run_worklist_recorded_model (fuel : positive) :
    option (assignment X A) * list (fx_recorded_event X C A) :=
  let '(queue, initialization) := fx_model_enqueue EC sch S (System.constraints S) PQueue.empty in
  let '(out, events) := fx_recorded_loop fuel (Engine.State Map.empty queue Map.empty) in
  (
    match out with
    | Done values => Some values
    | Pending _ => None
    end,
   FxRecordedBase initialization :: FxRecordedCase 6 :: events ++ [FxRecordedCase 7]).

(** Each helper and the full fixed-fuel operation erase to the original recorded operations. *)

(** Erasing counted updates, steps and loop events recovers the original recorded worklist
    operations. *)
Definition fx_recorded_model_erasure_statement : Prop :=
  (forall r xa mq, fst (fx_recorded_update r xa mq) =
    engine_update EX EC L sch mode S Recorded r xa mq) /\
  (forall r ups mq, fst (fx_recorded_updates r ups mq) =
    engine_updates EX EC L sch mode S Recorded r ups mq) /\
  (forall state, fst (fx_recorded_step state) = step_outcome EX EC L sch mode S Recorded state) /\
  (forall fuel state, fst (fx_recorded_loop fuel state) =
    loop (step_outcome EX EC L sch mode S Recorded) fuel state) /\
  (forall fuel, fst (run_worklist_recorded_model fuel) =
    run_worklist EX EC L sch mode S Recorded fuel).

(** The fixed charge includes each retained map, set, enumeration and queue source-frame model. *)

Definition fx_recorded_event_work (event : fx_recorded_event X C A) : nat :=
  match event with
  | FxRecordedBase events => fx_declared_model_work EC events
  | FxRecordedRead _ _ _ lookup_code _ lookup_events _ _ add_events set_code _ set_events =>
      1 + audit_encoding_weight (Pos.size_nat lookup_code) +
      audit_trie_get_trace_source_work lookup_events + audit_finset_source_work (@length
        (fx_encoder_entry C)) add_events +
      audit_encoding_weight (Pos.size_nat set_code) + audit_trie_update_trace_source_work set_events
  | FxRecordedReaders _ _ code _ lookup_events _ _ elements_events =>
      1 + audit_encoding_weight (Pos.size_nat code) +
      audit_trie_get_trace_source_work lookup_events + audit_set_elements_work elements_events
  | FxRecordedWrite _ code _ _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | FxRecordedCompare _ _ _ => 1
  | FxRecordedCase _ => 1
  end.

(** Work is the fixed fold over this particular recorded execution's events. *)

Definition fx_recorded_work (events : list (fx_recorded_event X C A)) : nat :=
  fold_right (fun event total => fx_recorded_event_work event + total) 0 events.

(** The budget uses actual operand sizes and reader-set states, never a client-provided price. *)

Definition fx_recorded_event_budget (event : fx_recorded_event X C A) : nat :=
  match event with
  | FxRecordedBase events => audit_work events + fx_declared_primitive_budget EC events
  | FxRecordedRead _ c _ lookup_code _ _ _ _ _ set_code _ _ =>
      20 + 6 * Pos.size_nat lookup_code + 17 * Pos.size_nat set_code +
        16 * Pos.size_nat (encode EC c)
  | FxRecordedReaders _ _ code _ _ set _ _ =>
      8 + 6 * Pos.size_nat code + 19 * audit_trie_nodes set + audit_trie_output_bits set
  | FxRecordedWrite _ code _ _ _ _ => 2 + 17 * Pos.size_nat code
  | FxRecordedCompare _ _ _ => 1
  | FxRecordedCase _ => 1
  end.

Definition fx_recorded_budget (events : list (fx_recorded_event X C A)) : nat :=
  fold_right (fun event total => fx_recorded_event_budget event + total) 0 events.

(** Base worklist events are kept in execution order for concrete pop and RHS counts. *)

Fixpoint fx_recorded_base_calls (events : list (fx_recorded_event X C A)) :
    list (fx_declared_call X C A) :=
  match events with
  | [] => []
  | FxRecordedBase base :: rest => audit_calls base ++ fx_recorded_base_calls rest
  | _ :: rest => fx_recorded_base_calls rest
  end.

(** The actual run meets operand-derived work and fuel bounds on that very execution. *)

(** The recorded worklist returns the original result within its trace budget, and the separate
    counts of base FxPop and FxRhs calls are each bounded by Pos.to_nat fuel. *)
Definition fx_recorded_model_cost_statement : Prop :=
  forall fuel,
    let '(result, events) := run_worklist_recorded_model fuel in
    result = run_worklist EX EC L sch mode S Recorded fuel /\
    fx_recorded_work events <= fx_recorded_budget events /\
    List.length (filter (fun call =>
      match call with
      | FxPop _ _ _ => true
      | _ => false
      end) (fx_recorded_base_calls events)) <= Pos.to_nat fuel /\
    List.length (filter (fun call =>
      match call with
      | FxRhs _ _ => true
      | _ => false
      end) (fx_recorded_base_calls events)) <= Pos.to_nat fuel.

(** A successful query creates exactly one recorded successor engine state. *)

(** The count of recorded successor-case events equals the count of recorded base right-hand-side
    calls. *)
Definition fx_recorded_successor_count_statement : Prop :=
  forall fuel,
    let '(_, events) := run_worklist_recorded_model fuel in
    List.length (filter (fun event =>
      match event with
      | FxRecordedCase 8 => true
      | _ => false
      end) events) =
    List.length (filter (fun call =>
      match call with
      | FxRhs _ _ => true
      | _ => false
      end) (fx_recorded_base_calls events)).

End RecordedEngine.
