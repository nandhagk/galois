(** * RewriteAuditIndexRebuild

    This module models index ticks, their repetition, and graph and fuel setup work.
    For example, counting calls in an empty repeat trace returns zero.
    Builds on: RewriteAuditIndexDirty and
    RewriteAuditIndexPair. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDirty RewriteAuditIndexPair
  RewriteAuditIndexReference RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_ri_tick_call (K Sort V : Type) : Type :=
  | RITickDirty : audit_trace (rw_ri_dirty_call K Sort V) -> rw_ri_tick_call K Sort V
  | RITickPop : audit_trace rw_queue_insert_call -> rw_ri_tick_call K Sort V
  | RITickPair : audit_trace (rw_ri_pair_call K Sort V) -> rw_ri_tick_call K Sort V.
Arguments RITickDirty {K Sort V}.
Arguments RITickPop {K Sort V}.
Arguments RITickPair {K Sort V}.

Definition rw_ri_tick_event_cost {K Sort V} (event : audit_event (rw_ri_tick_call K Sort V)) :
    nat :=
  match event with
  | AuditCall (RITickDirty trace) => 64 + rw_ri_dirty_trace_cost trace
  | AuditCall (RITickPop trace) => 64 + rw_queue_insert_expanded_work trace
  | AuditCall (RITickPair trace) => 64 + rw_ri_pair_trace_cost trace
  | _ => 64
  end.

Definition rw_ri_tick_trace_cost {K Sort V} (trace : audit_trace (rw_ri_tick_call K Sort V)) :
    nat :=
  fold_right (fun event total => rw_ri_tick_event_cost event + total) 0 trace.

Definition rw_ri_tick_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (s : rw_index_state K Sort V) :
    option (rw_index_state K Sort V * rw_index_event) * audit_trace (rw_ri_tick_call K Sort V) :=
  match rw_index_dirty_order s with
  | id :: rest =>
    let '(next, trace) := rw_ri_dirty_tick_atomic op sort value s id rest in
    (Some (next, RWIndexDirty id),
      [AuditCase 930 []; AuditCall (RITickDirty trace); AuditConstruct 931 []])
  | nil =>
    let '(popped, trace) := rw_queue_pop_atomic (rw_index_pending s) in
    match popped with
    | None =>
      (None, [AuditCase 932 []; AuditCall (RITickPop trace);
        AuditCase 933 []; AuditConstruct 934 []])
    | Some (pair_value, remaining) =>
      let '(next, pair_trace) := rw_ri_pair_atomic op sort value s pair_value remaining in
      (Some next, [AuditCase 932 []; AuditCall (RITickPop trace);
        AuditCase 935 []; AuditCall (RITickPair pair_trace); AuditConstruct 936 []])
    end
  end.

(** When operator, sort, and value adapters agree, erasing tick receipts yields the
    public index tick result. *)
Definition rw_ri_tick_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) s,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_ri_tick_atomic op sort value s) = rw_index_tick EK ES EV s.

Inductive rw_ri_repeat_call (K Sort V : Type) : Type :=
  | RIRepeatTick : rw_index_state K Sort V -> option (rw_index_state K Sort V * rw_index_event) ->
      audit_trace (rw_ri_tick_call K Sort V) -> rw_ri_repeat_call K Sort V.
Arguments RIRepeatTick {K Sort V}.

Definition rw_ri_repeat_event_cost {K Sort V} (event : audit_event (rw_ri_repeat_call K Sort V)) :
    nat :=
  match event with
  | AuditCall (RIRepeatTick _ _ trace) => 64 + rw_ri_tick_trace_cost trace
  | _ => 64
  end.

Definition rw_ri_repeat_trace_cost {K Sort V} (trace : audit_trace (rw_ri_repeat_call K Sort V)) :
    nat :=
  fold_right (fun event total => rw_ri_repeat_event_cost event + total) 0 trace.

Definition rw_ri_repeat_once {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V * list rw_index_event) :
    (rw_index_state K Sort V * list rw_index_event) * audit_trace (rw_ri_repeat_call K Sort V) :=
  let '(answer, trace) := rw_ri_tick_atomic op sort value (fst state) in
  match answer with
  | None =>
    (state, [AuditCall (RIRepeatTick (fst state) answer trace); AuditCase 937 []])
  | Some (next, event) =>
    ((next, event :: snd state),
      [AuditCall (RIRepeatTick (fst state) answer trace); AuditCase 938 [];
        AuditConstruct 939 []; AuditConstruct 940 []])
  end.

Fixpoint rw_ri_repeat_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (fuel : positive)
    (state : rw_index_state K Sort V * list rw_index_event) :
    (rw_index_state K Sort V * list rw_index_event) * audit_trace (rw_ri_repeat_call K Sort V) :=
  if rw_ri_rebuild_done state then (state, [AuditCase 941 []; AuditCase 942 []])
  else
    match fuel with
    | xH =>
      let '(out, trace) := rw_ri_repeat_once op sort value state in
      (out, [AuditCase 941 []; AuditCase 943 []] ++ trace)
    | xO rest =>
      let '(middle, first_trace) := rw_ri_repeat_atomic op sort value rest state in
      let '(out, second_trace) := rw_ri_repeat_atomic op sort value rest middle in
      (out, [AuditCase 941 []; AuditCase 944 []] ++ first_trace ++ second_trace)
    | xI rest =>
      let '(middle, first_trace) := rw_ri_repeat_once op sort value state in
      let '(later, second_trace) := rw_ri_repeat_atomic op sort value rest middle in
      let '(out, last_trace) := rw_ri_repeat_atomic op sort value rest later in
      (out, [AuditCase 941 []; AuditCase 945 []] ++ first_trace ++ second_trace ++ last_trace)
    end.

(** When operator, sort, and value adapters agree, erasing repeat receipts yields the
    plain rebuild repeat on the same fuel and state. *)
Definition rw_ri_repeat_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) fuel state,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_ri_repeat_atomic op sort value fuel state) =
      rw_repeat rw_ri_rebuild_done (rw_ri_rebuild_step EK ES EV) fuel state.

Fixpoint rw_ri_reverse_onto {A} (xs acc : list A) : list A * nat :=
  match xs with
  | nil => (acc, 64)
  | x :: rest =>
    let '(out, work) := rw_ri_reverse_onto rest (x :: acc) in
    (out, 128 + work)
  end.

(** Counts the AuditCall events present in a repeat trace. *)
Definition rw_ri_repeat_tick_count {K Sort V} (trace : audit_trace (rw_ri_repeat_call K Sort V)) :
    nat :=
  fold_right (fun event count =>
    match event with
    | AuditCall _ => S count
    | _ => count
    end) 0 trace.

(** The number of tick calls in the trace returned by repeat is at most the positive fuel value. *)
Definition rw_ri_repeat_tick_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) fuel state,
    rw_ri_repeat_tick_count (snd (rw_ri_repeat_atomic op sort value fuel state)) <= Pos.to_nat fuel.

Definition rw_ri_forest_root_atomic (forest : UnionFind.t rw_id) (id : rw_id) :
    rw_id * list (audit_uf_event rw_id (audit_basic_encoding_event positive)) :=
  let '(found, trace) := audit_uf_find audit_positive_encode id forest in
  (fst found, trace).

Fixpoint rw_ri_roots_atomic (forest : UnionFind.t rw_id) (roots : list rw_id) : list rw_id * nat :=
  match roots with
  | nil => (nil, 64)
  | r :: rest =>
    let '(root, trace) := rw_ri_forest_root_atomic forest r in
    let '(same, compare_trace) := audit_positive_eqb root r in
    let '(tail, tail_work) := rw_ri_roots_atomic forest rest in
    ((if same then r :: tail else tail),
      64 + audit_uf_source_work audit_basic_encoding_work trace +
        audit_positive_eqb_source_work compare_trace + tail_work)
  end.

Definition rw_ri_graph_atomic {K Sort V} (state : rw_index_state K Sort V) :
    rw_graph K Sort V * nat :=
  let base := rw_index_base state in
  let forest := rw_index_forest state in
  let '(roots, root_work) := rw_ri_roots_atomic forest (rw_roots base) in
  let '(aliases, trace) :=
    audit_map_transform (rw_ri_forest_root_atomic forest) (rw_class_roots base) in
  (RwGraph roots (rw_nodes_in base) aliases (rw_sorts base) (rw_nodes base),
    64 + root_work +
      audit_map_transform_source_work (audit_uf_source_work audit_basic_encoding_work) trace).

Definition rw_ri_rebuild_fuel_atomic {K Sort V} (s : rw_index_state K Sort V) : positive * nat :=
  let '(nodes, nt) := rw_fuel_length (rw_nodes_in (rw_index_base s)) in
  let '(graph, gw) := rw_ri_graph_atomic s in
  let '(roots, rt) := rw_fuel_length (rw_roots graph) in
  let '(pending, pt) := rw_fuel_length (rw_pending_sequence (rw_index_pending s)) in
  let '(first, mt) := rw_fuel_mul (S roots) (S nodes) in
  let '(square, st) := rw_fuel_mul first (S nodes) in
  let '(prefix, add_trace) := rw_fuel_add pending square in
  let '(dirty, dt) := rw_fuel_length (rw_index_dirty_order s) in
  let '(total, total_trace) := rw_fuel_add prefix dirty in
  let '(fuel, ft) := rw_fuel_to_positive total in
  (fuel, 64 + audit_work nt + gw + audit_work rt + audit_work pt +
    audit_work mt + audit_work st + audit_work add_trace + audit_work dt +
    audit_work total_trace + audit_work ft).

Definition rw_ri_rebuild_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (s : rw_index_state K Sort V) : (rw_index_state K Sort V * list rw_index_event) * nat :=
  let '(fuel, fuel_work) := rw_ri_rebuild_fuel_atomic s in
  let '((out, reversed), trace) := rw_ri_repeat_atomic op sort value fuel (s, nil) in
  let '(events, reverse_work) := rw_ri_reverse_onto reversed nil in
  ((out, events), 64 + fuel_work + rw_ri_repeat_trace_cost trace + reverse_work).

(** Erasing graph-materialization work yields the public index graph. *)
Definition rw_ri_graph_erases_statement : Prop :=
  forall K Sort V (s : rw_index_state K Sort V), fst (rw_ri_graph_atomic s) = rw_index_graph s.

(** Erasing fuel-setup work yields the plain rebuild fuel. *)
Definition rw_ri_rebuild_fuel_erases_statement : Prop :=
  forall K Sort V (s : rw_index_state K Sort V), fst (rw_ri_rebuild_fuel_atomic s) =
    rw_ri_rebuild_fuel s.

(** When operator, sort, and value adapters agree, erasing rebuild work yields the
    public index rebuild state and event list. *)
Definition rw_ri_rebuild_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) s,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_ri_rebuild_atomic op sort value s) = rw_index_rebuild EK ES EV s.

(** When operator, sort, and value adapters agree, erasing pair-tick receipts yields
    the plain pair tick for the same state, pair, and remaining queue. *)
Definition rw_ri_pair_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) s pair_value remaining,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_ri_pair_atomic op sort value s pair_value remaining) =
      rw_ri_pair_tick EK ES EV s pair_value remaining.

(** Count node-read calls in a pair-tick trace. *)
Definition rw_ri_pair_node_read_count {K Sort V} (trace : audit_trace (rw_ri_pair_call K Sort V)) :
    nat :=
  fold_right (fun event total =>
    match event with
    | AuditCall (RIPairNode _) => S total
    | _ => total
    end) 0 trace.
