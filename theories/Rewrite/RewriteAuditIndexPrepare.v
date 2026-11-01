(** * RewriteAuditIndexPrepare

    This module builds index buckets with receipts for node and parent processing.
    For example, processing no node identifiers leaves the accumulator and emits one block receipt.
    Builds on: RewriteAuditIndexBuild and
    RewriteAuditIndexBucket. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBucket RewriteAuditIndexBuild
  RewriteAuditIndexPrepareReference RewriteAuditIndexReference RewriteAuditQueueContracts
  RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_ri_prepare_receipt (K Sort V : Type) : Type :=
  | RIPrepareBlock : rw_ri_prepare_receipt K Sort V
  | RIPrepareNodeRead : list (audit_map_event rw_id (rw_id * rw_node K Sort V)
      (audit_basic_encoding_event positive)) -> rw_ri_prepare_receipt K Sort V
  | RIPrepareRootRead : list (audit_map_event rw_id rw_id (audit_basic_encoding_event positive)) ->
      rw_ri_prepare_receipt K Sort V
  | RIPrepareOperatorOnce : audit_trace (rw_ri_bucket_call K nat) -> rw_ri_prepare_receipt K Sort V
  | RIPrepareVariableOnce : audit_trace (rw_ri_bucket_call V nat) -> rw_ri_prepare_receipt K Sort V
  | RIPrepareParentOnce : audit_trace (rw_ri_bucket_call rw_id (audit_basic_encoding_event
      positive)) -> rw_ri_prepare_receipt K Sort V
  | RIPrepareDirtyOnce : list (audit_set_event rw_id (audit_basic_encoding_event positive)) ->
      rw_ri_prepare_receipt K Sort V
  | RIPrepareFreshOnce : audit_trace (rw_ri_fresh_call K Sort V) -> rw_ri_prepare_receipt K Sort V.
Arguments RIPrepareBlock {K Sort V}.
Arguments RIPrepareNodeRead {K Sort V}.
Arguments RIPrepareRootRead {K Sort V}.
Arguments RIPrepareOperatorOnce {K Sort V}.
Arguments RIPrepareVariableOnce {K Sort V}.
Arguments RIPrepareParentOnce {K Sort V}.
Arguments RIPrepareDirtyOnce {K Sort V}.
Arguments RIPrepareFreshOnce {K Sort V}.

Definition rw_ri_prepare_receipt_work {K Sort V} (receipt : rw_ri_prepare_receipt K Sort V) : nat :=
  match receipt with
  | RIPrepareBlock => 64
  | RIPrepareNodeRead trace => 64 + audit_map_source_work audit_basic_encoding_work trace
  | RIPrepareRootRead trace => 64 + audit_map_source_work audit_basic_encoding_work trace
  | RIPrepareOperatorOnce trace => 64 + rw_ri_bucket_trace_cost rw_external_events_work trace
  | RIPrepareVariableOnce trace => 64 + rw_ri_bucket_trace_cost rw_external_events_work trace
  | RIPrepareParentOnce trace => 64 + rw_ri_bucket_trace_cost audit_basic_encoding_work trace
  | RIPrepareDirtyOnce trace => 64 + audit_finset_source_work audit_basic_encoding_work trace
  | RIPrepareFreshOnce trace => 64 + rw_ri_fresh_trace_cost trace
  end.

Definition rw_ri_prepare_once_work {K Sort V} (receipts : list (rw_ri_prepare_receipt K Sort V)) :
    nat :=
  fold_right (fun receipt total => rw_ri_prepare_receipt_work receipt + total) 0 receipts.

Fixpoint rw_ri_prepare_parents_once {K Sort V} (g : rw_graph K Sort V) (id : rw_id)
    (children : list rw_id) (table : Map.t rw_id (FinSet.t rw_id)) :
    Map.t rw_id (FinSet.t rw_id) * list (rw_ri_prepare_receipt K Sort V) :=
  match children with
  | nil => (table, [RIPrepareBlock])
  | child :: rest =>
    let '(found, lookup) := audit_map_get audit_positive_encode child (rw_class_roots g) in
    match found with
    | None =>
      let '(out, later) := rw_ri_prepare_parents_once g id rest table in
      (out, RIPrepareRootRead lookup :: RIPrepareBlock :: later)
    | Some root =>
      let '(updated, bucket) := rw_ri_bucket_add_atomic audit_positive_encode root id table in
      let '(out, later) := rw_ri_prepare_parents_once g id rest updated in
      (out, RIPrepareRootRead lookup :: RIPrepareParentOnce bucket :: later)
    end
  end.

Fixpoint rw_ri_prepare_nodes_once {K Sort V} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (g : rw_graph K Sort V) (ids : list rw_id)
    (acc : rw_ri_build_acc K V) : rw_ri_build_acc K V * list (rw_ri_prepare_receipt K Sort V) :=
  match ids with
  | nil => (acc, [RIPrepareBlock])
  | id :: rest =>
    let '(found, lookup) := audit_map_get audit_positive_encode id (rw_nodes g) in
    match found with
    | None =>
      let '(out, later) := rw_ri_prepare_nodes_once op value g rest acc in
      (out, RIPrepareNodeRead lookup :: RIPrepareBlock :: later)
    | Some (_, RWNVar _ v) =>
      let '(updated, bucket) := rw_ri_bucket_add_atomic (rw_external_encoding_events value)
        v id (rw_ri_build_vars acc) in
      let next := RwRiBuildAcc (rw_ri_build_ops acc) updated (rw_ri_build_parents acc) in
      let '(out, later) := rw_ri_prepare_nodes_once op value g rest next in
      (out, RIPrepareNodeRead lookup :: RIPrepareVariableOnce bucket :: later)
    | Some (_, RWNApp _ k children) =>
      let '(updated, bucket) := rw_ri_bucket_add_atomic (rw_external_encoding_events op)
        k id (rw_ri_build_ops acc) in
      let '(parents, parent_receipts) :=
        rw_ri_prepare_parents_once g id children (rw_ri_build_parents acc) in
      let next := RwRiBuildAcc updated (rw_ri_build_vars acc) parents in
      let '(out, later) := rw_ri_prepare_nodes_once op value g rest next in
      (out, RIPrepareNodeRead lookup :: RIPrepareOperatorOnce bucket ::
        parent_receipts ++ later)
    end
  end.

Definition rw_ri_prepare_once {K Sort V} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (g : rw_graph K Sort V) :
    rw_index_state K Sort V * list (rw_ri_prepare_receipt K Sort V) :=
  let empty := RwRiBuildAcc Map.empty Map.empty Map.empty in
  let '(buckets, bucket_receipts) :=
    rw_ri_prepare_nodes_once op value g (rw_nodes_in g) empty in
  let '(dirty, dirty_trace) := audit_finset_of_list audit_positive_encode (rw_nodes_in g) in
  let '(fresh, fresh_trace) := rw_ri_fresh_atomic g in
  (RWIndexState g UnionFind.make (rw_ri_build_parents buckets) Map.empty Map.empty
    (rw_nodes_in g) dirty rw_pending_empty (rw_ri_build_ops buckets)
    (rw_ri_build_vars buckets) fresh,
    RIPrepareBlock :: bucket_receipts ++
      [RIPrepareDirtyOnce dirty_trace; RIPrepareFreshOnce fresh_trace; RIPrepareBlock]).

(** When the operator and value adapters erase to their encodings, preparation erases to the
    plain index builder. *)
Definition rw_ri_prepare_once_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (value : rw_queue_encoder_adapter V) graph,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_ri_prepare_once op value graph) = rw_index_build EK ES EV graph.

(** Preparation emits at most sixteen receipts per unit of stored input structure. *)
Definition rw_ri_prepare_once_receipts_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (value : rw_queue_encoder_adapter V)
    (graph : rw_graph K Sort V),
    length (snd (rw_ri_prepare_once op value graph)) <= 16 * rw_rq_input_structure graph.
