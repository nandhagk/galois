(** * RewriteAuditProofRebuild

    This module audits tracked rebuilds and states their projection under connectedness.
    For example, rebuild is done when both the dirty order and pending sequence are empty.
    Builds on: RewriteAuditIndexRebuild and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRebuild RewriteAuditIndexReference
  RewriteAuditIndexTickReference RewriteAuditProofCarrier RewriteAuditProofClosure
  RewriteAuditProofTick RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_rp_rebuild_done {K Sort V H}
    (state : rw_tracked_state K Sort V H * nat * list rw_index_event) : bool :=
  let '(tracked, _, _) := state in
  match rw_index_dirty_order (rw_tracked_machine tracked),
    rw_pending_sequence (rw_index_pending (rw_tracked_machine tracked)) with
  | nil, nil => true
  | _, _ => false
  end.

Definition rw_rp_rebuild_once {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (group : nat)
    (state : rw_tracked_state K Sort V H * nat * list rw_index_event) :
    (rw_tracked_state K Sort V H * nat * list rw_index_event) * nat :=
  let '(tracked, position, events) := state in
  let '(next, work) := rw_rp_tick_atomic op sort value (group, S position) tracked in
  match next with
  | None => (state, 64 + work)
  | Some (final, event) => ((final, S position, event :: events), 64 + work)
  end.

Fixpoint rw_rp_rebuild_repeat {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (group : nat)
    (fuel : positive) (state : rw_tracked_state K Sort V H * nat * list rw_index_event) :
    (rw_tracked_state K Sort V H * nat * list rw_index_event) * nat :=
  if rw_rp_rebuild_done state then (state, 64)
  else
    match fuel with
    | xH =>
      let '(out, work) := rw_rp_rebuild_once op sort value group state in
      (out, 64 + work)
    | xO rest =>
      let '(middle, mw) := rw_rp_rebuild_repeat op sort value group rest state in
      let '(out, tw) := rw_rp_rebuild_repeat op sort value group rest middle in
      (out, 64 + mw + tw)
    | xI rest =>
      let '(first, fw) := rw_rp_rebuild_once op sort value group state in
      let '(middle, mw) := rw_rp_rebuild_repeat op sort value group rest first in
      let '(out, tw) := rw_rp_rebuild_repeat op sort value group rest middle in
      (out, 64 + fw + mw + tw)
    end.

Definition rw_rp_rebuild_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (group : nat)
    (state : rw_tracked_state K Sort V H) :
    (rw_tracked_state K Sort V H * list rw_index_event) * nat :=
  let '(fuel, fw) := rw_ri_rebuild_fuel_atomic (rw_tracked_machine state) in
  let '((final, _, reversed), work) :=
    rw_rp_rebuild_repeat op sort value group fuel (state, 0, nil) in
  let '(events, rw) := rw_ri_reverse_onto reversed nil in
  ((final, events), 64 + fw + work + rw).

(** A connected phase has a well-formed enumerated provenance map and well-formed graph;
    every found class has an unfolding represented witness, every successfully unfolded stored
    root witness represents its root, and same-class terms have generated connections. *)
Definition rw_rp_phase_connected {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (state : rw_tracked_state K Sort V H) : Prop :=
  let graph := rw_index_graph (rw_tracked_machine state) in
  let proof := rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  Map.wf positive_encoding (rw_provenance_nodes proof) /\
  (forall id, In id (rw_provenance_ids proof) <->
    exists node, Map.get positive_encoding id (rw_provenance_nodes proof) = Some node) /\
  (exists sig, rw_graph_wf sig graph) /\
  (forall c root, rw_find graph c = Some root ->
    exists pointer tree,
      Map.get positive_encoding root (rw_class_witness_roots witnesses) = Some pointer /\
      rw_shared_unfold (RwSharedTree K Sort V pointer (rw_class_witness_nodes witnesses)) =
        Some tree /\
      rw_represents graph root tree) /\
  (forall root pointer tree,
    Map.get positive_encoding root (rw_class_witness_roots witnesses) = Some pointer ->
    rw_shared_unfold (RwSharedTree K Sort V pointer (rw_class_witness_nodes witnesses)) =
      Some tree ->
    rw_represents graph root tree) /\
  forall c lhs rhs, rw_represents graph c lhs -> rw_represents graph c rhs ->
    rw_rp_generated proof lhs rhs.

(** With agreeing encoders and a connected phase, tracked source rebuild projects
    to index rebuild with the same machine and events. *)
Definition rw_rp_rebuild_projects_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) group (state : rw_tracked_state K Sort V H)
    final events work,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_rp_rebuild_atomic op sort value group state = ((final, events), work) ->
    rw_rp_phase_connected EK ES EV state ->
    rw_index_rebuild EK ES EV (rw_tracked_machine state) = (rw_tracked_machine final, events).
