(** * RewriteAuditProofSeed

    This module constructs a tracked graph and witness store from a seed term and
    states a prospective representation property.
    For example, seeding a variable of natural sort 0 and value 0 creates one graph node
    and one shared witness node.
    Builds on: RewriteAuditIndexPrepare and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrepare RewriteAuditIndexReference
  RewriteAuditProofCarrier RewriteAuditProofTick RewriteAuditQueueReference
  RewriteAuditSharedReference.
Import List.ListNotations.

Record rw_rp_seed_acc (K Sort V : Type) := RwRpSeedAcc {
  rw_rp_seed_graph : rw_graph K Sort V;
  rw_rp_seed_witnesses : rw_class_witness_store K Sort V;
  rw_rp_seed_next : positive;
  rw_rp_seed_witness_next : positive
}.
Arguments RwRpSeedAcc {K Sort V}.
Arguments rw_rp_seed_graph {K Sort V}.
Arguments rw_rp_seed_witnesses {K Sort V}.
Arguments rw_rp_seed_next {K Sort V}.
Arguments rw_rp_seed_witness_next {K Sort V}.

Definition rw_rp_seed_empty {K Sort V} : rw_rp_seed_acc K Sort V :=
  RwRpSeedAcc (RwGraph nil nil Map.empty Map.empty Map.empty)
    (RWClassWitnessStore Map.empty Map.empty) 1%positive 1%positive.

Definition rw_rp_seed_node {K Sort V} (node : rw_node K Sort V) (shared : rw_shared_node K Sort V)
    (acc : rw_rp_seed_acc K Sort V) : ((rw_id * positive) * rw_rp_seed_acc K Sort V) * nat :=
  let id := rw_rp_seed_next acc in
  let pointer := rw_rp_seed_witness_next acc in
  let graph := rw_rp_seed_graph acc in
  let store := rw_rp_seed_witnesses acc in
  let '(aliases, alias_trace) := audit_map_set audit_positive_encode id id (rw_class_roots graph) in
  let '(sorts, sort_trace) :=
    audit_map_set audit_positive_encode id (rw_node_sort node) (rw_sorts graph) in
  let '(nodes, node_trace) := audit_map_set audit_positive_encode id (id, node) (rw_nodes graph) in
  let '(shared_nodes, shared_trace) :=
    audit_map_set audit_positive_encode pointer shared (rw_class_witness_nodes store) in
  let '(witness_roots, root_trace) :=
    audit_map_set audit_positive_encode id pointer (rw_class_witness_roots store) in
  let '(fresh, fresh_trace) := rw_fuel_pos_succ id in
  let '(witness_fresh, witness_fresh_trace) := rw_fuel_pos_succ pointer in
  (((id, pointer), RwRpSeedAcc
    (RwGraph (id :: rw_roots graph) (id :: rw_nodes_in graph) aliases sorts nodes)
    (RWClassWitnessStore shared_nodes witness_roots) fresh witness_fresh),
    64 + audit_map_source_work audit_basic_encoding_work alias_trace +
      audit_map_source_work audit_basic_encoding_work sort_trace +
      audit_map_source_work audit_basic_encoding_work node_trace +
      audit_map_source_work audit_basic_encoding_work shared_trace +
      audit_map_source_work audit_basic_encoding_work root_trace + audit_work fresh_trace +
      audit_work witness_fresh_trace).

Fixpoint rw_rp_seed_term {K Sort V} (term : rw_term K Sort V) (acc : rw_rp_seed_acc K Sort V) :
    ((rw_id * positive) * rw_rp_seed_acc K Sort V) * nat :=
  match term with
  | RWVar ty v =>
    let '(out, work) := rw_rp_seed_node (RWNVar ty v) (RWSharedVar K Sort V ty v) acc in
    (out, 64 + work)
  | RWApp ty op children =>
    let fix visit (ts : list (rw_term K Sort V)) (state : rw_rp_seed_acc K Sort V) :
        (list rw_id * list positive * rw_rp_seed_acc K Sort V) * nat :=
      match ts with
      | nil => ((nil, nil, state), 64)
      | t :: rest =>
        let '(((head, pointer), next), hw) := rw_rp_seed_term t state in
        let '((tail, pointers, final), tw) := visit rest next in
        ((head :: tail, pointer :: pointers, final), 64 + hw + tw)
      end in
    let '((ids, pointers, next), child_work) := visit children acc in
    let '(out, work) :=
      rw_rp_seed_node (RWNApp ty op ids) (RWSharedApp K Sort V ty op pointers) next in
    (out, 64 + child_work + work)
  end.

Definition rw_rp_seed_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (value : rw_queue_encoder_adapter V)
    (term : rw_term K Sort V) : (rw_id * rw_tracked_state K Sort V H) * nat :=
  let '(((root, _), acc), seed_work) :=
    rw_rp_seed_term term rw_rp_seed_empty in
  let '(machine, trace) := rw_ri_prepare_once op value (rw_rp_seed_graph acc) in
  ((root, RWTrackedState machine (RWProvenance nil Map.empty) (rw_rp_seed_witnesses acc) Map.empty),
    64 + seed_work + rw_ri_prepare_once_work trace).

(** Seeding a typed term produces a well-formed graph representing it and unfoldable
    class witnesses represented at their respective roots. *)
Definition rw_rp_seed_represents_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (value : rw_queue_encoder_adapter V)
    (sig : rw_signature K Sort V) term root (state : rw_tracked_state K Sort V H) work,
    rw_typed sig term ->
    rw_rp_seed_atomic EK ES EV op value term = ((root, state), work) ->
    rw_graph_wf sig (rw_index_graph (rw_tracked_machine state)) /\
    rw_represents (rw_index_graph (rw_tracked_machine state)) root term /\
    forall c pointer,
      Map.get positive_encoding c (rw_class_witness_roots (rw_tracked_witnesses state)) =
        Some pointer ->
      exists tree,
        rw_shared_unfold (RwSharedTree K Sort V pointer
          (rw_class_witness_nodes (rw_tracked_witnesses state))) = Some tree /\
        rw_represents (rw_index_graph (rw_tracked_machine state)) c tree.
