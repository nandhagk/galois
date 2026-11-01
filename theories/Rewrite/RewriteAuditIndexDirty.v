(** * RewriteAuditIndexDirty

    This module audits dirty-node processing, including signature buckets and pending pairs.
    For example, a dirty identifier missing from the node map is removed from the dirty set.
    Builds on: RewriteAuditIndexBucket and
    RewriteAuditIndexTickReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBucket RewriteAuditIndexFind
  RewriteAuditIndexReference RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_node_event (K Sort V : Type) :=
  audit_sum_event (Sort * V) (Sort * (K * list rw_id)) (audit_pair_event Sort V nat nat)
    (audit_pair_event Sort (K * list rw_id) nat (audit_pair_event K (list rw_id) nat
    (audit_list_event rw_id (audit_basic_encoding_event positive)))).

Definition rw_ri_node_encoder {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (node : rw_node K Sort V) :
    positive * list (rw_ri_node_event K Sort V) :=
  rw_node_encode_atomic (rw_external_encoding_events op) (rw_external_encoding_events sort)
    (rw_external_encoding_events value) node.

Definition rw_ri_node_encoding_work {K Sort V} (trace : list (rw_ri_node_event K Sort V)) : nat :=
  rw_node_encode_trace_cost rw_external_events_work rw_external_events_work rw_external_events_work
    trace.

Inductive rw_ri_dirty_call (K Sort V : Type) : Type :=
  | RIDirtySet : list (audit_set_event rw_id (audit_basic_encoding_event positive)) ->
      rw_ri_dirty_call K Sort V
  | RIDirtyNode : list (audit_map_event rw_id (rw_id * rw_node K Sort V) (audit_basic_encoding_event
      positive)) -> rw_ri_dirty_call K Sort V
  | RIDirtyOldKey : list (audit_map_event rw_id (rw_node K Sort V) (audit_basic_encoding_event
      positive)) -> rw_ri_dirty_call K Sort V
  | RIDirtyBucket : list (audit_event (rw_ri_bucket_call (rw_node K Sort V) (rw_ri_node_event K Sort
      V))) -> rw_ri_dirty_call K Sort V
  | RIDirtyCanon : rw_node K Sort V -> rw_node K Sort V -> audit_trace rw_ri_canon_call ->
      rw_ri_dirty_call K Sort V
  | RIDirtySignature : list (audit_map_event (rw_node K Sort V) (FinSet.t rw_id) (rw_ri_node_event K
      Sort V)) -> rw_ri_dirty_call K Sort V
  | RIDirtyPeers : list (audit_set_elements_event rw_id) -> rw_ri_dirty_call K Sort V
  | RIDirtyPairs : list rw_id -> list rw_pair -> audit_trace unit -> rw_ri_dirty_call K Sort V
  | RIDirtyPending : rw_pending_queue -> audit_trace rw_queue_insert_call -> rw_ri_dirty_call K Sort
      V
  | RIDirtyKeySet : list (audit_map_event rw_id (rw_node K Sort V) (audit_basic_encoding_event
      positive)) -> rw_ri_dirty_call K Sort V.
Arguments RIDirtySet {K Sort V}.
Arguments RIDirtyNode {K Sort V}.
Arguments RIDirtyOldKey {K Sort V}.
Arguments RIDirtyBucket {K Sort V}.
Arguments RIDirtyCanon {K Sort V}.
Arguments RIDirtySignature {K Sort V}.
Arguments RIDirtyPeers {K Sort V}.
Arguments RIDirtyPairs {K Sort V}.
Arguments RIDirtyPending {K Sort V}.
Arguments RIDirtyKeySet {K Sort V}.

Definition rw_ri_dirty_event_cost {K Sort V} (event : audit_event (rw_ri_dirty_call K Sort V)) : nat
    :=
  match event with
  | AuditCall (RIDirtySet trace) => 1 + audit_finset_source_work audit_basic_encoding_work trace
  | AuditCall (RIDirtyNode trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIDirtyOldKey trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIDirtyBucket trace) => 1 + rw_ri_bucket_trace_cost rw_ri_node_encoding_work trace
  | AuditCall (RIDirtyCanon _ _ trace) => 1 + rw_ri_canon_trace_cost trace
  | AuditCall (RIDirtySignature trace) => 1 + audit_map_source_work rw_ri_node_encoding_work trace
  | AuditCall (RIDirtyPeers trace) => 1 + audit_set_elements_work trace
  | AuditCall (RIDirtyPairs _ _ trace) => 1 + audit_work trace
  | AuditCall (RIDirtyPending _ trace) => 1 + rw_queue_insert_expanded_work trace
  | AuditCall (RIDirtyKeySet trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | _ => 1
  end.

Definition rw_ri_dirty_trace_cost {K Sort V} (trace : audit_trace (rw_ri_dirty_call K Sort V)) : nat
    :=
  fold_right (fun event total => rw_ri_dirty_event_cost event + total) 0 trace.

Fixpoint rw_ri_peer_pairs_atomic (id : rw_id) (peers : list rw_id) : list rw_pair * audit_trace unit
    :=
  match peers with
  | nil => (nil, [AuditCase 840 []; AuditConstruct 841 []])
  | peer :: rest =>
    let pair_value := (id, peer) in
    let '(tail, trace) := rw_ri_peer_pairs_atomic id rest in
    (pair_value :: tail, [AuditCase 842 []; AuditConstruct 843 []] ++ trace ++ [AuditConstruct
      844 []])
  end.

Definition rw_ri_dirty_tick_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (s : rw_index_state K Sort V) (id : rw_id) (rest : list rw_id) :
    rw_index_state K Sort V * audit_trace (rw_ri_dirty_call K Sort V) :=
  let node_enc := rw_ri_node_encoder op sort value in
  let '(dirty, dirty_trace) :=
    audit_finset_remove audit_positive_encode id (rw_index_dirty_set s) in
  let '(found, node_trace) := audit_map_get audit_positive_encode id (rw_nodes (rw_index_base s)) in
  let prefix := [AuditCall (RIDirtySet dirty_trace); AuditCall (RIDirtyNode node_trace)] in
  match found with
  | None =>
    (rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
      (rw_index_signatures s) (rw_index_node_keys s) rest dirty (rw_index_pending s),
      prefix ++ [AuditCase 845 []; AuditConstruct 846 []])
  | Some (_, node) =>
    let '(old, old_trace) := audit_map_get audit_positive_encode id (rw_index_node_keys s) in
    let '(signatures, remove_events) :=
      match old with
      | None => (rw_index_signatures s, [AuditCase 849 []])
      | Some key =>
        let '(out, trace) := rw_ri_bucket_remove_atomic node_enc key id
          (rw_index_signatures s) in
        (out, [AuditCase 850 []; AuditCall (RIDirtyBucket trace)])
      end in
    let '(canonical, canon_trace) := rw_ri_canon_atomic s node in
    let '(found_peers, sig_trace) := audit_map_get node_enc canonical signatures in
    let bucket :=
      match found_peers with
      | Some b => b
      | None => FinSet.empty
      end in
    let '(peers, peers_trace) := audit_finset_elements bucket in
    let '(pairs, pairs_trace) := rw_ri_peer_pairs_atomic id peers in
    let '(pending, pending_trace) := rw_queue_prepend_atomic pairs (rw_index_pending s) in
    let '(signatures', add_trace) := rw_ri_bucket_add_atomic node_enc canonical id signatures in
    let '(keys', key_trace) := audit_map_set audit_positive_encode id canonical
      (rw_index_node_keys s) in
    (rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s) signatures' keys' rest
      dirty pending,
      prefix ++ [AuditCase 847 []; AuditCall (RIDirtyOldKey old_trace)] ++ remove_events ++
      [AuditCall (RIDirtyCanon node canonical canon_trace); AuditCall (RIDirtySignature sig_trace);
        AuditCall (RIDirtyPeers peers_trace); AuditCall (RIDirtyPairs peers pairs pairs_trace);
        AuditCall (RIDirtyPending pending pending_trace); AuditCall (RIDirtyBucket add_trace);
        AuditCall (RIDirtyKeySet key_trace); AuditConstruct 848 []])
  end.

Definition rw_ri_dirty_tick_budget {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (s : rw_index_state K Sort V) (id : rw_id) : nat :=
  let EN := rw_node_encoding EK ES EV in
  let node_enc := rw_ri_node_encoder op sort value in
  100 + 64 * Pos.size_nat id +
  match rw_node_at (rw_index_base s) id with
  | None => 0
  | Some (_, node) =>
    let old := Map.get positive_encoding id (rw_index_node_keys s) in
    let signatures :=
      match old with
      | None => rw_index_signatures s
      | Some key => rw_ri_bucket_remove EN key id (rw_index_signatures s)
      end in
    let canonical := rw_index_canonical_node s node in
    let peers_bucket := rw_index_bucket EN canonical signatures in
    let peers := FinSet.elements peers_bucket in
    let pairs := map (fun other => (id, other)) peers in
    (
      match old with
      | None => 0
      | Some key =>
        rw_ri_bucket_atomic_budget node_enc rw_ri_node_encoding_work key id
      end) +
    rw_ri_canon_budget s node +
    2 * rw_ri_bucket_atomic_budget node_enc rw_ri_node_encoding_work canonical id +
    19 * audit_trie_nodes peers_bucket + audit_trie_output_bits peers_bucket + 6 +
    2 + 3 * length peers + rw_queue_prepend_expanded_budget pairs
  end.

(** With the three encoder adapter laws, a dirty tick returns the plain dirty tick
    result and its trace cost is bounded by the dirty-tick budget. *)
Definition rw_ri_dirty_client_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop) (s : rw_index_state K Sort V) id rest,
    rw_queue_encoder_adapter_laws EK op_execution op ->
    rw_queue_encoder_adapter_laws ES sort_execution sort ->
    rw_queue_encoder_adapter_laws EV value_execution value ->
    let '(out, trace) := rw_ri_dirty_tick_atomic op sort value s id rest in
    out = rw_ri_dirty_tick EK ES EV s id rest /\
    rw_ri_dirty_trace_cost trace <= rw_ri_dirty_tick_budget EK ES EV op sort value s id.

(** With the three encoder adapter laws, a dirty tick returns the plain dirty tick
    result and its trace cost is bounded by the dirty-tick budget. *)
Definition rw_ri_dirty_client_contract : Prop :=
  rw_ri_dirty_client_statement.
