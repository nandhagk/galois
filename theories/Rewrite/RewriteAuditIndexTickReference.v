(** * RewriteAuditIndexTickReference

    This module defines plain dirty and pair ticks and the resulting index rebuild.
    For example, an empty dirty order and empty pending queue make the next tick return None.
    Builds on: RewriteAuditIndexBuild and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBuild RewriteAuditIndexReference
  RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_state_update {K Sort V} (s : rw_index_state K Sort V) (forest : UnionFind.t rw_id)
    (parents : Map.t rw_id (FinSet.t rw_id))
    (signatures : Map.t (rw_node K Sort V) (FinSet.t rw_id))
    (keys : Map.t rw_id (rw_node K Sort V)) (dirty_order : list rw_id) (dirty_set : FinSet.t rw_id)
    (pending : rw_pending_queue) : rw_index_state K Sort V :=
  RWIndexState (rw_index_base s) forest parents signatures keys dirty_order dirty_set pending
    (rw_index_operators s) (rw_index_variables s) (rw_index_fresh s).

Definition rw_ri_bucket_remove {A} (E : encoding A) (key : A) (id : rw_id)
    (table : Map.t A (FinSet.t rw_id)) : Map.t A (FinSet.t rw_id) :=
  match Map.get E key table with
  | None => table
  | Some bucket =>
    let updated := FinSet.remove positive_encoding id bucket in
    if FinSet.is_empty updated then Map.remove E key table else Map.set E key updated table
  end.

Fixpoint rw_ri_mark_dirty (ids : list rw_id) (order : list rw_id) (members : FinSet.t rw_id) :
    list rw_id * FinSet.t rw_id :=
  match ids with
  | nil => (order, members)
  | id :: rest =>
    if FinSet.mem positive_encoding id members then rw_ri_mark_dirty rest order members
    else rw_ri_mark_dirty rest (id :: order) (FinSet.add positive_encoding id members)
  end.

Definition rw_ri_dirty_tick {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (s : rw_index_state K Sort V) (id : rw_id) (rest : list rw_id) : rw_index_state K Sort V :=
  let EN := rw_node_encoding EK ES EV in
  let dirty := FinSet.remove positive_encoding id (rw_index_dirty_set s) in
  match rw_node_at (rw_index_base s) id with
  | None =>
    rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
      (rw_index_signatures s) (rw_index_node_keys s) rest dirty (rw_index_pending s)
  | Some (_, node) =>
    let signatures :=
      match Map.get positive_encoding id (rw_index_node_keys s) with
      | None => rw_index_signatures s
      | Some old => rw_ri_bucket_remove EN old id (rw_index_signatures s)
      end in
    let canonical := rw_index_canonical_node s node in
    let peers := FinSet.elements (rw_index_bucket EN canonical signatures) in
    let pending := rw_pending_prepend (map (fun other => (id, other)) peers) (rw_index_pending s) in
    let signatures' := rw_ri_bucket_add EN canonical id signatures in
    let keys' := Map.set positive_encoding id canonical (rw_index_node_keys s) in
    rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
      signatures' keys' rest dirty pending
  end.

Definition rw_ri_pair_tick {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (s : rw_index_state K Sort V) (pair : rw_pair) (remaining : rw_pending_queue) :
    rw_index_state K Sort V * rw_index_event :=
  let '(n, m) := pair in
  let dropped := rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
    (rw_index_signatures s) (rw_index_node_keys s) (rw_index_dirty_order s) (rw_index_dirty_set s)
    remaining in
  let base := rw_index_base s in
  let EN := rw_node_encoding EK ES EV in
  match rw_node_at base n, rw_node_at base m with
  | Some (a, node), Some (b, other) =>
    match rw_index_find s a, rw_index_find s b with
    | Some ra, Some rb =>
      if Pos.eq_dec (encode EN (rw_index_canonical_node s node))
          (encode EN (rw_index_canonical_node s other)) then
        if Pos.eq_dec ra rb then (dropped, RWIndexSkipped pair)
        else
          match rw_class_sort base a, rw_class_sort base b with
          | Some sa, Some sb =>
            if Pos.eq_dec (encode ES sa) (encode ES sb) then
              let forest := UnionFind.union positive_encoding ra rb (rw_index_forest s) in
              let root := fst (UnionFind.find positive_encoding ra forest) in
              let parent_table := rw_index_parent_buckets s in
              let left_parents := rw_index_bucket positive_encoding ra parent_table in
              let right_parents := rw_index_bucket positive_encoding rb parent_table in
              let merged := FinSet.union positive_encoding left_parents right_parents in
              let without :=
                Map.remove positive_encoding rb (Map.remove positive_encoding ra parent_table) in
              let parents :=
                if FinSet.is_empty merged then without
                else Map.set positive_encoding root merged without in
              let '(order, dirty) := rw_ri_mark_dirty (FinSet.elements merged)
                (rw_index_dirty_order s) (rw_index_dirty_set s) in
              (rw_ri_state_update s forest parents (rw_index_signatures s) (rw_index_node_keys s)
                order dirty remaining, RWIndexCongruence pair ra rb root)
            else (dropped, RWIndexSkipped pair)
          | _, _ => (dropped, RWIndexSkipped pair)
          end
      else (dropped, RWIndexSkipped pair)
    | _, _ => (dropped, RWIndexSkipped pair)
    end
  | _, _ => (dropped, RWIndexSkipped pair)
  end.

Definition rw_index_tick {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (s : rw_index_state K Sort V) : option (rw_index_state K Sort V * rw_index_event) :=
  match rw_index_dirty_order s with
  | id :: rest => Some (rw_ri_dirty_tick EK ES EV s id rest, RWIndexDirty id)
  | nil =>
    match rw_pending_pop (rw_index_pending s) with
    | None => None
    | Some (pending_pair, remaining) => Some (rw_ri_pair_tick EK ES EV s pending_pair remaining)
    end
  end.

Definition rw_ri_rebuild_done {K Sort V} (state : rw_index_state K Sort V * list rw_index_event) :
    bool :=
  match rw_index_dirty_order (fst state), rw_pending_sequence (rw_index_pending (fst state)) with
  | nil, nil => true
  | _, _ => false
  end.

Definition rw_ri_rebuild_step {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (state : rw_index_state K Sort V * list rw_index_event) :
    rw_index_state K Sort V * list rw_index_event :=
  match rw_index_tick EK ES EV (fst state) with
  | None => state
  | Some (next, event) => (next, event :: snd state)
  end.

Definition rw_ri_rebuild_fuel {K Sort V} (s : rw_index_state K Sort V) : positive :=
  let nodes := length (rw_nodes_in (rw_index_base s)) in
  let roots := length (rw_roots (rw_index_graph s)) in
  let pending := length (rw_pending_sequence (rw_index_pending s)) in
  Pos.of_succ_nat (pending + (S roots) * (S nodes) * (S nodes) + length (rw_index_dirty_order s)).

Definition rw_index_rebuild {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (s : rw_index_state K Sort V) : rw_index_state K Sort V * list rw_index_event :=
  let '(out, reversed) := rw_repeat rw_ri_rebuild_done (rw_ri_rebuild_step EK ES EV)
    (rw_ri_rebuild_fuel s) (s, nil) in
  (out, rev reversed).
