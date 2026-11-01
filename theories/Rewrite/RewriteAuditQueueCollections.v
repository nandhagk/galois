(** * RewriteAuditQueueCollections

    This module provides source operations for pending queues, buckets, and graph lookups.
    For example, popping a queue with an empty sequence produces source value None.
    Builds on: RewriteAuditQueueKernel and
    RewriteAuditQueueReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueKernel RewriteAuditQueueReference.
Import List.ListNotations.

Local Notation "'rqlet' x ':=' e 'in' c" :=
  (rw_rq_bind 1020 e (fun x => c))
  (at level 10, x ident, e at level 100, c at level 200).

Definition rw_rq_insert_source {K Sort V} (p : rw_pair) (queue : rw_pending_queue) :
    rw_rq_source K Sort V rw_pending_queue :=
  rqlet code := rw_rq_pair_encode p in
  rqlet found := rw_rq_map_code_get code (rw_pending_members queue) in
  match found with
  | Some _ => rw_rq_return 1021 queue
  | None =>
    rqlet write_code := rw_rq_pair_encode p in
    rqlet members := rw_rq_code_set write_code (p, tt) (rw_pending_members queue) in
    rw_rq_return 1022 (RwPendingQueue (p :: rw_pending_sequence queue) members)
  end.

Definition rw_rq_prepend_source {K Sort V} (pairs : list rw_pair) (queue : rw_pending_queue) :
    rw_rq_source K Sort V rw_pending_queue :=
  rw_rq_source_fold_right rw_rq_insert_source pairs queue.

Definition rw_rq_pop_source {K Sort V} (queue : rw_pending_queue) :
    rw_rq_source K Sort V (option (rw_pair * rw_pending_queue)) :=
  match rw_pending_sequence queue with
  | nil => rw_rq_return 1023 None
  | p :: rest =>
    rqlet code := rw_rq_pair_encode p in
    rqlet members := rw_rq_code_remove code (rw_pending_members queue) in
    rw_rq_return 1024 (Some (p, RwPendingQueue rest members))
  end.

Fixpoint rw_rq_id_member_source {K Sort V} (target : rw_id) (ids : list rw_id) :
    rw_rq_source K Sort V bool :=
  match ids with
  | nil => rw_rq_return 1025 false
  | id :: rest =>
    rqlet tail := rw_rq_id_member_source target rest in
    rqlet same := rw_rq_decision id target in
    rw_rq_return 1026 (same || tail)
  end.

Fixpoint rw_rq_id_nodup_source {K Sort V} (ids : list rw_id) : rw_rq_source K Sort V (list rw_id) :=
  match ids with
  | nil => rw_rq_return 1027 nil
  | id :: rest =>
    rqlet present := rw_rq_id_member_source id rest in
    rqlet tail := rw_rq_id_nodup_source rest in
    rw_rq_return 1028 (if present then tail else id :: tail)
  end.

Fixpoint rw_rq_remove_ids_source {K Sort V} (target : rw_id) (ids : list rw_id) :
    rw_rq_source K Sort V (list rw_id) :=
  match ids with
  | nil => rw_rq_return 1029 nil
  | id :: rest =>
    rqlet same := rw_rq_decision target id in
    rqlet tail := rw_rq_remove_ids_source target rest in
    rw_rq_return 1030 (if same then tail else id :: tail)
  end.

Definition rw_rq_bucket_add_source {K Sort V A} (encoder : A -> rw_rq_source K Sort V positive)
    (key : A) (id : rw_id) (table : Map.t A (list rw_id)) :
    rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rqlet code := encoder key in
  rqlet found := rw_rq_map_code_get code table in
  let ids :=
    match found with
    | Some xs => xs
    | None => nil
    end in
  rqlet unique := rw_rq_id_nodup_source (id :: ids) in
  rqlet write_code := encoder key in
  rw_rq_code_set write_code (key, unique) table.

Definition rw_rq_bucket_remove_source {K Sort V A} (encoder : A -> rw_rq_source K Sort V positive)
    (key : A) (id : rw_id) (table : Map.t A (list rw_id)) :
    rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rqlet code := encoder key in
  rqlet found := rw_rq_map_code_get code table in
  let ids :=
    match found with
    | Some xs => xs
    | None => nil
    end in
  rqlet retained := rw_rq_remove_ids_source id ids in
  rqlet write_code := encoder key in
  rw_rq_code_set write_code (key, retained) table.

Definition rw_rq_table_add_source {K Sort V A} (encoder : A -> rw_rq_source K Sort V positive)
    (keys : list A) (id : rw_id) (table : Map.t A (list rw_id)) :
    rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rw_rq_source_fold_right (fun key acc => rw_rq_bucket_add_source encoder key id acc) keys table.

Definition rw_rq_table_remove_source {K Sort V A} (encoder : A -> rw_rq_source K Sort V positive)
    (keys : list A) (id : rw_id) (table : Map.t A (list rw_id)) :
    rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rw_rq_source_fold_right (fun key acc => rw_rq_bucket_remove_source encoder key id acc) keys table.

Definition rw_rq_positive_encode {K Sort V} (id : positive) : rw_rq_source K Sort V positive :=
  rw_rq_return 1031 id.

Definition rw_rq_find_source {K Sort V} (g : rw_graph K Sort V) (id : rw_id) : rw_rq_source K Sort V
    (option rw_id) :=
  rqlet code := rw_rq_positive_encode id in
  rw_rq_map_code_get code (rw_class_roots g).

Definition rw_rq_node_source {K Sort V} (g : rw_graph K Sort V) (id : rw_id) : rw_rq_source K Sort V
    (option (rw_id * rw_node K Sort V)) :=
  rqlet code := rw_rq_positive_encode id in
  rw_rq_map_code_get code (rw_nodes g).

Definition rw_rq_sort_source {K Sort V} (g : rw_graph K Sort V) (id : rw_id) : rw_rq_source K Sort V
    (option Sort) :=
  rqlet code := rw_rq_positive_encode id in
  rw_rq_map_code_get code (rw_sorts g).

Definition rw_rq_canon_node_source {K Sort V} (g : rw_graph K Sort V) (node : rw_node K Sort V) :
    rw_rq_source K Sort V (rw_node K Sort V) :=
  match node with
  | RWNVar s v => rw_rq_return 1032 (RWNVar s v)
  | RWNApp s k ids =>
    rqlet canonical := rw_rq_source_map (fun id =>
      rqlet found := rw_rq_find_source g id in
      rw_rq_return 1033 (
        match found with
        | Some r => r
        | None => id
        end)) ids in
    rw_rq_return 1034 (RWNApp s k canonical)
  end.

Fixpoint rw_rq_root_filter_source {K Sort V} (a b : rw_id) (roots : list rw_id) :
    rw_rq_source K Sort V (list rw_id) :=
  match roots with
  | nil => rw_rq_return 1035 nil
  | root :: rest =>
    rqlet first := rw_rq_decision root a in
    rqlet second := rw_rq_decision root b in
    rqlet tail := rw_rq_root_filter_source a b rest in
    rw_rq_return 1036 (if first || second then tail else root :: tail)
  end.

Definition rw_rq_merge_source {K Sort V} (g : rw_graph K Sort V) (a b : rw_id) :
    rw_rq_source K Sort V (rw_graph K Sort V) :=
  rqlet roots := rw_rq_root_filter_source a b (rw_roots g) in
  rqlet classes := rw_rq_collapse_source b a (rw_class_roots g) in
  rw_rq_return 1037 (RwGraph (a :: roots) (rw_nodes_in g) classes (rw_sorts g) (rw_nodes g)).

Definition rw_rq_union_source {K Sort V} (sort : rw_queue_encoder_adapter Sort)
    (g : rw_graph K Sort V) (a b : rw_id) : rw_rq_source K Sort V (option (rw_graph K Sort V)) :=
  rqlet first := rw_rq_find_source g a in
  match first with
  | None => rw_rq_return 1038 None
  | Some ra =>
    rqlet second := rw_rq_find_source g b in
    match second with
    | None => rw_rq_return 1039 None
    | Some rb =>
      rqlet first_sort := rw_rq_sort_source g a in
      match first_sort with
      | None => rw_rq_return 1040 None
      | Some sa =>
        rqlet second_sort := rw_rq_sort_source g b in
        match second_sort with
        | None => rw_rq_return 1041 None
        | Some sb =>
          rqlet ca := rw_rq_sort_encode sort sa in
          rqlet cb := rw_rq_sort_encode sort sb in
          rqlet same := rw_rq_decision ca cb in
          if same then rqlet out := rw_rq_merge_source g ra rb in rw_rq_return 1042 (Some out)
          else rw_rq_return 1043 None
        end
      end
    end
  end.
