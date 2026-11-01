(** * RewriteAuditQueueIndex

    Builds index and pending-pair source operations from receipt-producing queue primitives.
    For example, a variable node with natural sort 0 and value 0 contributes no operator keys.
    Builds on: RewriteAuditQueueCollections and
    RewriteAuditQueueKernel. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueCollections RewriteAuditQueueKernel
  RewriteAuditQueueReference.
Import List.ListNotations.

Local Notation "'rqlet' x ':=' e 'in' c" :=
  (rw_rq_bind 1020 e (fun x => c))
  (at level 10, x ident, e at level 100, c at level 200).

Definition rw_rq_operator_keys_source {K Sort V} (node : rw_node K Sort V) : rw_rq_source K Sort V
    (list K) :=
  match node with
  | RWNVar _ _ => rw_rq_return 1044 nil
  | RWNApp _ op _ => rw_rq_return 1045 [op]
  end.

Definition rw_rq_child_keys_source {K Sort V} (node : rw_node K Sort V) : rw_rq_source K Sort V
    (list rw_id) :=
  match node with
  | RWNVar _ _ => rw_rq_return 1046 nil
  | RWNApp _ _ children => rw_rq_return 1047 children
  end.

Definition rw_rq_root_keys_source {K Sort V} (g : rw_graph K Sort V) (node : rw_node K Sort V) :
    rw_rq_source K Sort V (list rw_id) :=
  rqlet children := rw_rq_child_keys_source node in
  rw_rq_source_flat_map (fun child =>
    rqlet found := rw_rq_find_source g child in
    rw_rq_return 1048 (
      match found with
      | None => nil
      | Some root => [root]
      end)) children.

Definition rw_rq_variable_keys_source {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (node : rw_node K Sort V) :
    rw_rq_source K Sort V (list rw_id) :=
  match node with
  | RWNVar s v =>
    rqlet code := rw_rq_node_encode op sort value (RWNVar s v) in
    rw_rq_return 1049 [code]
  | RWNApp _ _ _ => rw_rq_return 1050 nil
  end.

Definition rw_rq_build_table_source {K Sort V A} (encoder : A -> rw_rq_source K Sort V positive)
    (keys : rw_node K Sort V -> rw_rq_source K Sort V (list A)) (g : rw_graph K Sort V)
    (ids : list rw_id) : rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rw_rq_source_fold_right (fun id table =>
    rqlet found := rw_rq_node_source g id in
    match found with
    | None => rw_rq_return 1051 table
    | Some (_, node) =>
      rqlet actual_keys := keys node in
      rw_rq_table_add_source encoder actual_keys id table
    end) ids Map.empty.

Definition rw_rq_prepare_source {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (g : rw_graph K Sort V) :
    rw_rq_source K Sort V (rw_index K * Map.t rw_id (list rw_id)) :=
  rqlet ops := rw_rq_build_table_source (rw_rq_operator_encode op)
    rw_rq_operator_keys_source g (rw_nodes_in g) in
  rqlet children := rw_rq_build_table_source rw_rq_positive_encode
    rw_rq_child_keys_source g (rw_nodes_in g) in
  rqlet roots := rw_rq_build_table_source rw_rq_positive_encode
    (rw_rq_root_keys_source g) g (rw_nodes_in g) in
  rqlet variables := rw_rq_build_table_source rw_rq_positive_encode
    (rw_rq_variable_keys_source op sort value) g (rw_nodes_in g) in
  rw_rq_return 1052 (RwIndex ops children roots, variables).

Definition rw_rq_partners_source {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (base : rw_graph K Sort V)
    (ix : rw_index K) (vars : Map.t rw_id (list rw_id)) (id : rw_id) : rw_rq_source K Sort V (list
    rw_id) :=
  rqlet found := rw_rq_node_source base id in
  match found with
  | None => rw_rq_return 1053 nil
  | Some (_, RWNVar s v) =>
    rqlet key := rw_rq_node_encode op sort value (RWNVar s v) in
    rqlet code := rw_rq_positive_encode key in
    rqlet bucket := rw_rq_map_code_get code vars in
    rw_rq_return 1054 (
      match bucket with
      | None => nil
      | Some ids => ids
      end)
  | Some (_, RWNApp _ k _) =>
    rqlet code := rw_rq_operator_encode op k in
    rqlet bucket := rw_rq_map_code_get code (rw_index_ops ix) in
    rw_rq_return 1055 (
      match bucket with
      | None => nil
      | Some ids => ids
      end)
  end.

Definition rw_rq_initial_source {K Sort V} (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (base : rw_graph K Sort V)
    (ix : rw_index K) (vars : Map.t rw_id (list rw_id)) : rw_rq_source K Sort V (rw_pending_queue *
    nat) :=
  rw_rq_source_fold_right (fun id state =>
    rqlet partners := rw_rq_partners_source op sort value base ix vars id in
    rw_rq_source_fold_right (fun other current =>
      let '(queue, count) := current in
      rqlet next := rw_rq_insert_source (id, other) queue in
      rw_rq_return 1056 (next, S count)) partners state)
    (rw_nodes_in base) (rw_pending_empty, 0).

Definition rw_rq_parent_source {K Sort V} (g : rw_graph K Sort V) (ix : rw_index K) (id : rw_id) :
    rw_rq_source K Sort V (list rw_id) :=
  rqlet found := rw_rq_find_source g id in
  match found with
  | None => rw_rq_return 1057 nil
  | Some root =>
    rqlet code := rw_rq_positive_encode root in
    rqlet found_bucket := rw_rq_map_code_get code (rw_index_root_parents ix) in
    rw_rq_return 1058 (
      match found_bucket with
      | None => nil
      | Some ids => ids
      end)
  end.

Definition rw_rq_index_update_source {K Sort V} (g g' : rw_graph K Sort V) (ix : rw_index K)
    (a b : rw_id) : rw_rq_source K Sort V (rw_index K) :=
  rqlet first := rw_rq_find_source g a in
  match first with
  | None => rw_rq_return 1059 ix
  | Some ra =>
    rqlet second := rw_rq_find_source g b in
    match second with
    | None => rw_rq_return 1060 ix
    | Some rb =>
      rqlet new_root := rw_rq_find_source g' a in
      match new_root with
      | None => rw_rq_return 1061 ix
      | Some root =>
        let before := rw_index_root_parents ix in
        rqlet first_bucket := rw_rq_map_code_get ra before in
        rqlet second_bucket := rw_rq_map_code_get rb before in
        let xs :=
          match first_bucket with
          | None => nil
          | Some ids => ids
          end in
        let ys :=
          match second_bucket with
          | None => nil
          | Some ids => ids
          end in
        rqlet joined := rw_rq_source_append xs ys in
        rqlet unique := rw_rq_id_nodup_source joined in
        rqlet removed_a := rw_rq_code_remove ra before in
        rqlet without := rw_rq_code_remove rb removed_a in
        rqlet updated := rw_rq_code_set root (root, unique) without in
        rw_rq_return 1062 (RwIndex (rw_index_ops ix) (rw_index_parents ix) updated)
      end
    end
  end.

Definition rw_rq_change_keys_source {K Sort V A} (g : rw_graph K Sort V) (keys : rw_node K Sort V ->
    rw_rq_source K Sort V (list A)) (id : rw_id) : rw_rq_source K Sort V (list A) :=
  rqlet found := rw_rq_node_source g id in
  match found with
  | None => rw_rq_return 1063 nil
  | Some (_, node) => keys node
  end.

Definition rw_rq_change_table_source {K Sort V A} (encoder : A -> rw_rq_source K Sort V positive)
    (g g' : rw_graph K Sort V)
    (old_keys new_keys : rw_node K Sort V -> rw_rq_source K Sort V (list A))
    (table : Map.t A (list rw_id)) (id : rw_id) : rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rqlet new := rw_rq_change_keys_source g' new_keys id in
  rqlet old := rw_rq_change_keys_source g old_keys id in
  rqlet removed := rw_rq_table_remove_source encoder old id table in
  rw_rq_table_add_source encoder new id removed.

Definition rw_rq_change_index_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (g g' : rw_graph K Sort V) (ix : rw_index K) (id : rw_id) :
    rw_rq_source K Sort V (rw_index K) :=
  rqlet ops := rw_rq_change_table_source (rw_rq_operator_encode op) g g'
    rw_rq_operator_keys_source rw_rq_operator_keys_source (rw_index_ops ix) id in
  rqlet children := rw_rq_change_table_source rw_rq_positive_encode g g'
    rw_rq_child_keys_source rw_rq_child_keys_source (rw_index_parents ix) id in
  rqlet roots := rw_rq_change_table_source rw_rq_positive_encode g g'
    (rw_rq_root_keys_source g) (rw_rq_root_keys_source g') (rw_index_root_parents ix) id in
  rw_rq_return 1064 (RwIndex ops children roots).

Definition rw_rq_final_one_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (g : rw_graph K Sort V) (ix : rw_index K) (id : rw_id) :
    rw_rq_source K Sort V (rw_graph K Sort V * rw_index K) :=
  rqlet found := rw_rq_node_source g id in
  match found with
  | None => rw_rq_return 1065 (g, ix)
  | Some (owner, node) =>
    rqlet canonical := rw_rq_canon_node_source g node in
    rqlet nodes := rw_rq_code_set id (id, (owner, canonical)) (rw_nodes g) in
    let next := RwGraph (rw_roots g) (rw_nodes_in g) (rw_class_roots g) (rw_sorts g) nodes in
    rqlet next_index := rw_rq_change_index_source op g next ix id in
    rw_rq_return 1066 (next, next_index)
  end.

Fixpoint rw_rq_final_all_source {K Sort V} (op : rw_queue_encoder_adapter K) (ids : list rw_id)
    (g : rw_graph K Sort V) (ix : rw_index K) :
    rw_rq_source K Sort V (rw_graph K Sort V * rw_index K) :=
  match ids with
  | nil => rw_rq_return 1067 (g, ix)
  | id :: rest =>
    rqlet next := rw_rq_final_one_source op g ix id in
    let '(graph, index) := next in rw_rq_final_all_source op rest graph index
  end.
