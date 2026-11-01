(** * RewriteAuditIndexBuild

    This module builds the operator, variable, and parent buckets of an index.
    For example, an empty node-id list leaves the build accumulator unchanged.
    Builds on: RewriteEgraph and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference.
Import List.ListNotations.

Record rw_ri_build_acc (K V : Type) := RwRiBuildAcc {
  rw_ri_build_ops : Map.t K (FinSet.t rw_id);
  rw_ri_build_vars : Map.t V (FinSet.t rw_id);
  rw_ri_build_parents : Map.t rw_id (FinSet.t rw_id)
}.
Arguments RwRiBuildAcc {K V}.
Arguments rw_ri_build_ops {K V}.
Arguments rw_ri_build_vars {K V}.
Arguments rw_ri_build_parents {K V}.

Definition rw_ri_bucket_add {A} (E : encoding A) (key : A) (id : rw_id)
    (table : Map.t A (FinSet.t rw_id)) : Map.t A (FinSet.t rw_id) :=
  Map.set E key (FinSet.add positive_encoding id (rw_index_bucket E key table)) table.

Fixpoint rw_ri_build_parent_nodes_value {K Sort V} (g : rw_graph K Sort V) (id : rw_id)
    (children : list rw_id) (table : Map.t rw_id (FinSet.t rw_id)) : Map.t rw_id (FinSet.t rw_id) :=
  match children with
  | nil => table
  | child :: rest =>
    match rw_find g child with
    | None => rw_ri_build_parent_nodes_value g id rest table
    | Some root => rw_ri_build_parent_nodes_value g id rest (rw_ri_bucket_add positive_encoding
      root id table)
    end
  end.

Fixpoint rw_ri_build_nodes_value {K Sort V} (EK : encoding K) (EV : encoding V)
    (g : rw_graph K Sort V) (ids : list rw_id) (acc : rw_ri_build_acc K V) : rw_ri_build_acc K V :=
  match ids with
  | nil => acc
  | id :: rest =>
    match rw_node_at g id with
    | None => rw_ri_build_nodes_value EK EV g rest acc
    | Some (_, RWNVar _ v) =>
      rw_ri_build_nodes_value EK EV g rest
        (RwRiBuildAcc (rw_ri_build_ops acc) (rw_ri_bucket_add EV v id (rw_ri_build_vars acc))
          (rw_ri_build_parents acc))
    | Some (_, RWNApp _ op children) =>
      let ops := rw_ri_bucket_add EK op id (rw_ri_build_ops acc) in
      let parents := rw_ri_build_parent_nodes_value g id children (rw_ri_build_parents acc) in
      rw_ri_build_nodes_value EK EV g rest (RwRiBuildAcc ops (rw_ri_build_vars acc) parents)
    end
  end.
