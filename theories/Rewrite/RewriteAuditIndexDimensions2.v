(** * RewriteAuditIndexDimensions2

    This module measures the dimension of a shared node for whole-operation bounds.
    For example, every shared variable has dimension 1.
    Builds on: RewriteAuditIndexDimensions and
    RewriteAuditSharedReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_whole_shared_node_dimension {K Sort V} (node : rw_shared_node K Sort V) : nat :=
  match node with
  | RWSharedVar _ _ _ _ _ => 1
  | RWSharedApp _ _ _ _ _ children => S (rw_whole_ids_dimension children)
  end.
