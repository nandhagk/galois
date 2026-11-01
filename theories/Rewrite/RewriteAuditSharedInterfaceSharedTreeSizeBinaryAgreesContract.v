(** * RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContract

    This module states the prospective binary-size agreement for shared trees.
    For example, a well-formed singleton DAG whose root 1 maps to a variable of natural sort 0
    and value 0 and unfolds to it must have binary size 1.
    Builds on: RewriteAuditSharedReference and
    RewriteExtract. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedPlain RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_tree_size_binary : forall {K Sort V}, rw_shared_tree K Sort V -> option N.

(** A well-formed shared tree with a successful unfolding has the unfolded size in binary. *)
Definition rw_shared_tree_size_binary_agrees_contract : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V) tree,
    rw_shared_wf dag ->
    rw_shared_unfold dag = Some tree ->
    rw_shared_tree_size_binary dag = Some (N.of_nat (rw_tree_size tree)).

End FuturePublicImplementations.
