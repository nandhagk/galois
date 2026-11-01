(** * RewriteAuditSharedInterfaceSharedTreeCostAgreesContract

    This module states unary cost agreement between a shared tree and its unfolding.
    For example, if a well-formed shared tree unfolds to variable 0 and its variable cost is 3,
    the contract requires the result Some 3.
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

Variable rw_shared_tree_cost : forall {K Sort V}, (V -> nat) -> (K -> nat) ->
    rw_shared_tree K Sort V -> option nat.

(** A well-formed shared tree with a successful unfolding has the unfolded tree cost. *)
Definition rw_shared_tree_cost_agrees_contract : Prop :=
  forall K Sort V (vc : V -> nat) (oc : K -> nat) (dag : rw_shared_tree K Sort V)
    (tree : rw_term K Sort V),
    rw_shared_wf dag -> rw_shared_unfold dag = Some tree ->
    rw_shared_tree_cost vc oc dag = Some (rw_tree_cost vc oc tree).

End FuturePublicImplementations.
