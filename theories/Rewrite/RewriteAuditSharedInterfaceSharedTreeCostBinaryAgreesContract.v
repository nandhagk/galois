(** * RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContract

    This module states the prospective agreement of binary shared-tree cost and unfolding.
    For example, a well-formed singleton DAG whose root 1 maps to a variable of natural sort 0
    and value 0 and unfolds to it must return binary cost 3 when that variable costs 3.
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

Variable rw_shared_tree_cost_binary : forall {K Sort V}, (V -> nat) -> (K -> nat) ->
  rw_shared_tree K Sort V -> option N.

(** A well-formed shared tree with a successful unfolding has the unfolded cost in binary. *)
Definition rw_shared_tree_cost_binary_agrees_contract : Prop :=
  forall K Sort V (vc : V -> nat) (oc : K -> nat) (dag : rw_shared_tree K Sort V)
    (tree : rw_term K Sort V),
    rw_shared_wf dag ->
    rw_shared_unfold dag = Some tree ->
    rw_shared_tree_cost_binary vc oc dag = Some (N.of_nat (rw_tree_cost vc oc tree)).

End FuturePublicImplementations.
