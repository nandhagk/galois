(** * RewriteAuditSharedInterfaceSharedObserversRejectContract

    This module states prospective rejection contracts for shared-tree observers.
    For example, an empty node map is malformed, so the contract requires the binary-size
    observer and unfolding to return None.
    Builds on: RewriteAuditSharedReference and
    NArith. *)

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

Variable rw_shared_tree_cost_binary : forall {K Sort V}, (V -> nat) -> (K -> nat) ->
  rw_shared_tree K Sort V -> option N.

Variable rw_shared_tree_size_binary : forall {K Sort V}, rw_shared_tree K Sort V -> option N.

(** Unfolding, cost, binary cost, and binary size all reject a malformed shared tree. *)
Definition rw_shared_observers_reject_contract : Prop :=
  forall K Sort V (vc : V -> nat) (oc : K -> nat) (dag : rw_shared_tree K Sort V),
    ~ rw_shared_wf dag ->
    rw_shared_unfold dag = None /\
    rw_shared_tree_cost vc oc dag = None /\
    rw_shared_tree_cost_binary vc oc dag = None /\
    rw_shared_tree_size_binary dag = None.

End FuturePublicImplementations.
