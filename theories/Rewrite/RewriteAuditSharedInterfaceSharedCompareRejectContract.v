(** * RewriteAuditSharedInterfaceSharedCompareRejectContract

    This module states the prospective rejection contract for shared-tree comparison.
    For example, it requires rejection when the left tree has an empty node map.
    Builds on: RewriteAuditSharedReference and
    CollectionsEncoding. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_compare : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  rw_shared_tree K Sort V -> rw_shared_tree K Sort V -> option bool.

(** Comparison returns None if either shared tree is not well formed. *)
Definition rw_shared_compare_reject_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (left right : rw_shared_tree K Sort V),
    ~ rw_shared_wf left \/ ~ rw_shared_wf right ->
    rw_shared_compare EK ES EV left right = None.

End FuturePublicImplementations.
