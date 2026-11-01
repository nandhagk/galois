(** * RewriteAuditSharedInterfaceRdCompareRealizesStatement

    This module states bounded realization of the public shared-tree comparison.
    For example, with agreeing adapters, the claim asks for a bounded run comparing with itself
    the singleton DAG whose root 1 maps to a variable of natural sort 0 and value 0.
    Builds on: RewriteAuditSharedCompare and
    RewriteAuditSharedReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedCompare
  RewriteAuditSharedExtract RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_compare : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  rw_shared_tree K Sort V -> rw_shared_tree K Sort V -> option bool.

(** If the encoder adapters agree, comparison has a source run returning the public result
    with work bounded by the comparison budget. *)
Definition rw_rd_compare_realizes_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) lhs rhs,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    exists work,
      rw_shared_compare_run op sort value lhs rhs (rw_shared_compare EK ES EV lhs rhs) work /\
      work <= rw_rd_compare_budget op sort value lhs rhs.

End FuturePublicImplementations.
