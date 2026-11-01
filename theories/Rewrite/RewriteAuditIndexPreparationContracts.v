(** * RewriteAuditIndexPreparationContracts

    This module states a whole-graph bound on the work of preparing an index.
    For example, with zero width and body budgets, the ceiling is 65536 times the
    sixteenth power of one plus the graph dimension.
    Builds on: RewriteAuditIndexExternal and
    RewriteAuditIndexPrepare. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexExternal
  RewriteAuditIndexPrepare RewriteAuditQueueReference.
Import List.ListNotations.

(** Given the whole-graph atom bounds, preparation work is bounded by the graph dimension,
    encoding width, and atom body budget. *)
Definition rw_ri_prepare_once_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (graph : rw_graph K Sort V) width body,
    rw_whole_graph_atoms op sort value width body graph ->
    (N.of_nat (rw_ri_prepare_once_work (snd (rw_ri_prepare_once op value graph))) <=
      65536 * (1 + N.of_nat body) *
      N.pow (N.of_nat (S (rw_whole_graph_dimension graph + width))) 16)%N.
