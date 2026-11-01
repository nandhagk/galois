(** * AnalysesAuditRewriteFacadeInterfaceFacadeSelectedRealizesStatement

    States the prospective correspondence between selected facade reconstruction and the legacy
    explanation.
    For example, under its adapter and guard laws, a source result must be None when the legacy
    explanation is None.
    Builds on: AnalysesAuditRewriteFacadeOptimizer and
    AnalysesAuditRewriteFacadeRun. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeOptimizer
  AnalysesAuditRewriteFacadePrepare AnalysesAuditRewriteFacadeRun.
From Galois.Rewrite Require Import RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_legacy_selected_explanation : forall K, encoding K -> list (rewrite_rule K) -> term K ->
  rw_legacy_tracked_state K -> term K -> option (list (rewrite_step K)).

(** When the operator adapter agrees and guard program laws hold, a selected facade
    run returns the legacy selected explanation. *)
Definition rw_facade_selected_realizes_statement : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard rules seed legacy output result
    work dimension,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    rw_facade_selected_run op guard rules seed legacy output result work dimension ->
    result = rw_legacy_selected_explanation K EK rules seed legacy output.

End FuturePublicImplementations.
