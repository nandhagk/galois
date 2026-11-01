(** * AnalysesAuditRewriteFacadeInterfaceFacadeTrackedRealizesStatement

    This module states when a tracked facade run realizes the legacy tracked result.
    For example, with fuel 1 and seed variable 0, the source and legacy results must agree
    under the adapter and guard laws.
    Builds on: AnalysesAuditRewriteFacadeRun and
    AnalysesAuditRewriteFacadePrepare. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadePrepare AnalysesAuditRewriteFacadeRun.
From Galois.Rewrite Require Import RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_legacy_tracked : forall K, encoding K -> list (rewrite_rule K) -> positive ->
  term K -> rw_legacy_tracked_state K.

(** When the operator adapter agrees and guard program laws hold, a tracked facade
    run returns the legacy tracked result. *)
Definition rw_facade_tracked_realizes_statement : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard rules fuel seed legacy work
    dimension,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    rw_facade_tracked_run EK op guard rules fuel seed legacy work dimension ->
    legacy = rw_legacy_tracked K EK rules fuel seed.

End FuturePublicImplementations.
