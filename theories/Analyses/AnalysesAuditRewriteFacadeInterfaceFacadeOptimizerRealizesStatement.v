(** * AnalysesAuditRewriteFacadeInterfaceFacadeOptimizerRealizesStatement

    This module states when a facade optimizer run realizes the public tracked optimizer.
    For example, under its adapter and guard laws, a source result of None must match
    the optimizer's None result.
    Builds on: AnalysesAuditRewriteFacadeOptimizer and
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
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeOptimizer
  AnalysesAuditRewriteFacadePrepare.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_optimise : forall K, encoding K -> list (rewrite_rule K) -> (K -> nat) ->
  positive -> term K -> option (rw_shared_tree K unit nat * list (rewrite_step K)).

(** When the operator adapter agrees and guard program laws hold, a facade optimizer
    run returns the public tracked optimizer result. *)
Definition rw_facade_optimizer_realizes_statement : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard cost rules fuel seed
    result work dimension,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    rw_facade_optimizer_run EK op guard cost rules fuel seed result work dimension ->
    result = rw_tracked_optimise K EK rules (fun k => fst (cost k)) fuel seed.

End FuturePublicImplementations.
