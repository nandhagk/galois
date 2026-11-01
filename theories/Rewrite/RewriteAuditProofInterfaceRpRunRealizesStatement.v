(** * RewriteAuditProofInterfaceRpRunRealizesStatement

    This module states agreement between an audited run and a public tracked run.
    For example, at fuel 0 the claim equates the public result to the work-erased source result,
    provided the encoder, callback, and strategy laws hold.
    Builds on: RewriteAuditProofRun and
    RewriteAuditIndexProgramLaws. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},
    encoding K -> encoding Sort -> encoding V -> encoding H ->
    rw_signature K Sort V -> list (rw_rule K Sort V H) ->
    (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->
    N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

(** When encoders and rule callbacks agree and the strategy adapter agrees and has its
    execution witness, the erased run observer equals the public tracked run. *)
Definition rw_rp_run_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V) rules
    (adapter : rw_rp_strategy_adapter K Sort V H) strategy execution fuel seed,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules ->
    rw_rp_strategy_adapter_laws EK ES EV adapter strategy execution ->
    fst (rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed) =
      rw_tracked_run EK ES EV EH sig rules strategy fuel seed.

End FuturePublicImplementations.
