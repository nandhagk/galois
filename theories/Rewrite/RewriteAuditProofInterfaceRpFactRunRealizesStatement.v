(** * RewriteAuditProofInterfaceRpFactRunRealizesStatement

    This module states agreement of the audited factful runner with a public runner.
    For example, at fuel 0 its equality compares both results for the same input fact map,
    under encoder, callback, and fact-strategy agreement.
    Builds on: RewriteAuditProofFacts and
    RewriteAuditProofFactPublic. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexProgramLaws RewriteAuditIndexRules
  RewriteAuditProofFactPublic RewriteAuditProofFacts RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditProofSemantic RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_factful_run : forall {K Sort V H C F},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> rw_analysis K Sort V C F ->
  (rw_fact_view K Sort V F -> option (rw_attempt K Sort V H)) -> N ->
  rw_tracked_state K Sort V H * Map.t rw_id F ->
  rw_tracked_output K Sort V H * Map.t rw_id F.

(** When encoders, rule callbacks, and fact strategies agree, the erased factful run
    observer yields the public factful run result. *)
Definition rw_rp_fact_run_realizes_statement : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules (an : rw_analysis K Sort V C F)
    adapter strategy fuel input,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules ->
    rw_rp_fact_strategy_agrees EK ES EV an adapter strategy ->
    fst (rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks rules (rw_fact_unknown an)
      adapter fuel input) = rw_factful_run EK ES EV EH sig rules an strategy fuel input.

End FuturePublicImplementations.
