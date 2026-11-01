(** * RewriteAuditIndexInterfaceRiRunRealizesStatement

    This module states the prospective correspondence between an index run and its observer.
    For example, its zero-fuel case compares the input graph and empty event lists under the laws.
    Builds on: RewriteAuditIndexProgramLaws and
    RewriteAuditIndexRun. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexProgramLaws
  RewriteAuditIndexPrograms RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditIndexRun RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

(** When encoders and callbacks agree and the strategy adapter agrees and has its
    execution witness, erasing the run observer yields the public index run and events. *)
Definition rw_ri_run_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules
    (adapter : rw_rp_strategy_adapter K Sort V H) strategy execution fuel graph,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules ->
    rw_rp_strategy_adapter_laws EK ES EV adapter strategy execution ->
    fst (rw_ri_run_atomic op sort value hole callbacks rules adapter fuel graph) =
      rw_index_run EK ES EV EH sig rules strategy fuel graph.

End FuturePublicImplementations.
