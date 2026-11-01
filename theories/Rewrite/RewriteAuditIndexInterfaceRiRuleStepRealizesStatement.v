(** * RewriteAuditIndexInterfaceRiRuleStepRealizesStatement

    This module relates the audited rule step to the public index rule-step interface.
    For example, with agreeing encoders and callbacks, a source rejection at rule index 0
    requires the public step to reject in the proposed equality.
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
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditIndexRun RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).

(** When encoder adapters and rule callbacks agree with their plain counterparts, erasing
    the rule-step observer yields the public index rule-step result. *)
Definition rw_ri_rule_step_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules state attempt,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules ->
    fst (rw_ri_rule_step_atomic op sort value hole callbacks rules state attempt) =
      rw_index_rule_step EK ES EV EH sig rules state attempt.

End FuturePublicImplementations.
