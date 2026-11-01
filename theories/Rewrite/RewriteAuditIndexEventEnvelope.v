(** * RewriteAuditIndexEventEnvelope

    This module applies the external-attempt envelope to accepted and rejected run events.
    For example, a rejected event containing attempt a requires the envelope for a.
    Builds on: RewriteAuditIndexExternal and
    RewriteAuditIndexRules. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexExternal RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditQueueReference.
Import List.ListNotations.

(** The attempt of an accepted or rejected run event satisfies the external bounds. *)
Definition rw_whole_event_external {K Sort V H} (EH : encoding H) (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (width body : nat) (rules : list (rw_rule K Sort V H)) (event : rw_run_event K Sort V H) :
    Prop :=
  match event with
  | RWRunRejected attempt =>
    rw_whole_attempt_external EH op sort value hole callbacks width body rules attempt
  | RWRunAccepted attempt _ =>
    rw_whole_attempt_external EH op sort value hole callbacks width body rules attempt
  end.
