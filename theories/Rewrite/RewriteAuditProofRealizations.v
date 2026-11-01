(** * RewriteAuditProofRealizations

    This module combines audited tracked apply with fact invalidation.
    For example, at position 0, a None tracked apply for rule 0 at root 1 with an empty
    substitution makes factful apply return None.
    Builds on: RewriteAuditProofApply and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditProofApply RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

(** A successful tracked source apply returns its result with an empty fact map. *)
Definition rw_rp_factful_apply_atomic {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules position
    (input : rw_tracked_state K Sort V H * Map.t rw_id F) attempt :
    option ((rw_tracked_state K Sort V H * Map.t rw_id F) * list rw_index_event) * nat :=
  let '(state, _) := input in
  let '(applied, work) := rw_rp_apply_atomic EK ES EV op sort value hole callbacks
    rules position state attempt in
  (option_map (fun pair => ((fst pair, Map.empty), snd pair)) applied, 128 + work).
