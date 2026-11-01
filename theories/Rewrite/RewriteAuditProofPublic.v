(** * RewriteAuditProofPublic

    This module states callback and zero-fuel properties of tracked source runs.
    For example, its zero-fuel claim specifies an empty event list and fuel exhaustion.
    Builds on: RewriteAuditProofRun and
    RewriteAuditProofSeed. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRules RewriteAuditProofRun
  RewriteAuditProofSeed RewriteAuditQueueReference.
Import List.ListNotations.

(** The tracked source run event count plus one when stopped is bounded by its fuel. *)
Definition rw_rp_run_callback_bound_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules adapter fuel seed,
    let '((_, output), _) :=
      rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed in
    (N.of_nat (length (rw_tracked_events output)) +
      match rw_tracked_stop output with
      | RWStopped => 1%N
      | RWFuelExhausted => 0%N
      end <= fuel)%N.

(** Zero-fuel tracked source execution returns the seeded state with no events,
    fuel exhaustion, and seed work plus 64. *)
Definition rw_rp_run_zero_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules adapter seed,
    let '((root, state), seed_work) := @rw_rp_seed_atomic K Sort V H EK ES EV op value seed in
    rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter 0%N seed =
      ((root, RwTrackedOutput state RWFuelExhausted nil nil), 64 + seed_work).
