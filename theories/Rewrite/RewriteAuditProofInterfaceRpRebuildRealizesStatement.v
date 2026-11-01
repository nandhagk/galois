(** * RewriteAuditProofInterfaceRpRebuildRealizesStatement

    This module states agreement between audited and public tracked rebuilds.
    For example, with agreeing adapters, the result at group 0 is required to match
    after erasing the source work.
    Builds on: RewriteAuditProofRebuild and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRebuild RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

(** When operator, sort, and value adapters agree, the erased rebuild observer yields
    the public tracked rebuild state and events. *)
Definition rw_rp_rebuild_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) group (state : rw_tracked_state K Sort V H),
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_rp_rebuild_atomic op sort value group state) = rw_tracked_rebuild EK ES EV group state.

End FuturePublicImplementations.
