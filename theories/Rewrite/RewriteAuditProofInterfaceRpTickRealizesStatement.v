(** * RewriteAuditProofInterfaceRpTickRealizesStatement

    States prospective realization of a tracked tick by its counted source observer.
    For example, under the three encoder agreements, a None source tick must match the public tick
    at the same stamp.
    Builds on: RewriteAuditProofTick and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_tick : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  (nat * nat) -> rw_tracked_state K Sort V H ->
  option (rw_tracked_state K Sort V H * rw_index_event).

(** When operator, sort, and value adapters agree, erasing tick work yields the public
    tracked tick result. *)
Definition rw_rp_tick_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) stamp (state : rw_tracked_state K Sort V H),
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_rp_tick_atomic op sort value stamp state) = rw_tracked_tick EK ES EV stamp state.

End FuturePublicImplementations.
