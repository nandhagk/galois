(** * RewriteAuditProofInterfaceRpFactfulApplyRealizesStatement

    This module relates audited factful apply to its tracked interface.
    For example, a rejected tracked apply makes the local factful apply return None.
    Builds on: RewriteAuditProofRealizations and
    RewriteAuditProofSemantic. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexProgramLaws RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofPlainPublic RewriteAuditProofRealizations
  RewriteAuditProofSemantic RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Variable rw_tracked_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

Let rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

Let rw_tracked_factful_apply {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (position : nat)
    (input : rw_tracked_state K Sort V H * Map.t rw_id F)
    (attempt : rw_attempt K Sort V H) :=
  let '(state, facts) := input in
  match rw_tracked_apply EK ES EV EH sig rules position state attempt with
  | None => None
  | Some (next, events) => Some ((next, rw_facts_invalidate facts), events)
  end.

(** When encoders and rule callbacks agree, the erased factful apply observer equals
    the public tracked factful apply result. *)
Definition rw_rp_factful_apply_realizes_statement : Prop :=
  forall K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules position
    (input : rw_tracked_state K Sort V H * Map.t rw_id F) attempt,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules ->
    fst (rw_rp_factful_apply_atomic EK ES EV op sort value hole callbacks rules position input
      attempt) = rw_tracked_factful_apply EK ES EV EH sig rules position input attempt.

End FuturePublicImplementations.
