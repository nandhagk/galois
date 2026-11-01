(** * RewriteAuditIndexInterfaceRiApplyRealizesStatement

    States the prospective realization of index application by its counted source observer.
    For example, under encoder and callback agreement, a rejected application must produce the same
    None result.
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
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditIndexRun
  RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).

Let rw_index_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :=
  match rw_index_rule_step EK ES EV EH sig rules state attempt with
  | None => None
  | Some intermediate => Some (rw_index_rebuild EK ES EV intermediate)
  end.

(** When encoder adapters and rule callbacks agree with their plain counterparts, erasing
    the apply observer yields the public index apply result and rebuild events. *)
Definition rw_ri_apply_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules state attempt,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules ->
    fst (rw_ri_apply_atomic op sort value hole callbacks rules state attempt) =
      rw_index_apply EK ES EV EH sig rules state attempt.

End FuturePublicImplementations.
