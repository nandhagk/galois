(** * RewriteAuditSharedInterfaceRdExtractRealizesStatement

    This module states the prospective realization of shared extraction by its source run.
    For example, with agreeing encoders, a value callback returning (3, 7) supplies cost 3
    to the public extraction used in the statement.
    Builds on: RewriteAuditSharedExtract and
    RewriteAuditSharedBoundsContracts. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedBoundsContracts
  RewriteAuditSharedExtract RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_extract : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  (V -> nat) -> (K -> nat) -> rw_graph K Sort V -> rw_id -> option (rw_shared_tree K Sort V).

(** If the encoder adapters agree, extraction has a source run returning the public result
    with work bounded by the extraction budget. *)
Definition rw_rd_extract_realizes_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (vc : V -> nat * nat) (oc : K -> nat * nat) g root,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    exists work,
      rw_shared_extract_run op sort value vc oc g root
        (rw_shared_extract EK ES EV (fun v => fst (vc v)) (fun k => fst (oc k)) g root) work /\
      work <= rw_rd_extract_budget op sort value vc oc g root.

End FuturePublicImplementations.
