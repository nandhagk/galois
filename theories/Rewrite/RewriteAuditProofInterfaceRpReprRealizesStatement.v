(** * RewriteAuditProofInterfaceRpReprRealizesStatement

    This module states agreement between audited representation search and the public search.
    For example, with agreeing adapters, a None source result at root 1 requires a None
    public result in the proposed equality.
    Builds on: RewriteAuditProofRepresentation and
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
  RewriteAuditProofRepresentation RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_repr_find : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  rw_phase_view K Sort V -> rw_id -> rw_term K Sort V -> option (rw_repr_witness K Sort V).

(** When operator, sort, and value adapters agree, erasing representation-search work
    yields the representation search on the index snapshot. *)
Definition rw_rp_repr_realizes_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) state root term,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_rp_repr_find_atomic op sort value state root term) =
      rw_repr_find EK ES EV (rw_snapshot_base (rw_index_view EK ES EV state)) root term.

End FuturePublicImplementations.
