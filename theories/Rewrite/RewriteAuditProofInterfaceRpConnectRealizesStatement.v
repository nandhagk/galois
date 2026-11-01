(** * RewriteAuditProofInterfaceRpConnectRealizesStatement

    States prospective realization of class connection by its counted source observer.
    For example, under the three encoder agreements, a None source result must match the public
    connection result.
    Builds on: RewriteAuditProofClosure and
    RewriteAuditProofRepresentation. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofCarrier RewriteAuditProofClosure
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_connect_class : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).

(** When the operator, sort, and value adapters agree, erasing connection work
    yields the public class-connection result for the supplied endpoints. *)
Definition rw_rp_connect_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (graph : rw_graph K Sort V)
    (proof : rw_provenance K Sort V H) root lhs rhs witness,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_rp_connect_atomic op sort value proof lhs rhs) =
      rw_connect_class EK ES EV EH graph proof root lhs rhs witness.

End FuturePublicImplementations.
