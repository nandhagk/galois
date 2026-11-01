(** * RewriteAuditProofInterfaceRpSelectedRealizesStatement

    States prospective realization of selected explanations by a counted source observer.
    For example, under the three encoder agreements, a None source result must match the public
    explanation result.
    Builds on: RewriteAuditProofSelected and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofCarrier RewriteAuditProofPlainPublic
  RewriteAuditProofSelected RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_selected_explanation : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> rw_tracked_state K Sort V H -> rw_id ->
  rw_term K Sort V -> rw_term K Sort V -> option (rw_provenance K Sort V H * positive).

(** When operator, sort, and value adapters agree, erasing selected-observer work yields
    the public explanation for the same state, root, seed, and tree. *)
Definition rw_rp_selected_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_tracked_state K Sort V H) root seed tree,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_rp_selected_atomic op sort value state root seed tree) =
      rw_selected_explanation EK ES EV state root seed tree.

End FuturePublicImplementations.
