(** * RewriteAuditProofSelectedContracts

    States prospective work bounds for selected explanations and representation search.
    For example, the selected bound requires atom bounds for both endpoints even when both are the
    same variable.
    Builds on: RewriteAuditProofSelected and
    RewriteAuditProofWholeContracts. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexExternal
  RewriteAuditIndexReference RewriteAuditProofDimensions2 RewriteAuditProofRepresentation
  RewriteAuditProofSelected RewriteAuditProofTick RewriteAuditProofWholeContracts
  RewriteAuditQueueReference.
Import List.ListNotations.

(** Given index, provenance, seed, and tree atom bounds, selected-explanation work
    is bounded by the stated dimension-dependent expression. *)
Definition rw_rp_selected_bound_statement : Prop :=
  forall K Sort V H (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_tracked_state K Sort V H)
    root seed tree width body,
    rw_whole_index_atoms op sort value width body (rw_tracked_machine state) ->
    rw_whole_provenance_atoms op sort value width body (rw_tracked_provenance state) ->
    rw_whole_term_atoms op sort value width body seed ->
    rw_whole_term_atoms op sort value width body tree ->
    let dimension := S (rw_whole_tracked_dimension state + Pos.size_nat root +
      rw_whole_term_dimension seed + rw_whole_term_dimension tree + width) in
    (N.of_nat (snd (rw_rp_selected_atomic op sort value state root seed tree)) <=
      4294967296 * (1 + N.of_nat body) * N.pow (N.of_nat dimension)
        (128 + 16 * N.of_nat (rw_whole_term_dimension seed + rw_whole_term_dimension tree)))%N.

(** Given index and term atom bounds, representation-search work is bounded by the
    stated dimension-dependent expression. *)
Definition rw_rp_repr_find_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_index_state K Sort V) root term width body,
    rw_whole_index_atoms op sort value width body state ->
    rw_whole_term_atoms op sort value width body term ->
    let dimension := S (rw_whole_index_dimension state + Pos.size_nat root +
      rw_whole_term_dimension term + width) in
    (N.of_nat (snd (rw_rp_repr_find_atomic op sort value state root term)) <=
      4294967296 * (1 + N.of_nat body) * N.pow (N.of_nat dimension)
        (64 + 16 * N.of_nat (rw_whole_term_dimension term)))%N.
