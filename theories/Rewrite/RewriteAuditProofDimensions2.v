(** * RewriteAuditProofDimensions2

    This module measures witness stores and tracked states for whole-operation bounds.
    For example, the witness-node fold starts at 1 when the node map is empty.
    Builds on: RewriteAuditProofDimensions and
    RewriteAuditSharedReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions2
  RewriteAuditProofDimensions RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_whole_witness_dimension {K Sort V} (store : rw_class_witness_store K Sort V) : nat :=
  let nodes := rw_class_witness_nodes store in
  S (rw_whole_map_dimension Pos.size_nat rw_whole_shared_node_dimension nodes +
    rw_whole_map_dimension Pos.size_nat Pos.size_nat (rw_class_witness_roots store) +
    fold_right (fun entry total =>
      match rw_shared_unfold (RwSharedTree K Sort V (fst entry) nodes) with
      | None => S total
      | Some term => S (rw_whole_term_dimension term + total)
      end) 1 (Map.elements nodes)).

Definition rw_whole_tracked_dimension {K Sort V H} (state : rw_tracked_state K Sort V H) : nat :=
  S (rw_whole_index_dimension (rw_tracked_machine state) +
    rw_whole_provenance_dimension (rw_tracked_provenance state) +
    rw_whole_witness_dimension (rw_tracked_witnesses state) +
    rw_whole_map_dimension (fun stamp => S (fst stamp + snd stamp)) Pos.size_nat
      (rw_tracked_event_nodes state)).
