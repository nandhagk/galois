(** * RewriteAuditProofDimensions

    Measures evidence reasons and provenance for tracked source bounds.
    For example, a reflexivity reason has dimension 1.
    Builds on: RewriteAuditIndexDimensions and
    RewriteAuditProofCarrier. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditProofCarrier.
Import List.ListNotations.

Definition rw_whole_reason_dimension {K Sort V H} (reason : rw_evidence_reason K Sort V H) : nat :=
  match reason with
  | RWEvidenceRefl => 1
  | RWEvidenceRule index bindings => S (index + rw_whole_bindings_dimension bindings)
  | RWEvidenceSym child => S (Pos.size_nat child)
  | RWEvidenceTrans first second => S (Pos.size_nat first + Pos.size_nat second)
  | RWEvidenceCongruence children => S (rw_whole_ids_dimension children)
  end.

Definition rw_whole_provenance_dimension {K Sort V H} (proof : rw_provenance K Sort V H) : nat :=
  S (rw_whole_ids_dimension (rw_provenance_ids proof) +
    rw_whole_map_dimension Pos.size_nat (fun node =>
      rw_whole_term_dimension (rw_evidence_left node) +
      rw_whole_term_dimension (rw_evidence_right node) +
      rw_whole_reason_dimension (rw_evidence_reason_of node) +
      fst (rw_evidence_time node) + snd (rw_evidence_time node)) (rw_provenance_nodes proof)).
