(** * RewriteAuditIndexDimensions3

    Measures the largest attempt dimension among recorded run events.
    For example, an empty event list has dimension 1.
    Builds on: RewriteAuditIndexDimensions and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexReference.
Import List.ListNotations.

Definition rw_whole_event_attempt_dimension {K Sort V H} (events : list (rw_run_event K Sort V H)) :
    nat :=
  fold_right (fun event largest =>
    Nat.max largest (
      match event with
      | RWRunRejected attempt => rw_whole_attempt_dimension attempt
      | RWRunAccepted attempt _ => rw_whole_attempt_dimension attempt
      end)) 1 events.
