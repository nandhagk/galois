(** * RewriteAuditIndexDimensions4

    Defines the dimension- and fuel-dependent ceiling for whole-source runs.
    For example, zero fuel and zero dimension, width, and body control give a ceiling of 4294967296.
    Builds on: binary natural arithmetic in NArith. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Definition rw_whole_source_ceiling (fuel : N) (dimension code_width body_control : nat) : N :=
  (4294967296 * (1 + fuel) * (1 + N.of_nat body_control) *
    N.pow (N.of_nat (S (dimension + code_width))) (128 + 16 * N.pow (N.of_nat dimension) 4))%N.
