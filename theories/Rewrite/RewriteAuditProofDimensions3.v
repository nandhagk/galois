(** * RewriteAuditProofDimensions3

    Combines seed, rule, final-state, and event dimensions for tracked-run bounds.
    For example, an empty event list contributes the event dimension 1.
    Builds on: RewriteAuditIndexDimensions3 and
    RewriteAuditProofDimensions2. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions3
  RewriteAuditProofDimensions2 RewriteAuditProofRun.
Import List.ListNotations.

Definition rw_rp_whole_operand_dimension {K Sort V H} (rules : list (rw_rule K Sort V H))
    (seed : rw_term K Sort V) (output : rw_tracked_output K Sort V H) : nat :=
  S (rw_whole_term_dimension seed + rw_whole_rules_dimension rules +
    rw_whole_tracked_dimension (rw_tracked_final output) +
    rw_whole_event_attempt_dimension (rw_tracked_events output)).
