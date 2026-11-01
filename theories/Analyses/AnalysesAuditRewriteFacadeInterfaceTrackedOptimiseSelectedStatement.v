(** * AnalysesAuditRewriteFacadeInterfaceTrackedOptimiseSelectedStatement

    This module states the selected-output guarantee for the tracked optimizer interface.
    For example, with seed cost 0, the proposed result includes a checked explanation and
    an extracted output with cost at most 0.
    Builds on: AnalysesAuditRewriteFacadeRun and
    RewriteAuditSharedReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeRun.
From Galois.Rewrite Require Import RewriteAuditProofRun RewriteAuditProofSemantic
  RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_legacy_tracked : forall K, encoding K -> list (rewrite_rule K) -> positive ->
  term K -> rw_legacy_tracked_state K.

Variable rw_legacy_selected_explanation : forall K, encoding K -> list (rewrite_rule K) -> term K ->
  rw_legacy_tracked_state K -> term K -> option (list (rewrite_step K)).

Variable rw_tracked_optimise : forall K, encoding K -> list (rewrite_rule K) -> (K -> nat) ->
  positive -> term K -> option (rw_shared_tree K unit nat * list (rewrite_step K)).

(** The tracked optimizer returns a shared DAG and checked explanation for an extracted
    output whose cost is at most the seed cost. *)
Definition rw_tracked_optimise_selected_statement : Prop :=
  forall K (EK : encoding K) rules cost fuel seed,
    let legacy := rw_legacy_tracked K EK rules fuel seed in
    exists dag steps output,
      rw_tracked_optimise K EK rules cost fuel seed = Some (dag, steps) /\
      rw_shared_unfold dag = Some (legacy_embed output) /\
      rw_extract_tree EK unit_encoding nat_encoding (fun _ => 0) cost
        (rw_tracked_graph (rw_tracked_final (rw_legacy_core K legacy)))
        (rw_legacy_root K legacy) = Some (legacy_embed output) /\
      rw_legacy_selected_explanation K EK rules seed legacy output = Some steps /\
      check_explanation EK rules seed output steps = true /\
      term_cost cost output <= term_cost cost seed.

End FuturePublicImplementations.
