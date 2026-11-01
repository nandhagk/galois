(** * AnalysesAuditRewriteFacadeInterfaceSelectedExplanationAcceptsStatement

    This module states the checker acceptance requirement for a selected explanation.
    For example, if extraction returns the embedding of variable 0, some explanation for
    variable 0 must be returned and accepted by the checker.
    Builds on: AnalysesAuditRewriteFacadeRun and
    RewriteExtract. *)

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
From Galois.Rewrite Require Import RewriteAuditProofRun RewriteAuditProofSemantic.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_legacy_tracked : forall K, encoding K -> list (rewrite_rule K) -> positive ->
  term K -> rw_legacy_tracked_state K.

Variable rw_legacy_selected_explanation : forall K, encoding K -> list (rewrite_rule K) -> term K ->
  rw_legacy_tracked_state K -> term K -> option (list (rewrite_step K)).

(** If extraction from the legacy run returns the embedded output, some selected
    explanation is returned and accepted by the original checker. *)
Definition rw_selected_explanation_accepts_statement : Prop :=
  forall K (EK : encoding K) rules fuel seed cost output,
    let legacy := rw_legacy_tracked K EK rules fuel seed in
    rw_extract_tree EK unit_encoding nat_encoding (fun _ => 0) cost
      (rw_tracked_graph (rw_tracked_final (rw_legacy_core K legacy)))
      (rw_legacy_root K legacy) = Some (legacy_embed output) ->
    exists steps,
      rw_legacy_selected_explanation K EK rules seed legacy output = Some steps /\
      check_explanation EK rules seed output steps = true.

End FuturePublicImplementations.
