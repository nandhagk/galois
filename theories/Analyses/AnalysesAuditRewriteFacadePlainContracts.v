(** * AnalysesAuditRewriteFacadePlainContracts

    These types instantiate facade contracts with the plain tracked and explanation builders.
    For example, if extraction returns embedded variable 0, the selected-explanation type
    requires an explanation accepted by the checker.
    Builds on: AnalysesAuditRewriteFacadePlainRun and
    AnalysesAuditRewriteFacadePlainExplain. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import
  AnalysesAuditRewriteFacadeInterfaceFacadeOptimizerRealizesStatement
  AnalysesAuditRewriteFacadeInterfaceFacadeSelectedRealizesStatement
  AnalysesAuditRewriteFacadeInterfaceFacadeTrackedRealizesStatement
  AnalysesAuditRewriteFacadeInterfaceLegacyRunLinkStatement
  AnalysesAuditRewriteFacadeInterfaceSelectedExplanationAcceptsStatement
  AnalysesAuditRewriteFacadeInterfaceTrackedOptimiseSelectedStatement
  AnalysesAuditRewriteFacadePlainExplain AnalysesAuditRewriteFacadePlainMaterializer
  AnalysesAuditRewriteFacadePlainRun.
From Galois.Rewrite Require Import RewriteAuditProofPlainPublic RewriteAuditSharedPlain.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** When the operator adapter agrees and guard program laws hold, a tracked facade
    run returns the legacy tracked result. *)
Definition rw_facade_tracked_realizes_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) :
    Prop :=
  @rw_facade_tracked_realizes_statement
    (@AnalysesAuditRewriteFacadePlainRun.rw_legacy_tracked_builder Hwf).

(** The legacy root and core equal the generic tracked run on the embedded seed,
    translated rules, and legacy strategy. *)
Definition rw_legacy_run_link_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_legacy_run_link_statement (@RewriteAuditProofPlainPublic.rw_tracked_run)
    (@AnalysesAuditRewriteFacadePlainRun.rw_legacy_tracked_builder Hwf).

(** When the operator adapter agrees and guard program laws hold, a selected facade
    run returns the legacy selected explanation. *)
Definition rw_facade_selected_realizes_fixed_type (Hmat :
    rw_facade_plain_materialize_well_founded_type) : Prop :=
  @rw_facade_selected_realizes_statement
    (@AnalysesAuditRewriteFacadePlainExplain.rw_legacy_selected_explanation_builder Hmat).

(** If extraction from the legacy run returns the embedded output, some selected
    explanation is returned and accepted by the original checker. *)
Definition rw_selected_explanation_accepts_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type)
    (Hmat : rw_facade_plain_materialize_well_founded_type) : Prop :=
  @rw_selected_explanation_accepts_statement
    (@AnalysesAuditRewriteFacadePlainRun.rw_legacy_tracked_builder Hwf)
    (@AnalysesAuditRewriteFacadePlainExplain.rw_legacy_selected_explanation_builder Hmat).

(** When the operator adapter agrees and guard program laws hold, a facade optimizer
    run returns the public tracked optimizer result. *)
Definition rw_facade_optimizer_realizes_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type)
    (Hmat : rw_facade_plain_materialize_well_founded_type) : Prop :=
  @rw_facade_optimizer_realizes_statement
    (@AnalysesAuditRewriteFacadePlainExplain.rw_tracked_optimise_builder Hwf Hmat).

(** The tracked optimizer returns a shared DAG and checked explanation for an extracted
    output whose cost is at most the seed cost. *)
Definition rw_tracked_optimise_selected_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type)
    (Hmat : rw_facade_plain_materialize_well_founded_type) : Prop :=
  @rw_tracked_optimise_selected_statement
    (@AnalysesAuditRewriteFacadePlainRun.rw_legacy_tracked_builder Hwf)
    (@AnalysesAuditRewriteFacadePlainExplain.rw_legacy_selected_explanation_builder Hmat)
    (@AnalysesAuditRewriteFacadePlainExplain.rw_tracked_optimise_builder Hwf Hmat).
