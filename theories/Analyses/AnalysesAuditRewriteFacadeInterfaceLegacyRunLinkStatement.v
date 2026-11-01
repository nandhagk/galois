(** * AnalysesAuditRewriteFacadeInterfaceLegacyRunLinkStatement

    This module states the link between legacy tracked results and a generic tracked run.
    For example, with seed variable 0 and positive fuel 1, the proposed link equates the
    legacy root and core with the generic run at binary fuel 1 on the embedded variable.
    Builds on: AnalysesAuditRewriteFacadeReference2 and
    AnalysesAuditRewriteFacadeRun. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeReference2
  AnalysesAuditRewriteFacadeRun.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRun.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},
    encoding K -> encoding Sort -> encoding V -> encoding H ->
    rw_signature K Sort V -> list (rw_rule K Sort V H) ->
    (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->
    N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

Variable rw_legacy_tracked : forall K, encoding K -> list (rewrite_rule K) -> positive ->
  term K -> rw_legacy_tracked_state K.

(** The legacy root and core equal the generic tracked run on the embedded seed,
    translated rules, and legacy strategy. *)
Definition rw_legacy_run_link_statement : Prop :=
  forall K (EK : encoding K) rules fuel seed,
    let legacy := rw_legacy_tracked K EK rules fuel seed in
    (rw_legacy_root K legacy, rw_legacy_core K legacy) =
      rw_tracked_run EK unit_encoding nat_encoding nat_encoding legacy_signature
        (map legacy_rule rules) (rw_legacy_strategy EK rules (legacy_list_table rules 0))
        (Npos fuel) (legacy_embed seed).

End FuturePublicImplementations.
