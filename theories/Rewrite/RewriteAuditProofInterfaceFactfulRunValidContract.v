(** * RewriteAuditProofInterfaceFactfulRunValidContract

    This module states preservation of fact-store validity across a factful run.
    For example, at fuel 0, valid input facts require the arbitrary runner's retained output
    store to be valid in its returned graph.
    Builds on: RewriteAuditProofRun and
    RewriteAuditProofSemantic. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofPlainPublic RewriteAuditProofRun
  RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_factful_run : forall {K Sort V H C F},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> rw_analysis K Sort V C F ->
  (rw_fact_view K Sort V F -> option (rw_attempt K Sort V H)) -> N ->
  rw_tracked_state K Sort V H * Map.t rw_id F ->
  rw_tracked_output K Sort V H * Map.t rw_id F.

(** A factful run preserves fact-store validity when the input store is valid. *)
Definition rw_factful_run_valid_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    strategy fuel state facts result retained,
    rw_fact_store_valid admissible an (rw_tracked_graph state) facts ->
    rw_factful_run EK ES EV EH sig rules an strategy fuel (state, facts) = (result, retained) ->
    rw_fact_store_valid admissible an (rw_tracked_graph (rw_tracked_final result)) retained.

End FuturePublicImplementations.
