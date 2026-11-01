(** * RewriteAuditProofInterfaceFactfulRunZeroContract

    States a prospective zero-fuel contract for factful tracked runs.
    For example, at zero fuel the contract requires the input fact map to be retained.
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

(** Zero fuel returns the tracked state and facts unchanged with no events. *)
Definition rw_factful_run_zero_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (an : rw_analysis K Sort V C F)
    strategy (state : rw_tracked_state K Sort V H) facts,
    rw_factful_run EK ES EV EH sig rules an strategy 0%N (state, facts) =
      (RwTrackedOutput state RWFuelExhausted nil nil, facts).

End FuturePublicImplementations.
