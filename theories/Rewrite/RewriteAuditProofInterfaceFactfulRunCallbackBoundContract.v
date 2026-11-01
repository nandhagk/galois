(** * RewriteAuditProofInterfaceFactfulRunCallbackBoundContract

    This module states the fuel bound for events and stopping in a factful run.
    For example, at fuel 1 an exhausted run may have at most one event under the contract.
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

(** The factful run event count plus one when stopped is bounded by its fuel. *)
Definition rw_factful_run_callback_bound_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (an : rw_analysis K Sort V C F) strategy fuel (state : rw_tracked_state K Sort V H) facts,
    let '(result, _) := rw_factful_run EK ES EV EH sig rules an strategy fuel (state, facts) in
    (N.of_nat (length (rw_tracked_events result)) +
      match rw_tracked_stop result with
      | RWStopped => 1
      | RWFuelExhausted => 0
      end <= fuel)%N.

End FuturePublicImplementations.
