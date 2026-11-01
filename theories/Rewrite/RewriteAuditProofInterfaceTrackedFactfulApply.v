(** * RewriteAuditProofInterfaceTrackedFactfulApply

    This module defines tracked apply and its fact-invalidating variant for future interfaces.
    For example, at position 0, rejection of rule 0 at root 1 with an empty substitution
    makes both apply operations return None.
    Builds on: RewriteAuditProofSemantic and
    RewriteAuditProofTick. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofSemantic
  RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Variable rw_tracked_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

Definition rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

Definition rw_tracked_factful_apply {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (position : nat)
    (input : rw_tracked_state K Sort V H * Map.t rw_id F) (attempt : rw_attempt K Sort V H) :=
  let '(state, facts) := input in
  match rw_tracked_apply EK ES EV EH sig rules position state attempt with
  | None => None
  | Some (next, events) => Some ((next, rw_facts_invalidate facts), events)
  end.

End FuturePublicImplementations.
