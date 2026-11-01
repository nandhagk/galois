(** * RewriteAuditIndexInterfaceIndexRunZeroContract

    This module states the zero-fuel contract for a public index runner.
    For example, the required result at fuel 0 contains the input graph and two empty event lists.
    Builds on: RewriteAuditIndexReference and
    RewriteRun. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

(** Zero fuel returns the input graph, fuel exhaustion, and no events. *)
Definition rw_index_run_zero_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) rules strategy (g : rw_graph K Sort V),
    rw_index_run EK ES EV EH sig rules strategy 0%N g =
      (RwRunResult g RWFuelExhausted, nil, nil).

End FuturePublicImplementations.
