(** * RewriteAuditIndexInterfaceIndexRunCallbackBoundContract

    States a prospective bound on index-run events and stopping against fuel.
    For example, a stopped run with no events is required to consume at least one unit of fuel.
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

(** The event count plus one for a stopped run is at most the supplied fuel. *)
Definition rw_index_run_callback_bound_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) rules strategy fuel (g : rw_graph K Sort V),
    let '(result, _, events) := rw_index_run EK ES EV EH sig rules strategy fuel g in
    (N.of_nat (length events) +
      match rw_run_stop result with
      | RWStopped => 1%N
      | RWFuelExhausted => 0%N
      end <= fuel)%N.

End FuturePublicImplementations.
