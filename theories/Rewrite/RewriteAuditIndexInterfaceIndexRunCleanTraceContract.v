(** * RewriteAuditIndexInterfaceIndexRunCleanTraceContract

    States a prospective clean-trace property for positive-fuel index runs.
    For example, with positive fuel, a sound, productive, well-formed input, and sound, well-formed
    rules, a stopped run must have no next attempt.
    Builds on: RewriteAuditIndexPublic and
    RewriteAuditIndexTickReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic
  RewriteAuditIndexPrepareReference RewriteAuditIndexPublic RewriteAuditIndexReference
  RewriteAuditIndexTickReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).

Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

Let rw_index_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :=
  match rw_index_rule_step EK ES EV EH sig rules state attempt with
  | None => None
  | Some intermediate => Some (rw_index_rebuild EK ES EV intermediate)
  end.

(** For sound, well-formed rules and a well-formed, sound, productive input graph, positive
    fuel yields a clean trace from the initial rebuild; stopping leaves no next attempt. *)
Definition rw_index_run_clean_trace_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) strategy fuel (input : rw_graph K Sort V)
    result initial_events events,
    Forall (rw_rule_wf sig) rules ->
    Forall (rw_rule_sound sig admissible) rules ->
    rw_graph_wf sig input ->
    rw_graph_sound sig admissible rules input ->
    rw_productive input ->
    rw_index_run EK ES EV EH sig rules strategy (Npos fuel) input =
      (result, initial_events, events) ->
    exists initial final,
      rw_index_rebuild EK ES EV (rw_index_build EK ES EV input) = (initial, initial_events) /\
      rw_index_clean_trace rw_index_graph (rw_index_view EK ES EV)
        (rw_index_apply EK ES EV EH sig rules) strategy initial (rev events) final /\
      rw_run_graph result = rw_index_graph final /\
      (rw_run_stop result = RWStopped -> strategy (rw_index_view EK ES EV final) = None).

End FuturePublicImplementations.
