(** * RewriteAuditIndexPrograms

    This module defines view-query programs and their plain and audited interpreters.
    For example, a return program containing 1 evaluates to 1 without a view query.
    Builds on: RewriteAuditIndexFind and
    RewriteAuditIndexRebuild. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexFind RewriteAuditIndexRebuild
  RewriteAuditIndexReference RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_rp_query (K Sort V : Type) : Type :=
  | RPQueryFind : rw_id -> option rw_id -> rw_rp_query K Sort V
  | RPQuerySort : rw_id -> option Sort -> rw_rp_query K Sort V
  | RPQueryNode : rw_id -> option (rw_id * rw_node K Sort V) -> rw_rp_query K Sort V
  | RPQueryOperator : K -> list rw_id -> rw_rp_query K Sort V
  | RPQueryVariable : V -> list rw_id -> rw_rp_query K Sort V
  | RPQueryParents : rw_id -> list rw_id -> rw_rp_query K Sort V
  | RPQueryRoots : list rw_id -> rw_rp_query K Sort V
  | RPQueryNodes : list rw_id -> rw_rp_query K Sort V
  | RPQueryGraph : rw_graph K Sort V -> rw_rp_query K Sort V.
Arguments RPQueryFind {K Sort V}.
Arguments RPQuerySort {K Sort V}.
Arguments RPQueryNode {K Sort V}.
Arguments RPQueryOperator {K Sort V}.
Arguments RPQueryVariable {K Sort V}.
Arguments RPQueryParents {K Sort V}.
Arguments RPQueryRoots {K Sort V}.
Arguments RPQueryNodes {K Sort V}.
Arguments RPQueryGraph {K Sort V}.

Inductive rw_rp_view_request (K Sort V : Type) : Type -> Type :=
  | RPRequestFind : rw_id -> rw_rp_view_request K Sort V (option rw_id)
  | RPRequestSort : rw_id -> rw_rp_view_request K Sort V (option Sort)
  | RPRequestNode : rw_id -> rw_rp_view_request K Sort V (option (rw_id * rw_node K Sort V))
  | RPRequestOperator : K -> rw_rp_view_request K Sort V (list rw_id)
  | RPRequestVariable : V -> rw_rp_view_request K Sort V (list rw_id)
  | RPRequestParents : rw_id -> rw_rp_view_request K Sort V (list rw_id)
  | RPRequestRoots : rw_rp_view_request K Sort V (list rw_id)
  | RPRequestNodes : rw_rp_view_request K Sort V (list rw_id)
  | RPRequestGraph : rw_rp_view_request K Sort V (rw_graph K Sort V).
Arguments RPRequestFind {K Sort V}.
Arguments RPRequestSort {K Sort V}.
Arguments RPRequestNode {K Sort V}.
Arguments RPRequestOperator {K Sort V}.
Arguments RPRequestVariable {K Sort V}.
Arguments RPRequestParents {K Sort V}.
Arguments RPRequestRoots {K Sort V}.
Arguments RPRequestNodes {K Sort V}.
Arguments RPRequestGraph {K Sort V}.

Inductive rw_rp_view_program (K Sort V A : Type) : Type :=
  | RPViewReturn : A -> nat -> rw_rp_view_program K Sort V A
  | RPViewAsk : forall R, nat -> rw_rp_view_request K Sort V R ->
      (R -> rw_rp_view_program K Sort V A) -> rw_rp_view_program K Sort V A.
Arguments RPViewReturn {K Sort V A}.
Arguments RPViewAsk {K Sort V A R}.

Inductive rw_rp_provider_trace (K Sort V : Type) : Type :=
  | RPProviderFind : audit_trace rw_ri_find_call -> rw_rp_provider_trace K Sort V
  | RPProviderPositive : forall A,
      list (audit_map_event rw_id A (audit_basic_encoding_event positive)) ->
      rw_rp_provider_trace K Sort V
  | RPProviderOperator : list (audit_map_event K (FinSet.t rw_id) nat) ->
      rw_rp_provider_trace K Sort V
  | RPProviderVariable : list (audit_map_event V (FinSet.t rw_id) nat) ->
      rw_rp_provider_trace K Sort V
  | RPProviderElements : FinSet.t rw_id -> list rw_id -> list (audit_set_elements_event rw_id) ->
      rw_rp_provider_trace K Sort V
  | RPProviderGraph : rw_index_state K Sort V -> rw_graph K Sort V -> nat ->
      rw_rp_provider_trace K Sort V.
Arguments RPProviderFind {K Sort V}.
Arguments RPProviderPositive {K Sort V A}.
Arguments RPProviderOperator {K Sort V}.
Arguments RPProviderVariable {K Sort V}.
Arguments RPProviderElements {K Sort V}.
Arguments RPProviderGraph {K Sort V}.

Definition rw_rp_provider_trace_work {K Sort V} (trace : rw_rp_provider_trace K Sort V) : nat :=
  match trace with
  | RPProviderFind events => rw_ri_find_trace_cost events
  | RPProviderPositive events => audit_map_source_work audit_basic_encoding_work events
  | RPProviderOperator events => audit_map_source_work rw_external_events_work events
  | RPProviderVariable events => audit_map_source_work rw_external_events_work events
  | RPProviderElements _ _ events => audit_set_elements_work events
  | RPProviderGraph _ _ work => work
  end.

Record rw_rp_query_receipt (K Sort V : Type) := RwRpQueryReceipt {
  rw_rp_query_observation : rw_rp_query K Sort V;
  rw_rp_query_sources : list (rw_rp_provider_trace K Sort V)
}.
Arguments RwRpQueryReceipt {K Sort V}.
Arguments rw_rp_query_observation {K Sort V}.
Arguments rw_rp_query_sources {K Sort V}.

Definition rw_rp_query_receipt_work {K Sort V} (receipt : rw_rp_query_receipt K Sort V) : nat :=
  fold_right (fun trace total => rw_rp_provider_trace_work trace + total) 64
    (rw_rp_query_sources receipt).

Definition rw_rp_view_plain_request {K Sort V R} (view : rw_snapshot_view K Sort V)
    (request : rw_rp_view_request K Sort V R) : R :=
  let base := rw_snapshot_base view in
  match request with
  | RPRequestFind id => rw_view_find base id
  | RPRequestSort id => rw_view_sort base id
  | RPRequestNode id => rw_view_node base id
  | RPRequestOperator key => rw_view_operator_nodes base key
  | RPRequestVariable key => rw_view_variable_nodes base key
  | RPRequestParents id => rw_view_parent_nodes base id
  | RPRequestRoots => rw_view_roots base tt
  | RPRequestNodes => rw_view_nodes base tt
  | RPRequestGraph => rw_snapshot_graph view tt
  end.

Fixpoint rw_rp_view_plain {K Sort V A} (view : rw_snapshot_view K Sort V)
    (program : rw_rp_view_program K Sort V A) : A :=
  match program with
  | RPViewReturn answer _ => answer
  | RPViewAsk _ request next =>
    rw_rp_view_plain view (next (rw_rp_view_plain_request view request))
  end.

Definition rw_rp_view_execute_request {K Sort V R} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (state : rw_index_state K Sort V)
    (request : rw_rp_view_request K Sort V R) : R * rw_rp_query_receipt K Sort V :=
  match request with
  | RPRequestFind id =>
    let '(answer, trace) := rw_ri_find_atomic state id in
    (answer, RwRpQueryReceipt (RPQueryFind id answer) [RPProviderFind trace])
  | RPRequestSort id =>
    let '(answer, trace) := audit_map_get audit_positive_encode id
      (rw_sorts (rw_index_base state)) in
    (answer, RwRpQueryReceipt (RPQuerySort id answer) [RPProviderPositive trace])
  | RPRequestNode id =>
    let '(answer, trace) := audit_map_get audit_positive_encode id
      (rw_nodes (rw_index_base state)) in
    (answer, RwRpQueryReceipt (RPQueryNode id answer) [RPProviderPositive trace])
  | RPRequestOperator key =>
    let '(found, trace) := audit_map_get (rw_external_encoding_events op) key
      (rw_index_operators state) in
    let bucket :=
      match found with
      | Some stored => stored
      | None => FinSet.empty
      end in
    let '(answer, elements) := audit_finset_elements bucket in
    (answer, RwRpQueryReceipt (RPQueryOperator key answer)
      [RPProviderOperator trace; RPProviderElements bucket answer elements])
  | RPRequestVariable key =>
    let '(found, trace) := audit_map_get (rw_external_encoding_events value) key
      (rw_index_variables state) in
    let bucket :=
      match found with
      | Some stored => stored
      | None => FinSet.empty
      end in
    let '(answer, elements) := audit_finset_elements bucket in
    (answer, RwRpQueryReceipt (RPQueryVariable key answer)
      [RPProviderVariable trace; RPProviderElements bucket answer elements])
  | RPRequestParents id =>
    let '(found, trace) := rw_ri_find_atomic state id in
    match found with
    | None => (nil, RwRpQueryReceipt (RPQueryParents id nil) [RPProviderFind trace])
    | Some root =>
      let '(stored, lookup) := audit_map_get audit_positive_encode root
        (rw_index_parent_buckets state) in
      let bucket :=
        match stored with
        | Some stored => stored
        | None => FinSet.empty
        end in
      let '(answer, elements) := audit_finset_elements bucket in
      (answer, RwRpQueryReceipt (RPQueryParents id answer)
        [RPProviderFind trace; RPProviderPositive lookup;
          RPProviderElements bucket answer elements])
    end
  | RPRequestRoots =>
    let '(graph, work) := rw_ri_graph_atomic state in
    (rw_roots graph, RwRpQueryReceipt (RPQueryRoots (rw_roots graph))
      [RPProviderGraph state graph work])
  | RPRequestNodes =>
    let answer := rw_nodes_in (rw_index_base state) in
    (answer, RwRpQueryReceipt (RPQueryNodes answer) nil)
  | RPRequestGraph =>
    let '(graph, work) := rw_ri_graph_atomic state in
    (graph, RwRpQueryReceipt (RPQueryGraph graph) [RPProviderGraph state graph work])
  end.

Fixpoint rw_rp_view_execute {K Sort V A} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (state : rw_index_state K Sort V)
    (program : rw_rp_view_program K Sort V A) : A * nat * list (rw_rp_query_receipt K Sort V) :=
  match program with
  | RPViewReturn answer body => (answer, 64 + body, nil)
  | RPViewAsk body request next =>
    let '(answer, receipt) := rw_rp_view_execute_request op value state request in
    let '(out, later_work, later) := rw_rp_view_execute op value state (next answer) in
    (out, 64 + body + rw_rp_query_receipt_work receipt + later_work, receipt :: later)
  end.

Record rw_rp_strategy_adapter (K Sort V H : Type) := RwRpStrategyAdapter {
  rw_rp_strategy_program : rw_rp_view_program K Sort V (option (rw_attempt K Sort V H))
}.
Arguments rw_rp_strategy_program {K Sort V H}.

Definition rw_rp_strategy_run {K Sort V H} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (adapter : rw_rp_strategy_adapter K Sort V H)
    (state : rw_index_state K Sort V) :=
  rw_rp_view_execute op value state (rw_rp_strategy_program adapter).
