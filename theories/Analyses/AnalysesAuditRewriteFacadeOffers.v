(** * AnalysesAuditRewriteFacadeOffers

    Models construction and selection of legacy facade rule offers and their source work.
    For example, choosing from an empty offer list returns None with work 64.
    Builds on: AnalysesAuditRewriteFacadePrepare and
    RewriteAuditSharedExtract. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeDimensions
  AnalysesAuditRewriteFacadeMaterialize AnalysesAuditRewriteFacadePrepare
  AnalysesAuditRewriteFacadeReference AnalysesAuditRewriteFacadeSourceWork.
From Galois.Rewrite Require Import RewriteAuditIndexMatch RewriteAuditIndexPrepare
  RewriteAuditIndexRebuild RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditQueueReference RewriteAuditSharedExtract RewriteAuditSharedReference.
Import List.ListNotations.

Fixpoint rw_facade_make_bindings_atomic {K} (graph : rw_graph K unit nat) (table : rw_rd_table)
    (store : rw_rd_store K unit nat) (holes : list nat) (assignment : rw_assignment nat) : option
    (Map.t nat (rw_term K unit nat)) * nat :=
  match holes with
  | nil => (Some Map.empty, 64)
  | hole :: rest =>
    let '(tail, tail_work) := rw_facade_make_bindings_atomic graph table store rest assignment in
    match tail with
    | None => (None, 64 + tail_work)
    | Some bindings =>
      let '(found, lookup) := audit_map_get audit_nat_encode hole assignment in
      let prefix := 64 + tail_work + audit_map_source_work audit_nat_events_work lookup in
      let '(term, term_work) :=
        match found with
        | None => (Some (RWVar tt hole), 64)
        | Some root =>
          let '(candidate, query_work) := rw_rd_candidate_get graph table root in
          match candidate with
          | None => (None, 64 + query_work)
          | Some candidate =>
            let '(out, trace) := rw_shared_unfold_atomic
              (RwSharedTree K unit nat (rw_rd_pointer candidate) (rw_rd_nodes store)) in
            (out, 64 + query_work + rw_shared_unfold_trace_cost trace)
          end
        end in
      match term with
      | None => (None, prefix + term_work)
      | Some term =>
        let '(out, insertion) := audit_map_set audit_nat_encode hole term bindings in
        (Some out, prefix + term_work + audit_map_source_work audit_nat_events_work insertion)
      end
    end
  end.

Definition rw_facade_rule_offers_atomic {K} (op : rw_queue_encoder_adapter K) (state :
    rw_index_state K unit nat) (graph : rw_graph K unit nat) (table : rw_rd_table) (store :
    rw_rd_store K unit nat) (entry : nat * rw_facade_prepared_rule K) : list (rw_attempt K unit nat
    nat) * nat :=
  let '(index, prepared) := entry in
  let rule := rw_facade_core_rule prepared in
  rw_ri_match_flat_map (fun root =>
    let '(assignments, matching_work) := rw_ri_match_atomic op rw_facade_unit_adapter
      rw_facade_nat_adapter rw_facade_nat_adapter state root (rw_lhs rule) in
    let '(out, binding_work) := rw_ri_match_flat_map (fun assignment =>
      let '(bindings, work) := rw_facade_make_bindings_atomic graph table store
        (rw_holes rule) assignment in
      ((
        match bindings with
        | None => nil
        | Some bindings => [RwAttempt index root bindings]
        end),
        64 + work)) assignments in
    (out, 64 + matching_work + binding_work)) (rw_roots graph).

Definition rw_facade_offer_gate_atomic {K} (op : rw_queue_encoder_adapter K) (guard :
    rw_facade_guard_adapter K) (prepared : rw_facade_prepared K) (attempt : rw_attempt K unit nat
    nat) : bool * nat :=
  let '(found, lookup) := audit_map_get audit_nat_encode (rw_attempt_rule attempt)
    (rw_facade_rule_table prepared) in
  let prefix := 64 + audit_map_source_work audit_nat_events_work lookup in
  match found with
  | None => (false, prefix)
  | Some entry =>
    let '(gate, gate_work) := rw_rp_rule_body_gate_atomic rw_facade_unit_adapter
      rw_facade_nat_adapter
      (rw_facade_local_callbacks guard entry) (rw_facade_core_rule entry) attempt in
    match gate with
    | None => (false, prefix + gate_work)
    | Some (lhs, rhs) =>
      let '(left_legacy, lw) := rw_facade_materialize_project_atomic lhs in
      let '(right_legacy, rw) := rw_facade_materialize_project_atomic rhs in
      let '(bindings, bw) := rw_facade_bindings_atomic (rw_attempt_sub attempt) in
      let '(replayed, trace) := rw_facade_step_atomic (rw_external_encoding_events op) guard
        (rw_facade_original_table prepared) left_legacy
        (RewriteStep nil (rw_attempt_rule attempt) true bindings) in
      let prefix := prefix + gate_work + lw + rw + bw + rw_facade_step_source_work trace in
      match replayed with
      | None => (false, prefix)
      | Some actual =>
        let '(same, comparison) := rw_facade_eq_atomic (rw_external_encoding_events op) actual
          right_legacy in
        (same, prefix + rw_facade_eq_source_work comparison)
      end
    end
  end.

Fixpoint rw_facade_choose_atomic {K} (op : rw_queue_encoder_adapter K) (guard :
    rw_facade_guard_adapter K) (prepared : rw_facade_prepared K) (offers : list (rw_attempt K unit
    nat nat)) : option (rw_attempt K unit nat nat) * nat :=
  match offers with
  | nil => (None, 64)
  | attempt :: rest =>
    let '(accepted, gate_work) := rw_facade_offer_gate_atomic op guard prepared attempt in
    if accepted then (Some attempt, 64 + gate_work)
    else
      let '(out, tail_work) := rw_facade_choose_atomic op guard prepared rest in
      (out, 64 + gate_work + tail_work)
  end.

(** A facade strategy run relates an index state to its selected offer, source work,
    and operand dimension, including the empty-root case. *)
Inductive rw_facade_strategy_run {K} (op : rw_queue_encoder_adapter K)
    (guard : rw_facade_guard_adapter K) (prepared : rw_facade_prepared K)
    (state : rw_index_state K unit nat) : option (rw_attempt K unit nat nat) -> nat -> nat ->
    Prop :=
  | RPFStrategyEmpty : forall graph graph_work fresh prepare_trace length_trace,
      rw_ri_graph_atomic state = (graph, graph_work) ->
      rw_ri_prepare_once op rw_facade_nat_adapter graph = (fresh, prepare_trace) ->
      rw_fuel_length (rw_roots graph) = (0, length_trace) ->
      rw_facade_strategy_run op guard prepared state None
        (64 + graph_work + rw_ri_prepare_once_work prepare_trace + audit_work length_trace)
        (S (rw_facade_prepared_dimension prepared + rw_facade_index_dimension state +
          rw_facade_graph_dimension graph + rw_facade_index_dimension fresh))
  | RPFStrategyReady : forall graph graph_work fresh prepare_trace count length_trace fuel
      fuel_trace
      entries enumeration table store dp_work offers offers_work chosen choice_work,
      rw_ri_graph_atomic state = (graph, graph_work) ->
      rw_ri_prepare_once op rw_facade_nat_adapter graph = (fresh, prepare_trace) ->
      rw_fuel_length (rw_roots graph) = (S count, length_trace) ->
      rw_fuel_to_positive count = (fuel, fuel_trace) ->
      audit_map_elements (rw_nodes graph) = (entries, enumeration) ->
      rw_rd_rounds_run op rw_facade_unit_adapter rw_facade_nat_adapter
        (fun _ => (0, 64)) (fun _ => (0, 64)) graph entries fuel Map.empty
        (RwRdStore Map.empty 1%positive) table store dp_work ->
      rw_ri_match_flat_map (rw_facade_rule_offers_atomic op fresh graph table store)
        (rw_facade_rule_entries prepared) = (offers, offers_work) ->
      rw_facade_choose_atomic op guard prepared offers = (chosen, choice_work) ->
      rw_facade_strategy_run op guard prepared state chosen
        (64 + graph_work + rw_ri_prepare_once_work prepare_trace + audit_work length_trace +
          audit_work fuel_trace + audit_elements_work enumeration + dp_work +
          offers_work + choice_work)
        (rw_facade_strategy_dimension prepared state graph fresh table store offers).
