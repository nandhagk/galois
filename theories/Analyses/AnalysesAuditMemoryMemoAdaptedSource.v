(** * Adapted family source bounds

    These obligations bind every genuine foreign callback to its actual input, result and body.
    For example, internally prepared predecessor lookups never receive a foreign source-price law.
    Builds on: the family's complete source model and the shared actual-call adapter. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditCallback.
From Galois.Analyses Require Import AnalysesAuditMemoryState AnalysesAuditMemoryEncoding.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Analyses Require Import AnalysesAuditMemoryInputBudget AnalysesAuditMemoryRawNext
  AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoWhole
  AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteBound
  AnalysesAuditMemoryMemoSnapshot AnalysesAuditMemoryTable AnalysesAuditMemorySharedBudget
  AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemoryMemoPublicSource
  AnalysesAuditMemoryMemoSnapshotSource.
Import List.ListNotations.

(** Callback adapter laws yield a recurrence witness at the query endpoints and bound its source
    work. *)
Definition audit_memory_memo_public_whole_input_bound_adapted_statement : Prop :=
  forall N E T CN CE SE OE BE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
      (state : memo_state EN g effects mg)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work operand_work before_work
      node_budget edge_budget site_budget operand_budget before_budget scope start fuel
        node_enc_source edge_enc_source site_enc_source operand_source before_source,
    audit_external_callback_adapter node_enc node_work node_enc_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_enc_source edge_budget ->
    audit_external_callback_adapter site_enc site_work site_enc_source site_budget ->
    audit_external_callback_adapter
      (fun args => operand (fst args) (snd args)) operand_work operand_source
      (fun args => operand_budget (fst args) (snd args)) ->
    audit_external_callback_adapter
      (fun args => before (fst args) (snd args)) before_work before_source
      (fun args => before_budget (fst args) (snd args)) ->
    let incoming := audit_walk_predecessors node_enc
      (in_index (@memo_adjacency N E T EN g effects mg state)) in
    let '(encoded_scope, run) := audit_memory_memo_public_source_counted node_enc edge_enc
      site_enc EN
      g effects mg state operand before scope start fuel in
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let key_enc := audit_memory_memo_key_encode node_enc edge_enc in
    let next := audit_memory_raw_next edge_enc site_enc
      (@memo_effect_index N E T EN g effects mg state) incoming operand before scope in
    exists budget,
      audit_memo_input_budget_run version_enc key_enc (fst encoded_scope) next
        (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget)
        (audit_memory_memo_key_input_budget node_enc edge_enc node_budget edge_budget)
        (@audit_raw_next_input_budget N E T CE SE (audit_map_event N (list E) CN) OE BE
          edge_enc site_enc (@memo_effect_index N E T EN g effects mg state) incoming before
          edge_budget site_budget (audit_walk_predecessor_input_budget node_enc node_budget)
          operand_budget before_budget scope)
        FinSet.empty (@memo_entries N E T EN g effects mg state) start (Npos fuel)
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run) budget /\
      4 + audit_memory_scope_work site_work (snd encoded_scope) +
        audit_memo_execution_source_work (audit_memory_version_work node_work edge_work)
          (audit_memory_memo_key_work node_work edge_work)
          (audit_raw_next_source_work edge_work site_work (audit_map_source_work node_work)
            operand_work before_work) run <=
      4 + audit_memory_scope_input_budget site_enc site_budget scope +
        16 * S (Pos.size_nat fuel) * budget.

(** Matching node, outgoing and target callbacks and adapter laws bound memo initialization,
    including graph preparation and effect indexing. *)
Definition audit_memory_memo_initial_whole_input_bound_adapted_statement : Prop :=
  forall N E T CN CE OE TE FE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (effects : E -> list (memory_effect T) * list FE)
      node_work edge_work out_work target_work effect_work
      node_budget edge_budget out_budget target_budget effect_budget (g : Graph.t N E)
      (mg : memory_graph N E) node_enc_source edge_enc_source out_source target_source
        effects_source,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    audit_external_callback_adapter node_enc node_work node_enc_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_enc_source edge_budget ->
    audit_external_callback_adapter out out_work out_source out_budget ->
    audit_external_callback_adapter target target_work target_source target_budget ->
    audit_external_callback_adapter effects effect_work effects_source effect_budget ->
    let '(_, (preparation, rows)) := audit_memory_memo_initial_source_counted EN node_enc edge_enc
      out target effects g mg in
    4 + audit_prepare_source_work (audit_snapshot_graph_body_work node_work out_work target_work)
      preparation + audit_memory_table_work edge_work out_work effect_work rows <=
    4 + audit_prepare_source_budget EN g + audit_graph_prepare_full_event_bound g *
      audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
        (Graph.nodes g) +
    audit_memory_table_input_budget edge_enc out effects edge_budget out_budget effect_budget
      (Graph.nodes g).

(** Callback adapter laws yield a recurrence witness at the saved query endpoints and bound its
    source work. *)
Definition audit_snapshot_query_whole_input_bound_adapted_statement : Prop :=
  forall N E T Epoch CN CE SE OE BE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (cache : audit_snapshot_memo_cache N E T Epoch EN)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work operand_work before_work
      node_budget edge_budget site_budget operand_budget before_budget scope start fuel
        node_enc_source edge_enc_source site_enc_source operand_source before_source,
    audit_external_callback_adapter node_enc node_work node_enc_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_enc_source edge_budget ->
    audit_external_callback_adapter site_enc site_work site_enc_source site_budget ->
    audit_external_callback_adapter
      (fun args => operand (fst args) (snd args)) operand_work operand_source
      (fun args => operand_budget (fst args) (snd args)) ->
    audit_external_callback_adapter
      (fun args => before (fst args) (snd args)) before_work before_source
      (fun args => before_budget (fst args) (snd args)) ->
    let incoming := audit_walk_predecessors node_enc (in_index (audit_cache_prepared cache)) in
    let '(encoded_scope, run) := audit_snapshot_query_source_counted EN node_enc edge_enc site_enc
      cache operand before scope start fuel in
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let key_enc := audit_memory_memo_key_encode node_enc edge_enc in
    let next := audit_memory_raw_next edge_enc site_enc (audit_cache_effect_index cache)
      incoming operand before scope in
    exists budget,
      audit_memo_input_budget_run version_enc key_enc (fst encoded_scope) next
        (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget)
        (audit_memory_memo_key_input_budget node_enc edge_enc node_budget edge_budget)
        (@audit_raw_next_input_budget N E T CE SE (audit_map_event N (list E) CN) OE BE
          edge_enc site_enc (audit_cache_effect_index cache) incoming before edge_budget site_budget
          (audit_walk_predecessor_input_budget node_enc node_budget) operand_budget
            before_budget scope)
        FinSet.empty (audit_cache_entries cache) start (Npos fuel)
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run) budget /\
      8 + audit_memory_scope_work site_work (snd encoded_scope) +
        audit_memo_execution_source_work (audit_memory_version_work node_work edge_work)
          (audit_memory_memo_key_work node_work edge_work)
          (audit_raw_next_source_work edge_work site_work (audit_map_source_work node_work)
            operand_work before_work) run <=
      8 + audit_memory_scope_input_budget site_enc site_budget scope +
        16 * S (Pos.size_nat fuel) * budget.

(** Matching node, outgoing and target callbacks and adapter laws bound refresh on both epoch
    hit and miss. *)
Definition audit_snapshot_refresh_whole_input_bound_adapted_statement : Prop :=
  forall N E T Epoch CE CN OE FE TE (EN : encoding N)
      (epoch_enc : Epoch -> positive * list CE) (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      epoch_work node_work edge_work out_work effect_work target_work
      epoch_budget node_budget edge_budget out_budget effect_budget target_budget old current
        epoch_enc_source node_enc_source edge_enc_source out_source effects_source target_source,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out (snapshot_graph current) n) ->
    (forall e, fst (target e) = Graph.target (snapshot_graph current) e) ->
    audit_external_callback_adapter epoch_enc epoch_work epoch_enc_source epoch_budget ->
    audit_external_callback_adapter node_enc node_work node_enc_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_enc_source edge_budget ->
    audit_external_callback_adapter out out_work out_source out_budget ->
    audit_external_callback_adapter effects effect_work effects_source effect_budget ->
    audit_external_callback_adapter target target_work target_source target_budget ->
    audit_snapshot_refresh_full_source_work epoch_work node_work edge_work out_work effect_work
      target_work (snd (audit_snapshot_refresh_source EN epoch_enc node_enc edge_enc out target
        effects old current)) <=
    audit_snapshot_refresh_input_budget EN epoch_enc node_enc edge_enc out target effects
      epoch_budget node_budget out_budget edge_budget effect_budget target_budget old current.
