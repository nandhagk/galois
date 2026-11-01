(** * Complete prepared clobber adjacency

    This model builds every version row before the binary search begins.
    For example, an unvisited phi still pays its complete operand materialization.
    Builds on: full graph preparation, concrete memory encoders and indexed search. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditElements.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryRawNext AnalysesAuditMemoryIndex AnalysesAuditMemoryTable
  AnalysesAuditMemorySharedBudget AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemorySearch
  AnalysesAuditMemorySearchInputBudget AnalysesAuditMemoryDistinct.
Import List.ListNotations.

Definition audit_walk_predecessors {N E CN} (node_enc : N -> positive * list CN)
    (incoming : Map.t N (list E)) (node : N) :=
  let '(found, calls) := audit_map_get node_enc node incoming in
  (
    match found with
    | Some edges => edges
    | None => []
    end, calls).

Definition audit_walk_successors {N E CN CE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (index : Map.t (memory_version N E) (list (memory_version N E)))
    (version : memory_version N E) :=
  let '(found, calls) := audit_map_get (audit_memory_version_encode node_enc edge_enc)
    version index in
  (
    match found with
    | Some versions => versions
    | None => []
    end, calls).

(** A walk raw event can record predecessor reads as counted node-map lookups. *)
Definition audit_walk_raw_event (N E T CN CE SE PE BE : Type) : Type :=
  audit_raw_next_event N E T CE SE (audit_map_event N (list E) CN) PE BE.

(** A walk index event can record version-key indexing and its raw successor events. *)
Definition audit_walk_index_event (N E T CN CE SE PE BE : Type) : Type :=
  audit_memory_index_event (memory_version N E) (list (memory_version N E))
    (audit_memory_version_event N E CN CE) (audit_walk_raw_event N E T CN CE SE PE BE).

Record audit_walk_index_run (N E T CN CE SE OE TE FE PE BE : Type) : Type :=
  AuditWalkIndexRun {
    audit_walk_index_value : Map.t (memory_version N E) (list (memory_version N E));
    audit_walk_index_table : list (audit_memory_table_event N E T CE OE FE);
    audit_walk_index_prepare :
      list (audit_prepare_source_event N E (audit_snapshot_graph_body CN OE TE));
    audit_walk_index_rows : list (audit_walk_index_event N E T CN CE SE PE BE)
  }.
Arguments AuditWalkIndexRun {N E T CN CE SE OE TE FE PE BE} _ _ _ _.
Arguments audit_walk_index_value {N E T CN CE SE OE TE FE PE BE} _.
Arguments audit_walk_index_table {N E T CN CE SE OE TE FE PE BE} _.
Arguments audit_walk_index_prepare {N E T CN CE SE OE TE FE PE BE} _.
Arguments audit_walk_index_rows {N E T CN CE SE OE TE FE PE BE} _.

Definition audit_memory_walk_index_counted {N E T CN CE SE OE TE FE PE BE}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (operand : N -> option E -> option (memory_version N E) * list PE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (g : Graph.t N E) (mg : memory_graph N E) (scope : memory_scope T) :=
  let '(table, table_events) := audit_memory_effect_table edge_enc out effects (Graph.nodes g) in
  let '(base, prepare_events) := audit_prepare_source_counted EN g
    (audit_snapshot_graph_callbacks node_enc out target) in
  let '(index, index_events) := audit_memory_result_index
    (audit_memory_version_encode node_enc edge_enc)
    (audit_memory_raw_next edge_enc site_enc table
      (audit_walk_predecessors node_enc (in_index base)) operand before scope)
    (memory_versions mg) in
  AuditWalkIndexRun index table_events prepare_events index_events.

Definition audit_memory_walk_index_source_work {N E T CN CE SE OE TE FE PE BE}
    (node_work : list CN -> nat) (edge_work : list CE -> nat) (site_work : list SE -> nat)
    (out_work : list OE -> nat) (target_work : list TE -> nat) (effect_work : list FE -> nat)
    (operand_work : list PE -> nat) (before_work : list BE -> nat)
    (run : audit_walk_index_run N E T CN CE SE OE TE FE PE BE) : nat :=
  4 + audit_memory_table_work edge_work out_work effect_work (audit_walk_index_table run) +
  audit_prepare_source_work (audit_snapshot_graph_body_work node_work out_work target_work)
    (audit_walk_index_prepare run) +
  audit_memory_index_work (audit_memory_version_work node_work edge_work)
    (audit_raw_next_source_work edge_work site_work (audit_map_source_work node_work)
      operand_work before_work) (audit_walk_index_rows run).

Definition audit_walk_predecessor_input_budget {N CN}
    (node_enc : N -> positive * list CN) (node_budget : N -> nat) (node : N) : nat :=
  5 + node_budget node + 5 * Pos.size_nat (fst (node_enc node)).

Definition audit_memory_walk_index_input_budget {N E T CN CE SE OE TE FE PE BE}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (operand : N -> option E -> option (memory_version N E) * list PE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (node_budget out_budget : N -> nat) (edge_budget effect_budget target_budget : E -> nat)
    (site_budget : T -> nat) (operand_budget : N -> option E -> nat)
    (before_budget : E -> nat -> nat) (g : Graph.t N E) (mg : memory_graph N E) scope : nat :=
  let table := fst (audit_memory_effect_table edge_enc out effects (Graph.nodes g)) in
  let base := fst (audit_prepare_source_counted EN g
    (audit_snapshot_graph_callbacks node_enc out target)) in
  4 + audit_memory_table_input_budget edge_enc out effects edge_budget out_budget effect_budget
    (Graph.nodes g) + audit_prepare_source_budget EN g +
  audit_graph_prepare_full_event_bound g *
    audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
      (Graph.nodes g) +
  audit_memory_index_input_budget (audit_memory_version_encode node_enc edge_enc)
    (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget)
    (@audit_raw_next_input_budget N E T CE SE (audit_map_event N (list E) CN) PE BE
      edge_enc site_enc table
      (audit_walk_predecessors node_enc (in_index base)) before edge_budget site_budget
      (audit_walk_predecessor_input_budget node_enc node_budget) operand_budget before_budget scope)
    (memory_versions mg).

(** Matching encoders and graph, effect and memory callbacks recover the original complete
    memory adjacency index. *)
Definition audit_memory_walk_index_erases_statement : Prop :=
  forall N E T CN CE SE OE TE FE PE BE (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      (g : Graph.t N E) (original : E -> list (memory_effect T)) (mg : memory_graph N E) scope,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall e, fst (effects e) = original e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    audit_walk_index_value (audit_memory_walk_index_counted EN node_enc edge_enc site_enc out
      target effects operand before g mg scope) = memory_walk_index EN EE ET g original mg scope.

(** Matching node, outgoing and target callbacks and callback budgets bound preparation and
    every materialized memory-version adjacency row. *)
Definition audit_memory_walk_index_whole_input_bound_statement : Prop :=
  forall N E T CN CE SE OE TE FE PE BE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work out_work target_work effect_work operand_work before_work
      node_budget edge_budget site_budget out_budget target_budget effect_budget
      operand_budget before_budget (g : Graph.t N E) (mg : memory_graph N E) scope,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    (forall e, effect_work (snd (effects e)) <= effect_budget e) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
    audit_memory_walk_index_source_work node_work edge_work site_work out_work target_work
      effect_work operand_work before_work (audit_memory_walk_index_counted EN node_enc edge_enc
        site_enc out target effects operand before g mg scope) <=
    audit_memory_walk_index_input_budget EN node_enc edge_enc site_enc out target effects operand
      before node_budget out_budget edge_budget effect_budget target_budget site_budget
      operand_budget before_budget g mg scope.
