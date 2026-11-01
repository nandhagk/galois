(** * Complete legacy projection preparation

    The normalized graph, its reachability, listed original edges and effects are built once.
    For example, a projection with no queried loads still pays every listed setup phase.
    Builds on: complete normalized graph preparation and original effect-table construction. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase GraphAuditDfs.
From Galois.Views Require Import ViewsMemoryEffects ViewsGraph.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier
  AnalysesMemoryLegacy AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Analyses Require Import AnalysesAuditMemoryLegacyCfg
  AnalysesAuditMemoryLegacySliceFull AnalysesAuditMemoryLegacyNoClobber
  AnalysesAuditMemoryLegacyInputBudget AnalysesAuditMemoryIndex AnalysesAuditMemoryTable
  AnalysesAuditMemorySharedBudget AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryGraphCallbacks.
Import List.ListNotations.

Record audit_legacy_setup_run {N E T CN CE OE TE FE} (EN : encoding N) : Type :=
  AuditLegacySetupRun {
    audit_legacy_setup_cfg : Graph.t N (N * N);
    audit_legacy_setup_prepared : prepared EN audit_legacy_setup_cfg;
    audit_legacy_setup_reached : FinSet.t N;
    audit_legacy_setup_listed : FinSet.t E;
    audit_legacy_setup_table : Map.t E (Map.t nat (memory_effect T));
    audit_legacy_setup_cfg_events : list (audit_memory_index_event N (list (N * N)) CN
      (audit_legacy_cfg_event N E CN OE TE));
    audit_legacy_setup_prepare_events : list (audit_prepare_source_event N (N * N)
      (audit_snapshot_graph_body CN (audit_map_event N (list (N * N)) CN) unit));
    audit_legacy_setup_reached_events : list (audit_dfs_nested_event N (N * N)
      (audit_graph_callback_capture N (N * N) (list CN)));
    audit_legacy_setup_edges_events : list (audit_memory_edges_event N E OE);
    audit_legacy_setup_listed_events : list (audit_set_event E CE);
    audit_legacy_setup_table_events : list (audit_memory_table_event N E T CE OE FE)
  }.
Arguments AuditLegacySetupRun {N E T CN CE OE TE FE EN} _ _ _ _ _ _ _ _ _ _ _.
Arguments audit_legacy_setup_cfg {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_prepared {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_reached {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_listed {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_table {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_cfg_events {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_prepare_events {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_reached_events {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_edges_events {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_listed_events {N E T CN CE OE TE FE EN} _.
Arguments audit_legacy_setup_table_events {N E T CN CE OE TE FE EN} _.

Definition audit_legacy_projection_setup {N E T CN CE OE TE FE} (EN : encoding N)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE) (g : Graph.t N E) :=
  let '(rows, cfg_events) := audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g) in
  let cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd in
  let '(prep, prepare_events) := audit_prepare_source_counted EN cfg
    (audit_legacy_prepare_callbacks node_enc rows) in
  let '(reached, reached_events) := audit_legacy_reached_counted EN node_enc cfg prep
    (Graph.entries cfg) in
  let '(edges, edge_events) := audit_memory_edges out (Graph.nodes g) in
  let '(listed, listed_events) := audit_finset_of_list edge_enc edges in
  let '(table, table_events) := audit_memory_effect_table edge_enc out effects (Graph.nodes g) in
  AuditLegacySetupRun cfg prep reached listed table cfg_events prepare_events reached_events
    edge_events listed_events table_events.

Definition audit_legacy_setup_source_work {N E T CN CE OE TE FE} (EN : encoding N)
    (node_work : list CN -> nat) (edge_work : list CE -> nat) (out_work : list OE -> nat)
    (target_work : list TE -> nat) (effect_work : list FE -> nat)
    (run : @audit_legacy_setup_run N E T CN CE OE TE FE EN) : nat :=
  6 + audit_legacy_cfg_source_work node_work out_work target_work (audit_legacy_setup_cfg_events
    run) +
  audit_prepare_source_work
    (audit_snapshot_graph_body_work node_work (audit_map_source_work node_work) (@length unit))
    (audit_legacy_setup_prepare_events run) +
  audit_dfs_source_work node_work (audit_legacy_setup_reached_events run) +
  audit_memory_edges_work out_work (audit_legacy_setup_edges_events run) +
  audit_finset_source_work edge_work (audit_legacy_setup_listed_events run) +
  audit_memory_table_work edge_work out_work effect_work (audit_legacy_setup_table_events run).

Fixpoint audit_legacy_listed_input_budget {E CE} (edge_enc : E -> positive * list CE)
    (edge_budget : E -> nat) (edges : list E) : nat :=
  match edges with
  | [] => 1
  | edge :: rest => 3 + edge_budget edge + 16 * Pos.size_nat (fst (edge_enc edge)) +
      audit_legacy_listed_input_budget edge_enc edge_budget rest
  end.

Definition audit_legacy_setup_input_budget {N E T CN CE OE TE FE} (EN : encoding N)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (node_budget out_budget : N -> nat) (edge_budget target_budget effect_budget : E -> nat)
    (g : Graph.t N E) : nat :=
  let rows := fst (audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g)) in
  let cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd in
  let prep := prepare EN cfg in
  let edges := fst (audit_memory_edges out (Graph.nodes g)) in
  6 + audit_legacy_cfg_input_budget node_enc out target node_budget out_budget target_budget
    (Graph.nodes g) + audit_prepare_source_budget EN cfg +
  audit_graph_prepare_full_event_bound cfg *
    audit_snapshot_graph_input_budget (audit_walk_predecessors node_enc rows)
      (fun edge : N * N => (snd edge, @nil unit)) node_budget
      (audit_walk_predecessor_input_budget node_enc node_budget) (fun _ => 1) (Graph.nodes cfg) +
  audit_legacy_dfs_input_budget EN cfg prep node_budget (Graph.entries cfg) +
  audit_memory_edges_input_budget out out_budget (Graph.nodes g) +
  audit_legacy_listed_input_budget edge_enc edge_budget edges +
  audit_memory_table_input_budget edge_enc out effects edge_budget out_budget effect_budget
    (Graph.nodes g).

(** Matching node and edge codes and graph callbacks make setup produce the original normalized
    graph, reached set, table and indexes. *)
Definition audit_legacy_projection_setup_erases_statement : Prop :=
  forall N E T CN CE OE TE FE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (effects : E -> list (memory_effect T) * list FE) (g : Graph.t N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    let run := audit_legacy_projection_setup EN node_enc edge_enc out target effects g in
    audit_legacy_setup_cfg run = legacy_cfg EN g /\
    audit_legacy_setup_reached run = legacy_reached (prepare EN (legacy_cfg EN g))
      (Graph.entries g) /\
    audit_legacy_setup_listed run = FinSet.of_list EE (edges_of g) /\
    audit_legacy_setup_table run = memory_walk_effect_table EE g (fun e => fst (effects e)) /\
    out_index (audit_legacy_setup_prepared run) = out_index (prepare EN (legacy_cfg EN g)) /\
    in_index (audit_legacy_setup_prepared run) = in_index (prepare EN (legacy_cfg EN g)) /\
    fuel (audit_legacy_setup_prepared run) = fuel (prepare EN (legacy_cfg EN g)) /\
    (forall n, succ_edges (audit_legacy_setup_prepared run) n =
      succ_edges (prepare EN (legacy_cfg EN g)) n).

(** Matching node codes and callback budgets bound the complete input-derived setup work. *)
Definition audit_legacy_setup_whole_input_bound_statement : Prop :=
  forall N E T CN CE OE TE FE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (effects : E -> list (memory_effect T) * list FE)
      node_work edge_work out_work target_work effect_work
      node_budget edge_budget out_budget target_budget effect_budget (g : Graph.t N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    (forall e, effect_work (snd (effects e)) <= effect_budget e) ->
    audit_legacy_setup_source_work EN node_work edge_work out_work target_work effect_work
      (audit_legacy_projection_setup EN node_enc edge_enc out target effects g) <=
    audit_legacy_setup_input_budget EN node_enc edge_enc out target effects node_budget out_budget
      edge_budget target_budget effect_budget g.
