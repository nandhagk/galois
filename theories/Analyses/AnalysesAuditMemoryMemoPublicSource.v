(** * Fixed public memo query with concrete predecessor reads

    The public source mirror reads predecessors from the saved state's actual incoming trie.
    For example, snapshot queries continue to execute the stored graph after an epoch reuse hit.
    Builds on: plain public memo queries, binary-credit source execution and stored snapshots. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Analyses Require Import AnalysesAuditMemoryRawNext AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoWhole
  AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteBound
  AnalysesAuditMemoryMemoSnapshot AnalysesAuditMemoryMemoSnapshotSource
  AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemoryTable AnalysesAuditMemorySharedBudget.
Import List.ListNotations.

Definition audit_memory_memo_public_source_counted {N E T CN CE SE OE BE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (site_enc : T -> positive * list SE) (EN : encoding N) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (state : memo_state EN g effects mg)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (before : E -> nat -> option (memory_version N E) * list BE) scope start fuel :=
  audit_memory_memo_query_counted node_enc edge_enc site_enc EN g effects mg state
    (audit_walk_predecessors node_enc (in_index (@memo_adjacency N E T EN g effects mg state)))
    operand before scope start fuel.

(** Matching callbacks make the counted query return the plain result and final memo entries. *)
Definition audit_memory_memo_public_source_erases_statement : Prop :=
  forall N E T CN CE SE OE BE (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
      (state : memo_state EN g effects mg)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE) scope start fuel,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    let run := snd (audit_memory_memo_public_source_counted node_enc edge_enc site_enc EN g
      effects mg
      state operand before scope start fuel) in
    let original := audit_memory_memo_query EN EE ET g effects mg state scope start fuel in
    audit_memo_value run = fst original /\
    audit_memo_cache run = @memo_entries N E T EN g effects mg (snd original).

(** Callback budgets yield a same-endpoint memo recurrence witness and bound the public query
    source work. *)
Definition audit_memory_memo_public_whole_input_bound_statement : Prop :=
  forall N E T CN CE SE OE BE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
      (state : memo_state EN g effects mg)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work operand_work before_work
      node_budget edge_budget site_budget operand_budget before_budget scope start fuel,
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
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

Definition audit_snapshot_query_source_counted {N E T Epoch CN CE SE OE BE}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (cache : audit_snapshot_memo_cache N E T Epoch EN)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (before : E -> nat -> option (memory_version N E) * list BE) scope start fuel :=
  let saved := audit_cache_snapshot cache in
  let state := @MemoState N E T EN (snapshot_graph saved) (snapshot_effects saved)
    (snapshot_memory saved) (audit_cache_prepared cache) (audit_cache_effect_index cache)
    (audit_cache_entries cache) in
  audit_memory_memo_public_source_counted node_enc edge_enc site_enc EN (snapshot_graph saved)
    (snapshot_effects saved) (snapshot_memory saved) state operand before scope start fuel.

(** Matching encoders and saved-memory callbacks make the counted query return the plain result
    and final memo entries. *)
Definition audit_snapshot_query_source_erases_statement : Prop :=
  forall N E T Epoch CN CE SE OE BE (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (cache : audit_snapshot_memo_cache N E T Epoch EN)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE) scope start fuel,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n key, fst (operand n key) = memory_operand (snapshot_memory (audit_cache_snapshot
      cache))
      n key) ->
    (forall e i, fst (before e i) = memory_before (snapshot_memory (audit_cache_snapshot cache))
      e i) ->
    let run := snd (audit_snapshot_query_source_counted EN node_enc edge_enc site_enc cache operand
      before scope start fuel) in
    let original := audit_snapshot_query EN EE ET cache scope start fuel in
    audit_memo_value run = fst original /\
    audit_memo_cache run = audit_cache_entries (snd original).

Definition audit_memory_memo_initial_source_counted {N E T CN CE OE TE FE}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
    (g : Graph.t N E) (mg : memory_graph N E) :=
  let '(prep, preparation) := audit_prepare_source_counted EN g
    (audit_snapshot_graph_callbacks node_enc out target) in
  let '(table, rows) := audit_memory_effect_table edge_enc out effects (Graph.nodes g) in
  (@MemoState N E T EN g (fun e => fst (effects e)) mg prep table Map.empty, (preparation, rows)).

(** Matching node and edge encoders and graph callbacks make counted initialization return the
    original initial state. *)
Definition audit_memory_memo_initial_source_erases_statement : Prop :=
  forall N E T CN CE OE TE FE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (effects : E -> list (memory_effect T) * list FE) (g : Graph.t N E) (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    fst (audit_memory_memo_initial_source_counted EN node_enc edge_enc out target effects g mg) =
      memo_initial EN EE g (fun e => fst (effects e)) mg.

(** Matching node, outgoing and target callbacks and callback budgets bound initial graph
    preparation and effect indexing. *)
Definition audit_memory_memo_initial_whole_input_bound_statement : Prop :=
  forall N E T CN CE OE TE FE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (effects : E -> list (memory_effect T) * list FE)
      node_work edge_work out_work target_work effect_work
      node_budget edge_budget out_budget target_budget effect_budget (g : Graph.t N E)
      (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    (forall e, effect_work (snd (effects e)) <= effect_budget e) ->
    let '(_, (preparation, rows)) := audit_memory_memo_initial_source_counted EN node_enc edge_enc
      out target effects g mg in
    4 + audit_prepare_source_work (audit_snapshot_graph_body_work node_work out_work target_work)
      preparation + audit_memory_table_work edge_work out_work effect_work rows <=
    4 + audit_prepare_source_budget EN g + audit_graph_prepare_full_event_bound g *
      audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
        (Graph.nodes g) +
    audit_memory_table_input_budget edge_enc out effects edge_budget out_budget effect_budget
      (Graph.nodes g).

(** Callback budgets yield a same-endpoint recurrence witness and bound saved-snapshot query
    work. *)
Definition audit_snapshot_query_whole_input_bound_statement : Prop :=
  forall N E T Epoch CN CE SE OE BE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (cache : audit_snapshot_memo_cache N E T Epoch EN)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work operand_work before_work
      node_budget edge_budget site_budget operand_budget before_budget scope start fuel,
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
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
