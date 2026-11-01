(** * Complete clobber search and materialized output

    One adjacency construction precedes search, and only indexed reads occur during search.
    For example, zero reachable successors still pays every source version's adjacency row.
    Builds on: complete walk indexes, binary search and concrete set enumeration. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditElements.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding AnalysesAuditMemoryInputBudget
  AnalysesAuditMemorySearch AnalysesAuditMemorySearchInputBudget AnalysesAuditMemoryDistinct
  AnalysesAuditMemorySharedBudget AnalysesAuditMemoryWalkIndex.
Import List.ListNotations.

(** A clobber search event captures version encoding and indexed successor lookup events. *)
Definition audit_clobber_search_event (N E CN CE : Type) : Type :=
  audit_memory_search_event (memory_version N E) (audit_memory_version_event N E CN CE)
    (audit_map_event (memory_version N E) (list (memory_version N E))
      (audit_memory_version_event N E CN CE)).

Record audit_clobbers_source_run (N E T CN CE SE OE TE FE PE BE : Type) : Type :=
  AuditClobbersSourceRun {
    audit_clobbers_source_result : memory_clobber_result N E;
    audit_clobbers_source_index : audit_walk_index_run N E T CN CE SE OE TE FE PE BE;
    audit_clobbers_source_search : list (audit_clobber_search_event N E CN CE);
    audit_clobbers_source_elements : list (audit_set_elements_event (memory_version N E));
    audit_clobbers_source_distinct : list (audit_memory_distinct_event (memory_version N E)
      (audit_memory_version_event N E CN CE));
    audit_clobbers_source_roots : list (memory_version N E)
  }.
Arguments AuditClobbersSourceRun {N E T CN CE SE OE TE FE PE BE} _ _ _ _ _ _.
Arguments audit_clobbers_source_result {N E T CN CE SE OE TE FE PE BE} _.
Arguments audit_clobbers_source_index {N E T CN CE SE OE TE FE PE BE} _.
Arguments audit_clobbers_source_search {N E T CN CE SE OE TE FE PE BE} _.
Arguments audit_clobbers_source_elements {N E T CN CE SE OE TE FE PE BE} _.
Arguments audit_clobbers_source_distinct {N E T CN CE SE OE TE FE PE BE} _.
Arguments audit_clobbers_source_roots {N E T CN CE SE OE TE FE PE BE} _.

Definition audit_memory_clobbers_source_counted {N E T CN CE SE OE TE FE PE BE}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (operand : N -> option E -> option (memory_version N E) * list PE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (g : Graph.t N E) (mg : memory_graph N E) (scope : memory_scope T)
    (start : memory_version N E) (fuel : positive) :=
  let setup := audit_memory_walk_index_counted EN node_enc edge_enc site_enc out target effects
    operand before g mg scope in
  let enc := audit_memory_version_encode node_enc edge_enc in
  let next := audit_walk_successors node_enc edge_enc (audit_walk_index_value setup) in
  let '(state, search_events) := audit_memory_search_run enc next fuel (memory_search_start
    start) in
  let '(roots, elements_events) := audit_finset_elements (memory_search_roots state) in
  let '(result, distinct_events) := audit_memory_distinct enc (roots ++ memory_search_todo state) in
  AuditClobbersSourceRun
    (MemoryClobberResult result (andb (memory_search_complete state)
      (
        match memory_search_todo state with
        | [] => true
        | _ :: _ => false
        end)))
    setup search_events elements_events distinct_events roots.

Definition audit_memory_clobbers_full_source_work {N E T CN CE SE OE TE FE PE BE}
    (node_work : list CN -> nat) (edge_work : list CE -> nat) (site_work : list SE -> nat)
    (out_work : list OE -> nat) (target_work : list TE -> nat) (effect_work : list FE -> nat)
    (operand_work : list PE -> nat) (before_work : list BE -> nat)
    (run : audit_clobbers_source_run N E T CN CE SE OE TE FE PE BE) : nat :=
  6 + audit_memory_walk_index_source_work node_work edge_work site_work out_work target_work
    effect_work operand_work before_work (audit_clobbers_source_index run) +
  audit_memory_search_source_work (audit_memory_version_work node_work edge_work)
    (audit_map_source_work (audit_memory_version_work node_work edge_work))
    (audit_clobbers_source_search run) +
  audit_set_elements_work (audit_clobbers_source_elements run) +
  length (audit_clobbers_source_roots run) +
  audit_memory_distinct_work (audit_memory_version_work node_work edge_work)
    (audit_clobbers_source_distinct run).

Definition audit_memory_clobbers_whole_input_budget {N E T CN CE SE OE TE FE PE BE}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (operand : N -> option E -> option (memory_version N E) * list PE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (node_budget out_budget : N -> nat) (edge_budget effect_budget target_budget : E -> nat)
    (site_budget : T -> nat) (operand_budget : N -> option E -> nat)
    (before_budget : E -> nat -> nat) (g : Graph.t N E) (mg : memory_graph N E) scope start fuel :=
  let setup := audit_memory_walk_index_counted EN node_enc edge_enc site_enc out target effects
    operand before g mg scope in
  let enc := audit_memory_version_encode node_enc edge_enc in
  let key_budget := audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget in
  let next := audit_walk_successors node_enc edge_enc (audit_walk_index_value setup) in
  let initial := memory_search_start start in
  let state := fst (audit_memory_search_run enc next fuel initial) in
  let roots := FinSet.elements (memory_search_roots state) in
  6 + audit_memory_walk_index_input_budget EN node_enc edge_enc site_enc out target effects operand
    before node_budget out_budget edge_budget effect_budget target_budget site_budget
    operand_budget before_budget g mg scope +
  audit_search_run_input_budget enc next key_budget
    (audit_search_read_input_budget enc key_budget) fuel initial +
  19 * audit_trie_nodes (memory_search_roots state) +
    audit_trie_output_bits (memory_search_roots state) + 6 + length roots +
  audit_memory_distinct_input_budget enc key_budget (roots ++ memory_search_todo state).

(** Matching encoders and graph, effect and memory callbacks recover the public clobber result
    after setup, search and duplicate removal. *)
Definition audit_memory_clobbers_source_erases_statement : Prop :=
  forall N E T CN CE SE OE TE FE PE BE (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      (g : Graph.t N E) (original : E -> list (memory_effect T)) (mg : memory_graph N E)
      scope start fuel,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall e, fst (effects e) = original e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    audit_clobbers_source_result (audit_memory_clobbers_source_counted EN node_enc edge_enc site_enc
      out target effects operand before g mg scope start fuel) =
    memory_clobbers EN EE ET g original mg scope start fuel.

(** Matching node, outgoing and target callbacks and callback budgets bound adjacency, search
    and root-materialization work. *)
Definition audit_memory_clobbers_whole_input_bound_statement : Prop :=
  forall N E T CN CE SE OE TE FE PE BE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work out_work target_work effect_work operand_work before_work
      node_budget edge_budget site_budget out_budget target_budget effect_budget
      operand_budget before_budget (g : Graph.t N E) (mg : memory_graph N E) scope start fuel,
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
    audit_memory_clobbers_full_source_work node_work edge_work site_work out_work target_work
      effect_work operand_work before_work (audit_memory_clobbers_source_counted EN node_enc
        edge_enc
        site_enc out target effects operand before g mg scope start fuel) <=
    audit_memory_clobbers_whole_input_budget EN node_enc edge_enc site_enc out target effects
      operand
      before node_budget out_budget edge_budget effect_budget target_budget site_budget
      operand_budget before_budget g mg scope start fuel.
