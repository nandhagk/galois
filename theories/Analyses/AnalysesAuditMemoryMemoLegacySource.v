(** * Source-shaped memo-threaded legacy projection

    The producer shares normalized setup and threads each complete query's actual memo receipt.
    For example, source traces distinguish retained-pair checking from later indexed load lookup.
    Builds on: complete legacy phases and concrete saved-state memo query source models. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase GraphAuditDfs.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk AnalysesMemoryLegacy
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding.
From Galois.Collections Require Import CollectionsAuditCallback CollectionsAuditMap
  CollectionsAuditFinSet CollectionsAuditEncoding.
From Galois.Analyses Require Import AnalysesAuditMemoryInputBudget AnalysesAuditMemoryRawNext
  AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoWhole
  AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteBound
  AnalysesAuditMemoryMemoPublicSource AnalysesAuditMemoryMemoLegacyPlain AnalysesAuditMemoryIndex
  AnalysesAuditMemoryTable AnalysesAuditMemoryLegacyCfg AnalysesAuditMemoryLegacySliceFull
  AnalysesAuditMemoryLegacyNoClobber AnalysesAuditMemoryLegacyChecker
  AnalysesAuditMemoryLegacySuccessor AnalysesAuditMemoryLegacyProposalSource
  AnalysesAuditMemoryLegacySetupSource AnalysesAuditMemoryLegacyProjectionSource
  AnalysesAuditMemoryLegacyInputBudget AnalysesAuditMemoryGraphCallbacks.
Import List.ListNotations.

Record audit_memo_legacy_receipt (N E T CN CE SE OE BE : Type) : Type := AuditMemoLegacyReceipt {
  audit_memo_legacy_scope_body : list (audit_memory_scope_event T SE);
  audit_memo_legacy_execution : audit_memo_execution N E (audit_memory_version_event N E CN CE)
    (audit_pair_event positive (memory_version N E) (audit_basic_encoding_event positive)
      (audit_memory_version_event N E CN CE))
    (audit_raw_next_event N E T CE SE (audit_map_event N (list E) CN) OE BE)
}.
Arguments AuditMemoLegacyReceipt {N E T CN CE SE OE BE} _ _.
Arguments audit_memo_legacy_scope_body {N E T CN CE SE OE BE} _.
Arguments audit_memo_legacy_execution {N E T CN CE SE OE BE} _.

(** A memo proposal event can carry the receipt of its threaded clobber query. *)
Definition audit_memo_legacy_proposal_event (F N E T CN CE SE XE OE BE LE RE : Type) :=
  audit_legacy_source_proposal_event F N E T CN CE XE BE LE RE
    (audit_memo_legacy_receipt N E T CN CE SE OE BE).

(** A memo legacy event combines the memo proposal and legacy retain observations. *)
Definition audit_memo_legacy_one_event (F N E T CN CE CF SE XE OE BE LE RE WE : Type) :=
  audit_legacy_projection_event F N
    (audit_memo_legacy_proposal_event F N E T CN CE SE XE OE BE LE RE)
    (audit_legacy_projection_retain_event F N T CN CF SE RE WE).

Definition audit_memo_legacy_receipt_work {N E T CN CE SE OE BE}
    (node_work : list CN -> nat) (edge_work : list CE -> nat) (site_work : list SE -> nat)
    (operand_work : list OE -> nat) (before_work : list BE -> nat)
    (receipt : audit_memo_legacy_receipt N E T CN CE SE OE BE) : nat :=
  4 + audit_memory_scope_work site_work (audit_memo_legacy_scope_body receipt) +
  audit_memo_execution_source_work (audit_memory_version_work node_work edge_work)
    (audit_memory_memo_key_work node_work edge_work)
    (audit_raw_next_source_work edge_work site_work (audit_map_source_work node_work)
      operand_work before_work) (audit_memo_legacy_execution receipt).

Definition audit_memo_legacy_setup_counted {N E T CN CE OE TE}
    (EN : encoding N) (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (out : N -> list E * list OE) (target : E -> N * list TE) (g : Graph.t N E)
    (table : Map.t E (Map.t nat (memory_effect T))) :=
  let '(rows, cfg_events) := audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g) in
  let cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd in
  let '(prep, prepare_events) := audit_prepare_source_counted EN cfg
    (audit_legacy_prepare_callbacks node_enc rows) in
  let '(reached, reached_events) := audit_legacy_reached_counted EN node_enc cfg prep
    (Graph.entries cfg) in
  let '(edges, edge_events) := audit_memory_edges out (Graph.nodes g) in
  let '(listed, listed_events) := audit_finset_of_list edge_enc edges in
  @AuditLegacySetupRun N E T CN CE OE TE unit EN cfg prep reached listed table cfg_events
    prepare_events reached_events edge_events listed_events [].

Section One.
  Context {F N E T CN CE CF SE XE OE BE LE RE WE : Type}.
  Context (EN : encoding N) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE).
  Context (operand : N -> option E -> option (memory_version N E) * list OE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E).

  Definition audit_memo_legacy_clobber_counted (state : memo_state EN g effects mg) scope start
    fuel :=
    let '(encoded_scope, run) := audit_memory_memo_public_source_counted node_enc edge_enc
      site_enc EN
      g effects mg state operand before scope start fuel in
    (audit_memo_value run, AuditMemoLegacyReceipt (snd encoded_scope) run).

  Fixpoint audit_memo_legacy_receipt_after (state : memo_state EN g effects mg)
      (events : list (audit_memo_legacy_proposal_event F N E T CN CE SE XE OE BE LE RE)) :=
    match events with
    | [] => state
    | AuditLegacySourceClobbers _ receipt :: _ =>
        @MemoState N E T EN g effects mg (@memo_adjacency N E T EN g effects mg state)
          (@memo_effect_index N E T EN g effects mg state)
          (audit_memo_cache (audit_memo_legacy_execution receipt))
    | _ :: rest => audit_memo_legacy_receipt_after state rest
    end.

  Definition audit_memo_legacy_one_counted {OO TE}
      (setup : @audit_legacy_setup_run N E T CN CE OO TE unit EN)
      (state : memo_state EN g effects mg) function fuel node :=
    let '(proposal, proposal_body) := audit_legacy_occurrence_source_with node_enc edge_enc source
      (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (@memo_effect_index N E T EN g effects mg state) before load reads
      (audit_memo_legacy_clobber_counted state) function fuel node in
    let next := audit_memo_legacy_receipt_after state proposal_body in
    match proposal with
    | None => (None, next, [AuditLegacyProjectionProposal proposal_body;
      AuditLegacyProjectionRetainNone])
    | Some candidate =>
        let cfg := audit_legacy_setup_cfg setup in
        let prep := audit_legacy_setup_prepared setup in
        let '(accepted, body) := audit_legacy_pair_check_full EN EF ET node_enc function_enc
          site_enc
          (audit_legacy_successors_counted EN node_enc cfg prep) reads writes cfg prep
          (audit_legacy_setup_reached setup) node candidate function in
        (if accepted then Some candidate else None, next,
          [AuditLegacyProjectionProposal proposal_body; AuditLegacyProjectionRetain candidate
            accepted body])
    end.
End One.

Inductive audit_memo_legacy_nodes_event (F N MS P CN : Type) : Type :=
  | AuditMemoLegacyNodesCase (remaining : list N)
  | AuditMemoLegacyNodesOne (node : N) (before after : MS)
      (candidate : option (mem_node F N)) (body : list P)
  | AuditMemoLegacyNodesStore
      (body : list (audit_map_event N (option (mem_node F N)) CN)).
Arguments AuditMemoLegacyNodesCase {F N MS P CN} _.
Arguments AuditMemoLegacyNodesOne {F N MS P CN} _ _ _ _ _.
Arguments AuditMemoLegacyNodesStore {F N MS P CN} _.

Section Nodes.
  Context {F N E T CN CE CF SE XE OO TE OE BE LE RE WE : Type}.
  Context (EN : encoding N) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE) (out : N -> list E * list OO) (target : E -> N * list TE).
  Context (operand : N -> option E -> option (memory_version N E) * list OE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E).
  Context (function : F) (fuel : positive).

  Fixpoint audit_memo_legacy_nodes_counted
      (setup : @audit_legacy_setup_run N E T CN CE OO TE unit EN) (nodes : list N)
      (state : memo_state EN g effects mg) (pairs : Map.t N (option (mem_node F N))) :=
    match nodes with
    | [] => (pairs, state, [AuditMemoLegacyNodesCase nodes])
    | node :: rest =>
        let '(candidate, next, body) := audit_memo_legacy_one_counted EN EF ET node_enc edge_enc
          function_enc site_enc source operand before load reads writes g effects mg setup state
          function fuel node in
        let '(updated, store_body) := audit_map_set node_enc node candidate pairs in
        let '(final_pairs, final_state, tail) := audit_memo_legacy_nodes_counted setup rest next
          updated in
        (final_pairs, final_state, [AuditMemoLegacyNodesCase nodes;
          AuditMemoLegacyNodesOne node state next candidate body; AuditMemoLegacyNodesStore
            store_body] ++ tail)
    end.

  Definition audit_memory_memo_legacy_project_counted (state : memo_state EN g effects mg) :=
    let setup := audit_memo_legacy_setup_counted EN node_enc edge_enc out target g
      (@memo_effect_index N E T EN g effects mg state) in
    (setup, audit_memo_legacy_nodes_counted setup (Graph.nodes g) state Map.empty).
End Nodes.

Section SourceWork.
  Context {F N E T CN CE CF SE XE OE BE LE RE WE : Type}.
  Context (EN : encoding N).
  Context (node_work : list CN -> nat) (edge_work : list CE -> nat).
  Context (function_work : list CF -> nat) (site_work : list SE -> nat).
  Context (source_work : list XE -> nat) (operand_work : list OE -> nat).
  Context (before_work : list BE -> nat) (load_work : list LE -> nat).
  Context (read_work : list RE -> nat) (write_work : list WE -> nat).

  Fixpoint audit_memo_legacy_one_source_work
      (events : list (audit_memo_legacy_one_event F N E T CN CE CF SE XE OE BE LE RE WE)) : nat :=
    match events with
    | [] => 0
    | event :: rest =>
        (2 +
          match event with
          | AuditLegacyProjectionProposal body =>
              audit_legacy_occurrence_source_work node_work edge_work source_work before_work
                load_work
                read_work (audit_memo_legacy_receipt_work node_work edge_work site_work operand_work
                  before_work) body
          | AuditLegacyProjectionRetainNone => 1
          | AuditLegacyProjectionRetain _ _ body => audit_legacy_pair_source_work EN node_work
            function_work
              site_work (audit_legacy_successor_source_work node_work) read_work write_work body
          end) + audit_memo_legacy_one_source_work rest
    end.

  Fixpoint audit_memo_legacy_nodes_source_work {MS}
      (events : list (audit_memo_legacy_nodes_event F N MS
        (audit_memo_legacy_one_event F N E T CN CE CF SE XE OE BE LE RE WE) CN)) : nat :=
    match events with
    | [] => 0
    | AuditMemoLegacyNodesCase _ :: rest => 2 + audit_memo_legacy_nodes_source_work rest
    | AuditMemoLegacyNodesOne _ _ _ _ body :: rest =>
        2 + audit_memo_legacy_one_source_work body + audit_memo_legacy_nodes_source_work rest
    | AuditMemoLegacyNodesStore body :: rest =>
        2 + audit_map_source_work node_work body + audit_memo_legacy_nodes_source_work rest
    end.
End SourceWork.

Section InputBudget.
  Context {F N E T CN CE CF SE XE OO TE OE BE LE RE WE : Type}.
  Context (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE) (out : N -> list E * list OO) (target : E -> N * list TE).
  Context (operand : N -> option E -> option (memory_version N E) * list OE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (node_budget out_budget load_budget read_budget write_budget : N -> nat).
  Context (edge_budget source_budget target_budget : E -> nat).
  Context (function_budget : F -> nat) (site_budget : T -> nat).
  Context (operand_budget : N -> option E -> nat) (before_budget : E -> nat -> nat).
  Context (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E).
  Context (function : F) (fuel : positive).
  Let State := memo_state EN g effects mg.
  Let Pairs := Map.t N (option (mem_node F N)).
  Let Setup := @audit_legacy_setup_run N E T CN CE OO TE unit EN.

  (** A query budget witnesses a memo recurrence at the same result and returned entries and
      charges scope work plus binary-credit cost. *)
  Definition audit_memo_legacy_query_input_budget (state : State) scope start
      (result : memory_clobber_result N E) (next : State) (cost : nat) : Prop :=
    let incoming := audit_walk_predecessors node_enc
      (in_index (@memo_adjacency N E T EN g effects mg state)) in
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let key_enc := audit_memory_memo_key_encode node_enc edge_enc in
    let next_versions := audit_memory_raw_next edge_enc site_enc
      (@memo_effect_index N E T EN g effects mg state) incoming operand before scope in
    exists final remaining query_cost,
      audit_memo_input_budget_run version_enc key_enc
        (fst (audit_memory_scope_encode site_enc scope)) next_versions
        (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget)
        (audit_memory_memo_key_input_budget node_enc edge_enc node_budget edge_budget)
        (@audit_raw_next_input_budget N E T CE SE (audit_map_event N (list E) CN) OE BE
          edge_enc site_enc (@memo_effect_index N E T EN g effects mg state) incoming before
          edge_budget site_budget (audit_walk_predecessor_input_budget node_enc node_budget)
          operand_budget before_budget scope)
        FinSet.empty (@memo_entries N E T EN g effects mg state) start (Npos fuel)
        result final remaining query_cost /\
      next = @MemoState N E T EN g effects mg (@memo_adjacency N E T EN g effects mg state)
        (@memo_effect_index N E T EN g effects mg state) final /\
      cost = 4 + audit_memory_scope_input_budget site_enc site_budget scope +
        16 * S (Pos.size_nat fuel) * query_cost.

  Definition audit_memo_legacy_prefix_input_budget (setup : Setup) (state : State) node : nat :=
    audit_legacy_occurrence_with_input_budget node_enc edge_enc source
      (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (@memo_effect_index N E T EN g effects mg state) before load reads
      (fun _ _ _ => (MemoryClobberResult [] false, tt)) node_budget load_budget read_budget
      edge_budget source_budget before_budget (fun _ _ _ => 0) function fuel node.

  Definition audit_memo_legacy_finish_input_budget (setup : Setup) node
      (result : memory_clobber_result N E) : nat :=
    (
      match clobber_roots result with
      | [MemoryDef edge _] => source_budget edge
      | _ => 0
      end) +
    match legacy_clobber_proposal function g result with
    | None => 0
    | Some candidate =>
        let cfg := audit_legacy_setup_cfg setup in
        let prep := audit_legacy_setup_prepared setup in
        audit_legacy_pair_input_budget EN node_enc function_enc site_enc
          (audit_legacy_successors_counted EN node_enc cfg prep) reads writes node_budget
            function_budget
          site_budget (audit_legacy_successors_input_budget node_enc node_budget (out_index prep))
          read_budget write_budget cfg prep node candidate function
    end.

  (** One-node budgeting retains the state on no request or threads the query state and charges
      its selected retention work. *)
  Inductive audit_memo_legacy_one_input_budget (setup : Setup) :
      State -> N -> option (mem_node F N) -> State -> nat -> Prop :=
    | AuditMemoLegacyBudgetNoQuery : forall state node,
        audit_memo_legacy_request EN EE g mg (audit_legacy_setup_reached setup)
          (audit_legacy_setup_listed setup) (@memo_effect_index N E T EN g effects mg state)
          (fun n => fst (reads n)) (fun n => fst (load n)) node = None ->
        audit_memo_legacy_one_input_budget setup state node None state
          (5 + audit_memo_legacy_prefix_input_budget setup state node)
    | AuditMemoLegacyBudgetQuery : forall state node scope start result next query_cost,
        audit_memo_legacy_request EN EE g mg (audit_legacy_setup_reached setup)
          (audit_legacy_setup_listed setup) (@memo_effect_index N E T EN g effects mg state)
          (fun n => fst (reads n)) (fun n => fst (load n)) node = Some (scope, start) ->
        audit_memo_legacy_query_input_budget state scope start result next query_cost ->
        audit_memo_legacy_one_input_budget setup state node
          (legacy_retain EN EF ET function (audit_legacy_setup_cfg setup)
            (audit_legacy_setup_prepared setup) (audit_legacy_setup_reached setup)
            (fun n => fst (writes n)) (fun n => fst (reads n)) node
            (legacy_clobber_proposal function g result)) next
          (5 + audit_memo_legacy_prefix_input_budget setup state node + query_cost +
            audit_memo_legacy_finish_input_budget setup node result).

  (** The list recurrence sums each occurrence once while threading its memo and materialized
    index. *)
  Inductive audit_memo_legacy_nodes_input_budget (setup : Setup) :
      list N -> State -> Pairs -> Pairs -> State -> nat -> Prop :=
    | AuditMemoLegacyBudgetNil : forall state pairs,
        audit_memo_legacy_nodes_input_budget setup [] state pairs pairs state 2
    | AuditMemoLegacyBudgetCons : forall node rest state pairs candidate next final final_state
      one tail,
        audit_memo_legacy_one_input_budget setup state node candidate next one ->
        audit_memo_legacy_nodes_input_budget setup rest next (Map.set EN node candidate pairs)
          final final_state tail ->
        audit_memo_legacy_nodes_input_budget setup (node :: rest) state pairs final final_state
          (6 + one + 2 + node_budget node + 16 * Pos.size_nat (fst (node_enc node)) + tail).
End InputBudget.

Definition audit_memo_legacy_lookup_counted {F N CN} (node_enc : N -> positive * list CN)
    (pairs : Map.t N (option (mem_node F N))) (node : N) :=
  let '(found, body) := audit_map_get node_enc node pairs in
  (
    match found with
    | Some candidate => candidate
    | None => None
    end, body).

(** A node-encoder adapter bounds the source work of the indexed returned-load lookup. *)
Definition audit_memo_legacy_lookup_source_bound_statement : Prop :=
  forall F N CN (node_enc : N -> positive * list CN) node_work node_budget node_source
      (pairs : Map.t N (option (mem_node F N))) node,
    audit_external_callback_adapter node_enc node_work node_source node_budget ->
    4 + audit_map_source_work node_work (snd (audit_memo_legacy_lookup_counted node_enc pairs
      node)) <=
      9 + node_budget node + 5 * Pos.size_nat (fst (node_enc node)).

Section Complete.
  Context {F N E T CN CE CF SE XE OO TE OE BE LE RE WE : Type}.
  Context (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE) (out : N -> list E * list OO) (target : E -> N * list TE).
  Context (operand : N -> option E -> option (memory_version N E) * list OE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E).
  Context (function : F) (fuel : positive) (state : memo_state EN g effects mg).

  Definition audit_memory_memo_legacy_check_counted :=
    let '(setup, (pairs, next, node_body)) := audit_memory_memo_legacy_project_counted EN EF ET
      node_enc edge_enc function_enc site_enc source out target operand before load reads writes
      g effects mg function fuel state in
    let '(accepted, check_body) := audit_legacy_no_clobber_counted EN EF ET node_enc
      function_enc site_enc
      out target reads writes function g (audit_memo_legacy_lookup_counted node_enc pairs) in
    (accepted, setup, pairs, next, node_body, check_body).

  (** Matching encoders and graph and memory callbacks recover the public final memo, every load
      answer and checker boolean. *)
  Definition audit_memory_memo_legacy_source_erases_at : Prop :=
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall f, fst (function_enc f) = encode EF f) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall e, fst (source e) = Graph.source g e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    let '(_, (pairs, next, _)) := audit_memory_memo_legacy_project_counted EN EF ET node_enc
      edge_enc
      function_enc site_enc source out target operand before load reads writes g effects mg
      function fuel state in
    let original := audit_memory_memo_legacy_project EN EE EF ET function g effects
      (fun n => fst (writes n)) (fun n => fst (reads n)) mg state (fun n => fst (load n)) fuel in
    next = snd original /\
    (forall node, fst (audit_memo_legacy_lookup_counted node_enc pairs node) =
      def_of_load (fst original) node) /\
    let '(accepted, _, _, _, _, _) := audit_memory_memo_legacy_check_counted in
    accepted = no_clobber_check EN EF ET function g (fun n => fst (writes n))
      (fun n => fst (reads n)) (fst original).

  Context (node_work : list CN -> nat) (edge_work : list CE -> nat).
  Context (function_work : list CF -> nat) (site_work : list SE -> nat).
  Context (source_work : list XE -> nat) (out_work : list OO -> nat) (target_work : list TE -> nat).
  Context (operand_work : list OE -> nat) (before_work : list BE -> nat).
  Context (load_work : list LE -> nat) (read_work : list RE -> nat) (write_work : list WE -> nat).
  Context (node_budget out_budget load_budget read_budget write_budget : N -> nat).
  Context (edge_budget source_budget target_budget : E -> nat).
  Context (function_budget : F -> nat) (site_budget : T -> nat).
  Context (operand_budget : N -> option E -> nat) (before_budget : E -> nat -> nat).

  Definition audit_memory_memo_legacy_source_work : nat :=
    let '(setup, (_, _, node_body)) := audit_memory_memo_legacy_project_counted EN EF ET node_enc
      edge_enc function_enc site_enc source out target operand before load reads writes g effects mg
      function fuel state in
    4 + audit_legacy_setup_source_work EN node_work edge_work out_work target_work (fun _ => 0)
      setup +
    audit_memo_legacy_nodes_source_work EN node_work edge_work function_work site_work source_work
      operand_work before_work load_work read_work write_work node_body.

  Definition audit_memory_memo_legacy_check_source_work : nat :=
    let '(_, _, _, _, _, check_body) := audit_memory_memo_legacy_check_counted in
    audit_memory_memo_legacy_source_work +
    audit_legacy_no_clobber_source_work EN node_work function_work site_work out_work target_work
      read_work write_work (fun body => 4 + audit_map_source_work node_work body) check_body.

  (** Matching encoders and graph and memory callbacks and adapter laws yield a same-endpoint
      producer recurrence witness and bounds for both producer and checker work. *)
  Definition audit_memory_memo_legacy_whole_input_bound_at : Prop :=
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall f, fst (function_enc f) = encode EF f) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall e, fst (source e) = Graph.source g e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    forall node_source edge_source function_source site_source source_source out_source
      target_source
        operand_source before_source load_source reads_source writes_source,
      audit_external_callback_adapter node_enc node_work node_source node_budget ->
      audit_external_callback_adapter edge_enc edge_work edge_source edge_budget ->
      audit_external_callback_adapter function_enc function_work function_source function_budget ->
      audit_external_callback_adapter site_enc site_work site_source site_budget ->
      audit_external_callback_adapter source source_work source_source source_budget ->
      audit_external_callback_adapter out out_work out_source out_budget ->
      audit_external_callback_adapter target target_work target_source target_budget ->
      audit_external_callback_adapter (fun args => operand (fst args) (snd args)) operand_work
        operand_source (fun args => operand_budget (fst args) (snd args)) ->
      audit_external_callback_adapter (fun args => before (fst args) (snd args)) before_work
        before_source (fun args => before_budget (fst args) (snd args)) ->
      audit_external_callback_adapter load load_work load_source load_budget ->
      audit_external_callback_adapter reads read_work reads_source read_budget ->
      audit_external_callback_adapter writes write_work writes_source write_budget ->
      let '(setup, (pairs, next, _)) := audit_memory_memo_legacy_project_counted EN EF ET
        node_enc edge_enc
        function_enc site_enc source out target operand before load reads writes g effects mg
        function fuel state in
      exists budget,
        audit_memo_legacy_nodes_input_budget EN EE EF ET node_enc edge_enc function_enc site_enc
          source
          operand before load reads writes node_budget load_budget read_budget write_budget
            edge_budget
          source_budget function_budget site_budget operand_budget before_budget g effects mg
            function fuel
          setup (Graph.nodes g) state Map.empty pairs next budget /\
        audit_memory_memo_legacy_source_work <=
          4 + audit_legacy_setup_input_budget EN node_enc edge_enc out target
            (fun e => (effects e, @nil unit)) node_budget out_budget edge_budget target_budget
            (fun _ => 0) g + budget /\
        audit_memory_memo_legacy_check_source_work <=
          4 + audit_legacy_setup_input_budget EN node_enc edge_enc out target
            (fun e => (effects e, @nil unit)) node_budget out_budget edge_budget target_budget
            (fun _ => 0) g + budget +
          audit_legacy_no_clobber_input_budget EN node_enc function_enc site_enc out target
            reads writes
            (audit_memo_legacy_lookup_counted node_enc pairs) node_budget out_budget read_budget
              write_budget
            (fun node => 9 + node_budget node + 5 * Pos.size_nat (fst (node_enc node)))
              function_budget
            site_budget target_budget g function.
End Complete.

(** Matching encoders and graph and memory callbacks recover the public final memo, every load
    answer and checker boolean. *)
Definition audit_memory_memo_legacy_source_erases_statement : Prop :=
  forall F N E T CN CE CF SE XE OO TE OE BE LE RE WE EN EE EF ET
      node_enc edge_enc function_enc site_enc source out target operand before load reads writes
      g effects mg function fuel state,
    @audit_memory_memo_legacy_source_erases_at F N E T CN CE CF SE XE OO TE OE BE LE RE WE
      EN EE EF ET node_enc edge_enc function_enc site_enc source out target operand before load
      reads writes g effects mg function fuel state.

(** Matching encoders and graph and memory callbacks and adapter laws yield a same-endpoint
    producer recurrence witness and bounds for both producer and checker work. *)
Definition audit_memory_memo_legacy_whole_input_bound_statement : Prop :=
  forall F N E T CN CE CF SE XE OO TE OE BE LE RE WE EN EE EF ET
      node_enc edge_enc function_enc site_enc source out target operand before load reads writes
      g effects mg function fuel state node_work edge_work function_work site_work source_work
        out_work
      target_work operand_work before_work load_work read_work write_work node_budget out_budget
      load_budget read_budget write_budget edge_budget source_budget target_budget function_budget
      site_budget operand_budget before_budget,
    @audit_memory_memo_legacy_whole_input_bound_at F N E T CN CE CF SE XE OO TE OE BE LE RE WE
      EN EE EF ET node_enc edge_enc function_enc site_enc source out target operand before load
      reads writes g effects mg function fuel state node_work edge_work function_work site_work
      source_work out_work target_work operand_work before_work load_work read_work write_work
        node_budget
      out_budget load_budget read_budget write_budget edge_budget source_budget target_budget
      function_budget site_budget operand_budget before_budget.
