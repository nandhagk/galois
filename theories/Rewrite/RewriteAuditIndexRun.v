(** * RewriteAuditIndexRun

    This module audits rule application and fuel-bounded indexed runs.
    For example, the zero-fuel source claim specifies no events and work 64.
    Builds on: RewriteAuditIndexPrepare and
    RewriteAuditIndexRebuild. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexFind RewriteAuditIndexMembership
  RewriteAuditIndexPair RewriteAuditIndexPrepare RewriteAuditIndexProgramLaws
  RewriteAuditIndexPrograms RewriteAuditIndexRebuild RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_grow_node {K Sort V} (node : rw_node K Sort V)
    (state : rw_graph K Sort V * positive) : (rw_id * (rw_graph K Sort V * positive)) * nat :=
  let '(graph, id) := state in
  let '(aliases, alias_trace) := audit_map_set audit_positive_encode id id (rw_class_roots graph) in
  let '(sorts, st) := audit_map_set audit_positive_encode id (rw_node_sort node) (rw_sorts graph) in
  let '(nodes, nt) := audit_map_set audit_positive_encode id (id, node) (rw_nodes graph) in
  let '(fresh, ft) := rw_fuel_pos_succ id in
  ((id, (RwGraph (id :: rw_roots graph) (id :: rw_nodes_in graph) aliases sorts nodes, fresh)),
    64 + audit_map_source_work audit_basic_encoding_work alias_trace +
      audit_map_source_work audit_basic_encoding_work st +
      audit_map_source_work audit_basic_encoding_work nt + audit_work ft).

Fixpoint rw_ri_grow_term {K Sort V} (term : rw_term K Sort V) (state : rw_graph K Sort V * positive)
    : (rw_id * (rw_graph K Sort V * positive)) * nat :=
  match term with
  | RWVar ty v =>
    let '(out, work) := rw_ri_grow_node (RWNVar ty v) state in (out, 64 + work)
  | RWApp ty op terms =>
    let fix visit (terms : list (rw_term K Sort V)) (state : rw_graph K Sort V * positive) :
        (list rw_id * (rw_graph K Sort V * positive)) * nat :=
      match terms with
      | nil => ((nil, state), 64)
      | term :: rest =>
        let '((id, next), hw) := rw_ri_grow_term term state in
        let '((ids, final), tw) := visit rest next in
        ((id :: ids, final), 64 + hw + tw)
      end in
    let '((ids, next), children_work) := visit terms state in
    let '(out, work) := rw_ri_grow_node (RWNApp ty op ids) next in
    (out, 64 + children_work + work)
  end.

Definition rw_ri_accept_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) (rhs : rw_term K Sort V) :
    option (rw_index_state K Sort V) * nat :=
  let '(graph, graph_work) := rw_ri_graph_atomic state in
  let '((rhs_root, (grown, _)), growth_work) :=
    rw_ri_grow_term rhs (graph, rw_index_fresh state) in
  let '(prepared, prepare_trace) := rw_ri_prepare_once op value grown in
  let '(first, ft) := rw_ri_find_atomic prepared (rw_attempt_root attempt) in
  let prefix := 64 + graph_work + growth_work + rw_ri_prepare_once_work prepare_trace +
    rw_ri_find_trace_cost ft in
  match first with
  | None => (None, prefix)
  | Some a =>
    let '(second, st) := rw_ri_find_atomic prepared rhs_root in
    let prefix := prefix + rw_ri_find_trace_cost st in
    match second with
    | None => (None, prefix)
    | Some b =>
      let '(left_sort, lt) := audit_map_get audit_positive_encode a (rw_sorts grown) in
      let prefix := prefix + audit_map_source_work audit_basic_encoding_work lt in
      match left_sort with
      | None => (None, prefix)
      | Some sa =>
        let '(right_sort, rt) := audit_map_get audit_positive_encode b (rw_sorts grown) in
        let prefix := prefix + audit_map_source_work audit_basic_encoding_work rt in
        match right_sort with
        | None => (None, prefix)
        | Some sb =>
          let '(same_sort, comparison_work) := rw_ri_encoded_equal sort sa sb in
          if same_sort then
            let '((machine, _), trace) := rw_ri_pair_merge_atomic prepared prepared
              (rw_attempt_root attempt, rhs_root) (rw_index_pending prepared) a b nil in
            (Some machine, prefix + comparison_work + rw_ri_pair_trace_cost trace)
          else (None, prefix + comparison_work)
        end
      end
    end
  end.

Definition rw_ri_rule_step_prepared_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) :
    option (rw_index_state K Sort V) * nat :=
  let '(gate, gate_work) := rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  match gate with
  | None => (None, 64 + gate_work)
  | Some (lhs, rhs) =>
    let '(represented, member_work) :=
      rw_ri_member_atomic op sort value state lhs (rw_attempt_root attempt) in
    if represented then
      let '(out, work) := rw_ri_accept_atomic op sort value state attempt rhs in
      (out, 64 + gate_work + member_work + work)
    else (None, 64 + gate_work + member_work)
  end.

Definition rw_ri_rule_step_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) : option (rw_index_state K Sort V) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) := rw_ri_rule_step_prepared_atomic op sort value hole callbacks table state
    attempt in
  (out, 64 + preparation_work + work).

Definition rw_ri_apply_prepared_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) :
    option (rw_index_state K Sort V * list rw_index_event) * nat :=
  let '(applied, work) := rw_ri_rule_step_prepared_atomic op sort value hole callbacks table
    state attempt in
  match applied with
  | None => (None, 64 + work)
  | Some next =>
    let '(out, rebuild_work) := rw_ri_rebuild_atomic op sort value next in
    (Some out, 64 + work + rebuild_work)
  end.

Definition rw_ri_apply_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) :
    option (rw_index_state K Sort V * list rw_index_event) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) := rw_ri_apply_prepared_atomic op sort value hole callbacks table state
    attempt in
  (out, 64 + preparation_work + work).

Record rw_ri_runner (K Sort V H : Type) := RwRiRunner {
  rw_ri_runner_state : rw_index_state K Sort V;
  rw_ri_runner_stopped : bool;
  rw_ri_runner_events : list (rw_run_event K Sort V H)
}.
Arguments RwRiRunner {K Sort V H}.
Arguments rw_ri_runner_state {K Sort V H}.
Arguments rw_ri_runner_stopped {K Sort V H}.
Arguments rw_ri_runner_events {K Sort V H}.

Definition rw_ri_run_once {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (strategy : rw_rp_strategy_adapter K Sort V H)
    (run : rw_ri_runner K Sort V H) : rw_ri_runner K Sort V H * nat :=
  if rw_ri_runner_stopped run then (run, 64)
  else
    let state := rw_ri_runner_state run in
    let '(offer, callback_work, _) := rw_rp_strategy_run op value strategy state in
    match offer with
    | None => (RwRiRunner state true (rw_ri_runner_events run), 64 + callback_work)
    | Some attempt =>
      let '(applied, work) := rw_ri_apply_prepared_atomic op sort value hole callbacks table
        state attempt in
      match applied with
      | None => (RwRiRunner state false (RWRunRejected attempt :: rw_ri_runner_events run),
          64 + callback_work + work)
      | Some (next, events) =>
        (RwRiRunner next false (RWRunAccepted attempt events :: rw_ri_runner_events run),
          64 + callback_work + work)
      end
    end.

Fixpoint rw_ri_run_repeat {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (strategy : rw_rp_strategy_adapter K Sort V H)
    (fuel : positive) (run : rw_ri_runner K Sort V H) : rw_ri_runner K Sort V H * nat :=
  if rw_ri_runner_stopped run then (run, 64)
  else
    match fuel with
    | xH =>
      let '(out, work) := rw_ri_run_once op sort value hole callbacks table strategy run in
      (out, 64 + work)
    | xO rest =>
      let '(middle, mw) := rw_ri_run_repeat op sort value hole callbacks table strategy rest run in
      let '(out, tw) := rw_ri_run_repeat op sort value hole callbacks table strategy rest middle in
      (out, 64 + mw + tw)
    | xI rest =>
      let '(first, fw) := rw_ri_run_once op sort value hole callbacks table strategy run in
      let '(middle, mw) :=
        rw_ri_run_repeat op sort value hole callbacks table strategy rest first in
      let '(out, tw) := rw_ri_run_repeat op sort value hole callbacks table strategy rest middle in
      (out, 64 + fw + mw + tw)
    end.

Definition rw_ri_run_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (strategy : rw_rp_strategy_adapter K Sort V H)
    (fuel : N) (graph : rw_graph K Sort V) :
    (rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H)) * nat :=
  match fuel with
  | N0 => ((RwRunResult graph RWFuelExhausted, nil, nil), 64)
  | Npos fuel =>
    let '(table, rule_preparation_work) := rw_rp_rule_table_atomic rules 0 in
    let '(prepared, prepare_trace) := rw_ri_prepare_once op value graph in
    let '((ready, initial_events), initial_work) := rw_ri_rebuild_atomic op sort value prepared in
    let '(final, run_work) := rw_ri_run_repeat op sort value hole callbacks table strategy fuel
      (RwRiRunner ready false nil) in
    let '(result_graph, graph_work) := rw_ri_graph_atomic (rw_ri_runner_state final) in
    ((RwRunResult result_graph
      (if rw_ri_runner_stopped final then RWStopped else RWFuelExhausted),
      initial_events, rw_ri_runner_events final),
      64 + rw_ri_prepare_once_work prepare_trace + initial_work + run_work + graph_work +
        rule_preparation_work)
  end.

(** A zero-fuel source run returns the input graph, fuel exhaustion, no events, and work 64. *)
Definition rw_ri_run_zero_source_statement : Prop :=
  forall K Sort V H (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules strategy graph,
    rw_ri_run_atomic op sort value hole callbacks rules strategy 0%N graph =
      ((RwRunResult graph RWFuelExhausted, nil, nil), 64).

(** With agreeing encoders and callbacks, sound well-formed rules, and a well-formed, sound,
    productive input graph, the source run yields a well-formed, sound, productive extension,
    clean for nonzero fuel. *)
Definition rw_ri_run_semantic_statement : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) rules adapter fuel graph,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    rw_rp_callbacks_agree EH sig callbacks rules ->
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    rw_graph_wf sig graph -> rw_graph_sound sig admissible rules graph -> rw_productive graph ->
    let '((result, _, _), _) :=
      rw_ri_run_atomic op sort value hole callbacks rules adapter fuel graph in
    rw_graph_wf sig (rw_run_graph result) /\
    rw_graph_sound sig admissible rules (rw_run_graph result) /\
    rw_productive (rw_run_graph result) /\ rw_extends graph (rw_run_graph result) /\
    (fuel <> 0%N -> rw_clean (rw_run_graph result)).
