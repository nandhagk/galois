(** * Direct IDF source contracts

    Record the actual forest preparation, priority queue, traversal and callback costs.
    For example, a pruned self-loop still records its live-predicate invocation.
    Builds on: graph audit components, collection source models and binary arithmetic. *)
From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap CollectionsTrie CollectionsAuditCost CollectionsAuditQueue
    CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditElements
      CollectionsAuditTrie CollectionsAuditPrimitive CollectionsAuditCompare
        CollectionsAuditPositiveSub CollectionsAuditNAdd.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators GraphFrontier
  GraphIdf GraphAuditBase GraphAuditDfs GraphAuditDominators GraphAuditFrontier.
Import List.ListNotations.

(** A captured traversal callback is priced at its actual client input. *)
Definition audit_idf_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E -> nat)
    (event : audit_graph_callback_capture V E B) : nat :=
  match event with
  | AuditGraphEncodeCapture _ _ _ v _ _ => encode_budget v
  | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e
  end.

Inductive audit_idf_collect_call (V E : Type) : Type :=
  | AuditIdfCollectCase (site : nat)
  | AuditIdfCollectTarget (e : E) (v : V)
  | AuditIdfCollectParent (v : V) (m : Map.t V V) (result : option V)
  | AuditIdfCollectDom (event : audit_frontier_dom_call V)
  | AuditIdfCollectLive (v : V) (result : bool)
  | AuditIdfCollectOut (v : V) (m : Map.t V (list E)) (result : option (list E))
  | AuditIdfCollectSucc (before after : N).
Arguments AuditIdfCollectCase {V E} _.
Arguments AuditIdfCollectTarget {V E} _ _.
Arguments AuditIdfCollectParent {V E} _ _ _.
Arguments AuditIdfCollectDom {V E} _.
Arguments AuditIdfCollectLive {V E} _ _.
Arguments AuditIdfCollectOut {V E} _ _ _.
Arguments AuditIdfCollectSucc {V E} _ _.

Definition audit_idf_join_counted {V E} (EV : encoding V) (g : Graph.t V E) (t : dom_tree V)
    (live : V -> bool) (root : V) (edge : E) : bool * list (audit_idf_collect_call V E) :=
  let first := Graph.target g edge in let stop := Map.get EV first (idom t) in
  let '(blocked, dom_events) :=
    match stop with
    | None => (false, [])
    | Some q => audit_frontier_dom_counted EV t root q
    end in
  let second := Graph.target g edge in let live_result := live second in
  (negb blocked && live_result, [AuditIdfCollectTarget edge first; AuditIdfCollectParent first
    (idom t) stop] ++
    map AuditIdfCollectDom dom_events ++ [AuditIdfCollectTarget edge second; AuditIdfCollectLive
      second live_result]).

Definition audit_idf_edge_counted {V E} (EV : encoding V) (g : Graph.t V E) (t : dom_tree V)
    (live : V -> bool) (root : V) (acc : list V * N) (edge : E)
    : (list V * N) * list (audit_idf_collect_call V E) :=
  let '(join, events) := audit_idf_join_counted EV g t live root edge in
  let '(values, target_events) := if join then let target := Graph.target g edge in
    (target :: fst acc, [AuditIdfCollectCase 0; AuditIdfCollectTarget edge target])
    else (fst acc, [AuditIdfCollectCase 1]) in
  let next := N.succ (snd acc) in
  ((values, next), events ++ target_events ++ [AuditIdfCollectSucc (snd acc) next]).

Fixpoint audit_idf_edges_counted {V E} (EV : encoding V) (g : Graph.t V E) (t : dom_tree V)
    (live : V -> bool) (root : V) (edges : list E) (acc : list V * N)
    : (list V * N) * list (audit_idf_collect_call V E) :=
  match edges with
  | [] => (acc, [AuditIdfCollectCase 2])
  | edge :: rest => let '(middle, here) := audit_idf_edge_counted EV g t live root acc edge in
      let '(result, later) := audit_idf_edges_counted EV g t live root rest middle in
      (result, AuditIdfCollectCase 3 :: here ++ later)
  end.

Fixpoint audit_idf_nodes_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (live : V -> bool) (root : V)
    (nodes : list V) (acc : list V * N) : (list V * N) * list (audit_idf_collect_call V E) :=
  match nodes with
  | [] => (acc, [AuditIdfCollectCase 4])
  | v :: rest => let found := Map.get EV v (out_index p) in
      let edges :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(middle, here) := audit_idf_edges_counted EV g t live root edges acc in
      let '(result, later) := audit_idf_nodes_counted p t live root rest middle in
      (result, AuditIdfCollectCase 5 :: AuditIdfCollectOut v (out_index p) found :: here ++ later)
  end.

Definition audit_idf_collect_event_work {V E} (EV : encoding V) (event : audit_idf_collect_call V
  E) : nat :=
  64 +
  match event with
  | AuditIdfCollectParent v _ _
  | AuditIdfCollectOut v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditIdfCollectDom inner => audit_frontier_dom_event_work EV inner
  | AuditIdfCollectSucc before _ => audit_binary_weight (Z.of_N before) 1
  | _ => 0
  end.

Definition audit_idf_collect_work {V E} (EV : encoding V) (events : list (audit_idf_collect_call V
  E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_idf_collect_event_work EV event + total) 0 events.

Definition audit_idf_collect_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (nodes : list V) : list E := flat_map (succ_edges p) nodes.

Definition audit_idf_collect_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (nodes : list V) : nat :=
  8 + 4 * length nodes + 32 * length (audit_idf_collect_edges p nodes).

Definition audit_idf_collect_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) (root : V) (nodes : list V) (visits : N) : nat :=
  let edge_targets := map (Graph.target g) (audit_idf_collect_edges p nodes) in
  Nat.max (audit_frontier_runner_width EV t root None)
    (Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) (nodes ++
      edge_targets)))
      (audit_z_bits (Z.of_N (N.add visits (N.of_nat (length edge_targets)))))).

Definition audit_idf_collect_budget {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (t : dom_tree V) (root : V) (nodes : list V) (visits : N) : nat :=
  let count := audit_idf_collect_event_bound p nodes in let width := audit_idf_collect_width EV g
    p t root nodes visits in
  512 * S count * S count + count * (256 + 12 * width).

(** Counted IDF collection returns the fold result with bounded events and work. *)
Definition audit_idf_collect_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
      live root nodes acc,
    let '(result, events) := audit_idf_nodes_counted p t live root nodes acc in
    result = fold_left (idf_collect_node p t live root) nodes acc /\
    length events <= audit_idf_collect_event_bound p nodes /\
    audit_idf_collect_work EV events <= audit_idf_collect_budget EV g p t root nodes (snd acc).

Inductive audit_idf_seed_call (V : Type) : Type :=
  | AuditIdfSeedCase (site : nat)
  | AuditIdfSeedGet (v : V) (m : Map.t V positive) (result : option positive)
  | AuditIdfSeedSub (ceiling rank result : positive)
  | AuditIdfSeedPush (priority : positive) (v : V) (before after : PQueue.t V) (events : list
  (queue_event V)).
Arguments AuditIdfSeedCase {V} _.
Arguments AuditIdfSeedGet {V} _ _ _.
Arguments AuditIdfSeedSub {V} _ _ _.
Arguments AuditIdfSeedPush {V} _ _ _ _ _.

Definition audit_idf_seed_counted {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (queue : PQueue.t V) (v : V) : PQueue.t V * list
      (audit_idf_seed_call V) :=
  let found := Map.get EV v levels in
  match found with
  | None => (queue, [AuditIdfSeedGet v levels found; AuditIdfSeedCase 0])
  | Some _ => let priority_found := Map.get EV v levels in
      let priority :=
        match priority_found with
        | Some rank => Pos.sub ceiling rank
        | None => ceiling
        end in
      let '(next, events) := queue_push EV priority v queue in
      (next, [AuditIdfSeedGet v levels found; AuditIdfSeedCase 1; AuditIdfSeedGet v levels
        priority_found] ++
        (match priority_found with
         | Some rank => [AuditIdfSeedSub ceiling rank priority]
         | None => []
         end) ++
        [AuditIdfSeedPush priority v queue next events])
  end.

Fixpoint audit_idf_seeds_counted {V} (EV : encoding V) (ceiling : positive) (levels : Map.t V
  positive)
    (defs : list V) (queue : PQueue.t V) : PQueue.t V * list (audit_idf_seed_call V) :=
  match defs with
  | [] => (queue, [AuditIdfSeedCase 2])
  | v :: rest => let '(next, here) := audit_idf_seed_counted EV ceiling levels queue v in
      let '(result, later) := audit_idf_seeds_counted EV ceiling levels rest next in
      (result, AuditIdfSeedCase 3 :: here ++ later)
  end.

Definition audit_idf_initial_counted {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) : IdfState.t V * list (audit_idf_seed_call V) :=
  let '(queue, events) := audit_idf_seeds_counted EV ceiling levels defs PQueue.empty in
  (IdfState.Make queue FinSet.empty FinSet.empty FinSet.empty [] 0%N 0%N, events).

Definition audit_idf_seed_event_work {V} (EV : encoding V) (event : audit_idf_seed_call V) : nat :=
  64 +
  match event with
  | AuditIdfSeedGet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_get_weight (encode EV v)
  | AuditIdfSeedSub ceiling rank _ => audit_binary_weight (Z.pos ceiling) (Z.pos rank)
  | AuditIdfSeedPush _ _ _ _ events => queue_model_work EV events
  | AuditIdfSeedCase _ => 0
  end.

Definition audit_idf_initial_work {V} (EV : encoding V) (events : list (audit_idf_seed_call V)) :
  nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_idf_seed_event_work EV event + total) 0 events.

Definition audit_idf_initial_width {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) : nat :=
  Nat.max (audit_key_bits_weight ceiling)
    (Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) defs))
      (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements
        levels)))).

Definition audit_idf_initial_budget {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) : nat :=
  let n := S (length defs) in let width := S (audit_idf_initial_width EV ceiling levels defs) in
  4096 * Nat.pow n 6 * Nat.pow width 2.

(** Counted IDF initialization returns the initial queue with bounded events and work. *)
Definition audit_idf_initial_statement : Prop :=
  forall V (EV : encoding V) ceiling levels defs,
    let '(result, events) := audit_idf_initial_counted EV ceiling levels defs in
    result = idf_initial EV ceiling levels defs /\ length events <= 1 + 6 * length defs /\
    audit_idf_initial_work EV events <= audit_idf_initial_budget EV ceiling levels defs.

Inductive audit_idf_work_call (V E : Type) : Type :=
  | IdfWorkCase : nat -> audit_idf_work_call V E
  | IdfWorkIsEmpty : PQueue.t V -> bool -> audit_idf_work_call V E
  | IdfWorkPop : PQueue.t V -> option (positive * V * PQueue.t V) ->
    list (queue_event V) -> audit_idf_work_call V E
  | IdfWorkPush : positive -> V -> PQueue.t V -> PQueue.t V ->
    list (queue_event V) -> audit_idf_work_call V E
  | IdfWorkGet : V -> Map.t V positive -> option positive -> audit_idf_work_call V E
  | IdfWorkMem : V -> FinSet.t V -> bool -> audit_idf_work_call V E
  | IdfWorkAdd : V -> FinSet.t V -> FinSet.t V -> audit_idf_work_call V E
  | IdfWorkDfs : list (audit_dfs_full_call V V) -> audit_idf_work_call V E
  | IdfWorkCollect : list (audit_idf_collect_call V E) -> audit_idf_work_call V E
  | IdfWorkSub : positive -> positive -> positive -> audit_idf_work_call V E
  | IdfWorkArithmetic : N -> N -> N -> audit_idf_work_call V E.
Arguments IdfWorkCase {V E} _.
Arguments IdfWorkIsEmpty {V E} _ _.
Arguments IdfWorkPop {V E} _ _ _.
Arguments IdfWorkPush {V E} _ _ _ _ _.
Arguments IdfWorkGet {V E} _ _ _.
Arguments IdfWorkMem {V E} _ _ _.
Arguments IdfWorkAdd {V E} _ _ _.
Arguments IdfWorkDfs {V E} _.
Arguments IdfWorkCollect {V E} _.
Arguments IdfWorkSub {V E} _ _ _.
Arguments IdfWorkArithmetic {V E} _ _ _.

Definition audit_idf_emit_counted {V E} (EV : encoding V) ceiling
    (levels : Map.t V positive) (st : IdfState.t V) (v : V)
    : IdfState.t V * list (audit_idf_work_call V E) :=
  let processed := FinSet.mem EV v (IdfState.processed st) in
  let '(pending, queue_events) := if processed then (IdfState.pending st, []) else
    let found := Map.get EV v levels in
    let '(priority, subevents) :=
      match found with
      | Some rank => let priority := Pos.sub ceiling rank in
          (priority, [IdfWorkSub ceiling rank priority])
      | None => (ceiling, [])
      end in
    let '(queue, events) := queue_push EV priority v (IdfState.pending st) in
    (queue, [IdfWorkGet v levels found] ++ subevents ++
      [IdfWorkPush priority v (IdfState.pending st) queue events]) in
  let emitted := FinSet.add EV v (IdfState.emitted st) in
  let was_emitted := FinSet.mem EV v (IdfState.emitted st) in
  let count := if was_emitted then IdfState.output_count st else N.succ (IdfState.output_count st)
    in
  (IdfState.Make pending emitted (IdfState.scanned st) (IdfState.processed st)
    (IdfState.trace st) (IdfState.edge_visits st) count,
    [IdfWorkMem v (IdfState.processed st) processed] ++ queue_events ++
    [IdfWorkAdd v (IdfState.emitted st) emitted;
     IdfWorkMem v (IdfState.emitted st) was_emitted] ++
    if was_emitted then [] else [IdfWorkArithmetic (IdfState.output_count st) 1%N count]).

Fixpoint audit_idf_emit_list_counted {V E} (EV : encoding V) ceiling
    (levels : Map.t V positive) (values : list V) (st : IdfState.t V)
    : IdfState.t V * list (audit_idf_work_call V E) :=
  match values with
  | [] => (st, [IdfWorkCase 0])
  | v :: rest => let '(middle, here) := audit_idf_emit_counted EV ceiling levels st v in
      let '(result, later) := audit_idf_emit_list_counted EV ceiling levels rest middle in
      (result, IdfWorkCase 1 :: here ++ later)
  end.

Fixpoint audit_idf_scan_add_counted {V E} (EV : encoding V) (values : list V)
    (set : FinSet.t V) : FinSet.t V * list (audit_idf_work_call V E) :=
  match values with
  | [] => (set, [IdfWorkCase 2])
  | v :: rest => let next := FinSet.add EV v set in
      let '(result, events) := audit_idf_scan_add_counted EV rest next in
      (result, IdfWorkCase 3 :: IdfWorkAdd v set next :: events)
  end.

Definition audit_idf_work_step_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V)
    (tree_index : prepared EV forest) (levels : Map.t V positive) (live : V -> bool)
    (st : IdfState.t V) : IdfState.t V * list (audit_idf_work_call V E) :=
  let '(popped, pop_events) := queue_pop EV (IdfState.pending st) in
  match popped with
  | None => (st, [IdfWorkPop (IdfState.pending st) popped pop_events; IdfWorkCase 4])
  | Some (_, root, rest) =>
      let '(search, dfs_events) := audit_dfs_full_counted tree_index (IdfState.scanned st) [root] in
      let fresh := preorder search in
      let '(collected, collect_events) := audit_idf_nodes_counted p t live root fresh ([], 0%N) in
      let '(scanned, scan_events) := audit_idf_scan_add_counted EV fresh (IdfState.scanned st) in
      let processed := FinSet.add EV root (IdfState.processed st) in
      let visits := N.add (IdfState.edge_visits st) (snd collected) in
      let started := IdfState.Make rest (IdfState.emitted st) scanned processed
        (root :: IdfState.trace st) visits (IdfState.output_count st) in
      let '(result, emit_events) := audit_idf_emit_list_counted EV (fuel p) levels (fst collected)
        started in
      (result, [IdfWorkPop (IdfState.pending st) popped pop_events; IdfWorkCase 5;
        IdfWorkDfs dfs_events; IdfWorkCollect collect_events] ++ scan_events ++
        [IdfWorkAdd root (IdfState.processed st) processed;
         IdfWorkArithmetic (IdfState.edge_visits st) (snd collected) visits] ++ emit_events)
  end.

Fixpoint audit_idf_run_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V)
    (tree_index : prepared EV forest) (levels : Map.t V positive) (live : V -> bool)
    (k : positive) (st : IdfState.t V) : IdfState.t V * list (audit_idf_work_call V E) :=
  if PQueue.is_empty (IdfState.pending st) then
    (st, [IdfWorkIsEmpty (IdfState.pending st) true; IdfWorkCase 6]) else
    match k with
    | xH => let '(result, events) := audit_idf_work_step_counted p t forest tree_index levels live
      st in
        (result, IdfWorkIsEmpty (IdfState.pending st) false :: IdfWorkCase 7 :: events)
    | xO half => let '(middle, first) := audit_idf_run_counted p t forest tree_index levels live
      half st in
        let '(result, second) := audit_idf_run_counted p t forest tree_index levels live half
          middle in
        (result, IdfWorkIsEmpty (IdfState.pending st) false :: IdfWorkCase 8 :: first ++ second)
    | xI half => let '(middle, first) := audit_idf_run_counted p t forest tree_index levels live
      half st in
        let '(next, second) := audit_idf_run_counted p t forest tree_index levels live half middle
          in
        let '(result, last) := audit_idf_work_step_counted p t forest tree_index levels live next in
        (result, IdfWorkIsEmpty (IdfState.pending st) false :: IdfWorkCase 9 :: first ++ second ++
          last)
    end.

(** Counted IDF work steps erase to the original step. *)
Definition audit_idf_work_step_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    t forest tree_index levels live st,
    fst (audit_idf_work_step_counted p t forest tree_index levels live st) =
      idf_work_step p t forest tree_index levels live st.

(** Counted IDF runs erase to the original run. *)
Definition audit_idf_run_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    t forest tree_index levels live k st,
    fst (audit_idf_run_counted p t forest tree_index levels live k st) =
      idf_run p t forest tree_index levels live k st.

Inductive audit_idf_producer_call (V E : Type) : Type :=
  | IdfProducerDom : audit_dom_call V E -> audit_idf_producer_call V E
  | IdfProducerPrepare : audit_prepare_nested_event V V (audit_dom_body V) ->
    audit_idf_producer_call V E
  | IdfProducerDfs : audit_dfs_nested_event V V (audit_dom_body V) ->
    audit_idf_producer_call V E
  | IdfProducerSeed : audit_idf_seed_call V -> audit_idf_producer_call V E
  | IdfProducerWork : audit_idf_work_call V E -> audit_idf_producer_call V E
  | IdfProducerLevelGet : V -> Map.t V V -> option V -> audit_idf_producer_call V E
  | IdfProducerLevelRead : V -> Map.t V positive -> option positive -> audit_idf_producer_call V E
  | IdfProducerLevelWrite : V -> positive -> Map.t V positive -> Map.t V positive ->
    audit_idf_producer_call V E
  | IdfProducerCase : nat -> audit_idf_producer_call V E.
Arguments IdfProducerDom {V E} _.
Arguments IdfProducerPrepare {V E} _.
Arguments IdfProducerDfs {V E} _.
Arguments IdfProducerSeed {V E} _.
Arguments IdfProducerWork {V E} _.
Arguments IdfProducerLevelGet {V E} _ _ _.
Arguments IdfProducerLevelRead {V E} _ _ _.
Arguments IdfProducerLevelWrite {V E} _ _ _ _.
Arguments IdfProducerCase {V E} _.

Fixpoint audit_idf_levels_fold_counted {V E} (EV : encoding V) (parents : Map.t V V)
    (order : list V) (levels : Map.t V positive)
    : Map.t V positive * list (audit_idf_producer_call V E) :=
  match order with
  | [] => (levels, [IdfProducerCase 0])
  | v :: rest =>
      let found := Map.get EV v parents in
      let '(level, reads) :=
      match found with
      | None => (xH, [])
      | Some parent => let prior := Map.get EV parent levels in
          (Pos.succ (
            match prior with
            | Some x => x
            | None => xH
            end),
           [IdfProducerLevelRead parent levels prior]) end in
      let next := Map.set EV v level levels in
      let '(result, events) := audit_idf_levels_fold_counted EV parents rest next in
      (result, [IdfProducerCase 1; IdfProducerLevelGet v parents found] ++ reads ++
        [IdfProducerLevelWrite v level levels next] ++ events)
  end.

Definition audit_direct_pruned_idf_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) (live : V -> bool)
    : FinSet.t V * list (audit_idf_producer_call V E) :=
  let parents := idom t in
  let '(search, search_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let vertices := preorder search in
  let rows := Map.elements parents in
  let '(children, child_events) := audit_dom_children_counted EV rows in
  let '(roots, root_events) := audit_dom_roots_counted EV parents vertices in
  let forest := Graph.Make roots vertices (fun v => index_edges EV children v)
    (fun v =>
      match Map.get EV v parents with
      | Some u => u
      | None => v
      end) (fun v => v) in
  let '(tree_index, prepare_events) :=
    audit_graph_prepare_nested_counted EV forest (audit_dom_prepare_callbacks EV children) in
  let '(level_search, level_dfs_events) :=
    audit_dfs_nested_counted tree_index (audit_dom_dfs_callbacks EV) FinSet.empty roots in
  let '(levels, level_events) := audit_idf_levels_fold_counted EV parents (rpo level_search)
    Map.empty in
  let '(initial, initial_events) := audit_idf_initial_counted EV (fuel p) levels defs in
  let '(result, run_events) := audit_idf_run_counted p t forest tree_index levels live
    (Pos.of_succ_nat (length (Graph.nodes g))) initial in
  (IdfState.emitted result,
    map (fun event => IdfProducerDom (AuditDomInitialDfs event)) search_events ++
    [IdfProducerDom (AuditDomElements parents rows)] ++
    map IdfProducerDom child_events ++ map IdfProducerDom root_events ++
    map IdfProducerPrepare prepare_events ++ map IdfProducerDfs level_dfs_events ++
    level_events ++ map IdfProducerSeed initial_events ++ map IdfProducerWork run_events).

(** Counted direct pruned IDF erases to the original result. *)
Definition audit_direct_pruned_idf_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) t defs live,
    fst (audit_direct_pruned_idf_counted p t defs live) = direct_pruned_idf p t defs live.

Definition audit_direct_idf_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) :=
  audit_direct_pruned_idf_counted p t defs (fun _ => true).

(** Counted direct IDF erases to the original result. *)
Definition audit_direct_idf_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) t defs,
    fst (audit_direct_idf_counted p t defs) = direct_idf p t defs.

Definition audit_idf_dom_body_event_work {V} (EV : encoding V) (event : audit_dom_body V) : nat :=
  64 +
  match event with
  | AuditDomBodyRead v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditDomBodyEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditDomBodyTarget _ => 0
  end.

Definition audit_idf_dom_event_work {V E} (EV : encoding V) (event : audit_dom_call V E) : nat :=
  64 +
  match event with
  | AuditDomInitialDfs item => audit_dfs_full_model_event EV item
  | AuditDomElements input _ => 64 * Nat.pow (S (Trie.size input)) 3
  | AuditDomChildRead v _ _
  | AuditDomRootGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditDomChildSet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditDomPrepare (outer, body) => audit_graph_full_event_work outer +
      fold_right (fun item n => audit_idf_dom_body_event_work EV item + n) 0 body
  | AuditDomDfs (outer, body) => audit_dfs_full_model_event EV outer +
      fold_right (fun item n => audit_idf_dom_body_event_work EV item + n) 0 body
  | AuditDomOutput size => S size
  | AuditDomCase _ => 0
  end.

Definition audit_idf_work_event_work {V E} (EV : encoding V) (event : audit_idf_work_call V E) :
  nat :=
  64 +
  match event with
  | IdfWorkPop _ _ events
  | IdfWorkPush _ _ _ _ events => queue_model_work EV events
  | IdfWorkGet v _ _
  | IdfWorkMem v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | IdfWorkAdd v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | IdfWorkDfs events =>
      fold_right (fun item n => audit_dfs_full_model_event EV item + n) 0 events
  | IdfWorkCollect events =>
      fold_right (fun item n => audit_idf_collect_event_work EV item + n) 0 events
  | IdfWorkSub a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | IdfWorkArithmetic a b _ => audit_binary_weight (Z.of_N a) (Z.of_N b)
  | IdfWorkCase _
  | IdfWorkIsEmpty _ _ => 0
  end.

Definition audit_idf_producer_event_work {V E} (EV : encoding V)
    (event : audit_idf_producer_call V E) : nat :=
  64 +
  match event with
  | IdfProducerDom item => audit_idf_dom_event_work EV item
  | IdfProducerPrepare (outer, body) => audit_graph_full_event_work outer +
      fold_right (fun item n => audit_idf_dom_body_event_work EV item + n) 0 body
  | IdfProducerDfs (outer, body) => audit_dfs_full_model_event EV outer +
      fold_right (fun item n => audit_idf_dom_body_event_work EV item + n) 0 body
  | IdfProducerSeed item => audit_idf_seed_event_work EV item
  | IdfProducerWork item => audit_idf_work_event_work EV item
  | IdfProducerLevelGet v _ _
  | IdfProducerLevelRead v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | IdfProducerLevelWrite v _ _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | IdfProducerCase _ => 0
  end.

Definition audit_idf_selected_work {V E} (EV : encoding V)
    (events : list (audit_idf_producer_call V E)) : nat :=
  1024 * S (length events) * S (length events) +
    fold_right (fun item n => audit_idf_producer_event_work EV item + n) 0 events.

Definition audit_idf_input_support {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : list V :=
  let rows := Map.elements (out_index p) in
  let parents := Map.elements (idom t) in
  defs ++ Graph.entries g ++ Graph.nodes g ++ map fst rows ++
    map (Graph.target g) (flat_map snd rows) ++ map fst parents ++ map snd parents ++
    map fst (Map.elements (tin t)) ++ map fst (Map.elements (tout t)).

Definition audit_idf_input_scale {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  let rows := Map.elements (out_index p) in
  1 + length (audit_idf_input_support p t defs) + length (flat_map snd rows) +
    Trie.size (out_index p) + Trie.size (idom t) + Trie.size (tin t) + Trie.size (tout t) +
    Pos.to_nat (fuel p).

Definition audit_idf_input_width {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  let numbers := fuel p :: map snd (Map.elements (tin t)) ++ map snd (Map.elements (tout t)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v))
    (audit_idf_input_support p t defs)))
    (fold_right Nat.max 0 (map audit_key_bits_weight numbers)).

Definition audit_idf_selected_input_budget {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  (1024 * 1024)%nat * Nat.pow (S (audit_idf_input_scale p t defs)) 24 *
    Nat.pow (S (audit_idf_input_width p t defs)) 4.

(** Counted direct pruned IDF preserves the result and bounds selected work. *)
Definition audit_direct_pruned_idf_selected_bound_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) t defs live,
    let '(result, events) := audit_direct_pruned_idf_counted p t defs live in
    result = direct_pruned_idf p t defs live /\
    audit_idf_selected_work EV events <= audit_idf_selected_input_budget p t defs.

(** Events retain every callback input, result and body of this execution. *)
Inductive audit_idf_collect_source_event (V E B : Type) : Type :=
  | IdfCollectSourceCase : nat -> audit_idf_collect_source_event V E B
  | IdfCollectSourceTarget : E -> V -> list B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceLive : V -> bool -> list B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceParent : audit_map_event V V B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceEdges : audit_map_event V (list E) B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceDom : audit_frontier_source_event V E B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceSucc : N -> N -> audit_idf_collect_source_event V E B.
Arguments IdfCollectSourceCase {V E B} _.
Arguments IdfCollectSourceTarget {V E B} _ _ _.
Arguments IdfCollectSourceLive {V E B} _ _ _.
Arguments IdfCollectSourceParent {V E B} _.
Arguments IdfCollectSourceEdges {V E B} _.
Arguments IdfCollectSourceDom {V E B} _.
Arguments IdfCollectSourceSucc {V E B} _ _.

(** The join tests dominance and liveness, retaining both actual target calls. *)
Definition audit_idf_collect_source_join {V E B} (enc : V -> positive * list B)
    (target : E -> V * list B) (live : V -> bool * list B) (t : dom_tree V) (root : V) (edge : E)
    : bool * list (audit_idf_collect_source_event V E B) :=
  let '(first, first_body) := target edge in
  let '(parent, parent_events) := audit_map_get enc first (idom t) in
  let '(blocked, dom_events) :=
    match parent with
    | None => (false, [])
    | Some v => audit_frontier_source_dom enc t root v
    end in
  let '(second, second_body) := target edge in
  let '(is_live, live_body) := live second in
  (negb blocked && is_live, [IdfCollectSourceTarget edge first first_body] ++
    map IdfCollectSourceParent parent_events ++ map IdfCollectSourceDom dom_events ++
    [IdfCollectSourceTarget edge second second_body; IdfCollectSourceLive second is_live
      live_body]).

(** Every edge increments its binary counter; emitted targets call the source callback again. *)
Definition audit_idf_collect_source_edge {V E B} (enc : V -> positive * list B)
    (target : E -> V * list B) (live : V -> bool * list B) (t : dom_tree V) (root : V)
    (acc : list V * N) (edge : E) : (list V * N) * list (audit_idf_collect_source_event V E B) :=
  let '(emit, calls) := audit_idf_collect_source_join enc target live t root edge in
  let '(values, value_events) := if emit then
    let '(v, body) := target edge in (v :: fst acc, [IdfCollectSourceTarget edge v body])
    else (fst acc, []) in
  let count := N.succ (snd acc) in
  ((values, count), calls ++ value_events ++ [IdfCollectSourceSucc (snd acc) count]).

(** The edge fold preserves every occurrence and intermediate accumulator. *)
Fixpoint audit_idf_collect_source_edges {V E B} (enc : V -> positive * list B)
    (target : E -> V * list B) (live : V -> bool * list B) (t : dom_tree V) (root : V)
    (edges : list E) (acc : list V * N) : (list V * N) * list (audit_idf_collect_source_event V E
      B) :=
  match edges with
  | [] => (acc, [IdfCollectSourceCase 0])
  | edge :: rest =>
      let '(next, calls) := audit_idf_collect_source_edge enc target live t root acc edge in
      let '(result, events) := audit_idf_collect_source_edges enc target live t root rest next in
      (result, IdfCollectSourceCase 1 :: calls ++ events)
  end.

(** Node collection uses the actual prepared adjacency map for each scanned vertex. *)
Fixpoint audit_idf_collect_source_nodes {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (enc : V -> positive * list B) (target : E -> V * list B)
    (live : V -> bool * list B) (t : dom_tree V) (root : V) (vertices : list V) (acc : list V * N)
    : (list V * N) * list (audit_idf_collect_source_event V E B) :=
  match vertices with
  | [] => (acc, [IdfCollectSourceCase 2])
  | v :: rest =>
      let '(found, reads) := audit_map_get enc v (out_index p) in
      let edges :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(next, calls) := audit_idf_collect_source_edges enc target live t root edges acc in
      let '(result, events) := audit_idf_collect_source_nodes p enc target live t root rest next in
      (result, IdfCollectSourceCase 3 :: map IdfCollectSourceEdges reads ++ calls ++ events)
  end.

(** The actual source fold and its captured callbacks erase to node collection. *)
Definition audit_idf_collect_source_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (enc : V -> positive * list B) (target : E -> V * list B) (live : V -> bool * list B)
    (live_value : V -> bool) t root vertices acc,
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall v, fst (live v) = live_value v) ->
    fst (audit_idf_collect_source_nodes p enc target live t root vertices acc) =
      fold_left (idf_collect_node p t live_value root) vertices acc.

(** Primitive work includes every recorded call and binary counter step. *)
Definition audit_idf_collect_source_event_work {V E B} (weight : B -> nat)
    (event : audit_idf_collect_source_event V E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 +
  match event with
  | IdfCollectSourceCase _ => 0
  | IdfCollectSourceTarget _ _ xs
  | IdfCollectSourceLive _ _ xs => body xs
  | IdfCollectSourceParent call => audit_map_source_work body [call]
  | IdfCollectSourceEdges call => audit_map_source_work body [call]
  | IdfCollectSourceDom call => audit_frontier_source_event_work weight call
  | IdfCollectSourceSucc n _ => 4 + 2 *
    match n with
    | N0 => 0
    | Npos p => Pos.size_nat p
    end
  end.

(** Only bodies of actual supplied callbacks are external. *)
Definition audit_idf_collect_source_event_external {V E B} (weight : B -> nat)
    (event : audit_idf_collect_source_event V E B) : nat :=
  match event with
  | IdfCollectSourceTarget _ _ body
  | IdfCollectSourceLive _ _ body
  | IdfCollectSourceParent (AuditMapGet _ _ _ _ body _)
  | IdfCollectSourceParent (AuditMapSet _ _ _ _ _ body _)
  | IdfCollectSourceParent (AuditMapRemove _ _ _ _ body _)
  | IdfCollectSourceEdges (AuditMapGet _ _ _ _ body _)
  | IdfCollectSourceEdges (AuditMapSet _ _ _ _ _ body _)
  | IdfCollectSourceEdges (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun x n => weight x + n) 0 body
  | IdfCollectSourceDom call => audit_frontier_source_body_event_work weight call
  | _ => 0
  end.

(** Source work includes trace-list composition for this execution. *)
Definition audit_idf_collect_source_work {V E B} (weight : B -> nat)
    (events : list (audit_idf_collect_source_event V E B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_idf_collect_source_event_work weight event + n) 0 events.

(** External work sums the captured callback bodies in the same events. *)
Definition audit_idf_collect_source_external {V E B} (weight : B -> nat)
    (events : list (audit_idf_collect_source_event V E B)) : nat :=
  fold_right (fun event n => audit_idf_collect_source_event_external weight event + n) 0 events.

(** The bound uses actual prepared edges, tree indexes, queried nodes and counter width. *)
Definition audit_idf_collect_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) (root : V) (vertices : list V) (acc : list V * N) : nat :=
  let rows := Map.elements (out_index p) in
  let edges := flat_map snd rows in
  let parents := Map.elements (idom t) in
  let before := Map.elements (tin t) in
  let after := Map.elements (tout t) in
  let keys := root :: vertices ++ fst acc ++ map fst rows ++ map (Graph.target g) edges ++
    map fst parents ++ map snd parents ++ map fst before ++ map fst after in
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) keys) in
  let ranks := fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (before ++ after)) in
  let counter :=
    match snd acc with
    | N0 => 0
    | Npos n => Pos.size_nat n
    end in
  4096 * Nat.pow (S (length keys + length edges + width + ranks + counter)) 6.

(** The same source fold has an input-derived bound plus actual callback bodies. *)
Definition audit_idf_collect_source_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (enc : V -> positive * list B) (target : E -> V * list B) (live : V -> bool * list B)
    t root vertices acc (weight : B -> nat),
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    let events := snd (audit_idf_collect_source_nodes p enc target live t root vertices acc) in
    audit_idf_collect_source_work weight events <= audit_idf_collect_source_budget EV g p t root
      vertices acc +
      audit_idf_collect_source_external weight events.

(** Nested frontier events identify actual client callback inputs. *)
Definition audit_idf_frontier_event_budget {V E B} (encode_budget : V -> nat) (target_budget
  source_budget : E -> nat)
    (event : audit_frontier_source_event V E B) : nat :=
  match event with
  | FrontierSourceDfs (_, calls) =>
      fold_right (fun call n => audit_idf_capture_budget encode_budget target_budget call + n) 0
        calls
  | FrontierSourceSource e _ _ => source_budget e
  | FrontierSourceTarget e _ _ => target_budget e
  | FrontierSourceParent (AuditMapGet v _ _ _ _ _)
  | FrontierSourceParent (AuditMapSet v _ _ _ _ _
    _) |
    FrontierSourceParent (AuditMapRemove v _ _ _ _ _) | FrontierSourceRank (AuditMapGet v _ _ _ _
      _) |
    FrontierSourceRank (AuditMapSet v _ _ _ _ _ _) | FrontierSourceRank (AuditMapRemove v _ _ _ _
      _) |
    FrontierSourcePred (AuditMapGet v _ _ _ _ _) | FrontierSourcePred (AuditMapSet v _ _ _ _ _ _) |
    FrontierSourcePred (AuditMapRemove v _ _ _ _ _) | FrontierSourceRows (AuditMapGet v _ _ _ _ _) |
    FrontierSourceRows (AuditMapSet v _ _ _ _ _ _) | FrontierSourceRows (AuditMapRemove v _ _ _ _
      _) |
    FrontierSourceSet (AuditSetAdd v _ _ _ _ _) | FrontierSourceSet (AuditSetMem v _ _ _ _ _) |
    FrontierSourceSet (AuditSetRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

(** Each collector event prices the actual invocation, including repeated targets. *)
Definition audit_idf_collect_source_event_budget {V E B} (encode_budget live_budget : V -> nat)
    (target_budget : E -> nat) (event : audit_idf_collect_source_event V E B) : nat :=
  match event with
  | IdfCollectSourceTarget e _ _ => target_budget e
  | IdfCollectSourceLive v _ _ => live_budget v
  | IdfCollectSourceParent (AuditMapGet v _ _ _ _ _)
  | IdfCollectSourceParent (AuditMapSet v _ _ _
    _ _ _) |
    IdfCollectSourceParent (AuditMapRemove v _ _ _ _ _) | IdfCollectSourceEdges (AuditMapGet v _ _
      _ _ _) |
    IdfCollectSourceEdges (AuditMapSet v _ _ _ _ _ _) | IdfCollectSourceEdges (AuditMapRemove v _
      _ _ _ _) =>
      encode_budget v
  | IdfCollectSourceDom call => audit_idf_frontier_event_budget encode_budget target_budget (fun _
    => 0) call
  | _ => 0
  end.

(** The adapted collector bounds the same source fold by per-call input budgets. *)
Definition audit_idf_collect_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (enc : V -> positive * list B) (target : E -> V * list B) (live : V -> bool * list B)
    (live_value : V -> bool) t root vertices acc (weight : B -> nat)
    encode_source target_source live_source encode_budget target_budget live_budget,
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall v, fst (live v) = live_value v) ->
    audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
    audit_graph_external_callback_adapter target weight target_source target_budget ->
    audit_graph_external_callback_adapter live weight live_source live_budget ->
    let '(result, events) := audit_idf_collect_source_nodes p enc target live t root vertices acc in
    result = fold_left (idf_collect_node p t live_value root) vertices acc /\
    audit_idf_collect_source_work weight events <= audit_idf_collect_source_budget EV g p t root
      vertices acc +
      fold_right (fun event n => audit_idf_collect_source_event_budget encode_budget live_budget
        target_budget event + n)
        0 events.

(** This component contract does not claim the complete IDF worklist bound. *)
Definition audit_idf_collect_source_contract_statement : Prop :=
  audit_idf_collect_source_erasure_statement /\ audit_idf_collect_source_bound_statement /\
  audit_idf_collect_source_adapted_statement.

(** Events retain actual map, set, queue and arithmetic invocations. *)
Inductive audit_idf_queue_event (V B : Type) : Type :=
  | IdfQueueCase : nat -> audit_idf_queue_event V B
  | IdfQueueMap : audit_map_event V positive B -> audit_idf_queue_event V B
  | IdfQueueSet : audit_set_event V B -> audit_idf_queue_event V B
  | IdfQueuePush : audit_queue_nested_event V (positive * list B) -> audit_idf_queue_event V B
  | IdfQueueSub : audit_idf_sub_event -> audit_idf_queue_event V B
  | IdfQueueSucc : audit_nat_encoding_event -> audit_idf_queue_event V B.
Arguments IdfQueueCase {V B} _.
Arguments IdfQueueMap {V B} _.
Arguments IdfQueueSet {V B} _.
Arguments IdfQueuePush {V B} _.
Arguments IdfQueueSub {V B} _.
Arguments IdfQueueSucc {V B} _.

(** Priority reads the actual level and follows the binary subtraction path when present. *)
Definition audit_idf_queue_priority {V B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (v : V) : positive * list (audit_idf_queue_event V B) :=
  let '(found, reads) := audit_map_get enc v levels in
  match found with
  | None => (ceiling, map IdfQueueMap reads ++ [IdfQueueCase 0])
  | Some rank => let '(result, calls) := audit_idf_sub_counted ceiling rank in
      (result, map IdfQueueMap reads ++ [IdfQueueCase 1] ++ map IdfQueueSub calls)
  end.

(** Each seed performs the source's first lookup and, when present, its second priority lookup. *)
Definition audit_idf_queue_seed {V B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (q : PQueue.t V) (v : V) : PQueue.t V * list
      (audit_idf_queue_event V B) :=
  let '(found, reads) := audit_map_get enc v levels in
  match found with
  | None => (q, map IdfQueueMap reads ++ [IdfQueueCase 2])
  | Some _ =>
      let '(priority, calls) := audit_idf_queue_priority enc ceiling levels v in
      let '(result, queue_events) := audit_queue_recorded_push enc priority v q in
      (result, map IdfQueueMap reads ++ [IdfQueueCase 3] ++ calls ++ map IdfQueuePush queue_events)
  end.

(** Seed folding preserves duplicate definitions and every intermediate queue. *)
Fixpoint audit_idf_queue_seeds {V B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) (q : PQueue.t V) : PQueue.t V * list
      (audit_idf_queue_event V B) :=
  match defs with
  | [] => (q, [IdfQueueCase 4])
  | v :: rest => let '(next, calls) := audit_idf_queue_seed enc ceiling levels q v in
      let '(result, events) := audit_idf_queue_seeds enc ceiling levels rest next in
      (result, IdfQueueCase 5 :: calls ++ events)
  end.

(** Binary counter increment exposes the positive successor frames when present. *)
Definition audit_idf_queue_succ (value : N) : N * list audit_nat_encoding_event :=
  match value with
  | N0 => (1%N, [])
  | Npos p => let '(next, events) := audit_positive_succ p in (Npos next, events)
  end.

(** Emission records both set calls and pushes only when the vertex is not processed. *)
Definition audit_idf_queue_emit {V B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (st : IdfState.t V) (v : V) : IdfState.t V * list
      (audit_idf_queue_event V B) :=
  let '(processed, pe) := audit_finset_mem enc v (IdfState.processed st) in
  let '(pending, queue_events) := if processed then (IdfState.pending st, []) else
    let '(priority, calls) := audit_idf_queue_priority enc ceiling levels v in
    let '(q, events) := audit_queue_recorded_push enc priority v (IdfState.pending st) in
    (q, calls ++ map IdfQueuePush events) in
  let '(emitted, ee) := audit_finset_add enc v (IdfState.emitted st) in
  let '(was_emitted, we) := audit_finset_mem enc v (IdfState.emitted st) in
  let '(count, ce) := if was_emitted then (IdfState.output_count st, [])
    else audit_idf_queue_succ (IdfState.output_count st) in
  (IdfState.Make pending emitted (IdfState.scanned st) (IdfState.processed st)
    (IdfState.trace st) (IdfState.edge_visits st) count,
    map IdfQueueSet pe ++ queue_events ++ map IdfQueueSet ee ++ map IdfQueueSet we ++ map
      IdfQueueSucc ce).

(** These source operations return the exact queue states and emitted state. *)
Definition audit_idf_queue_source_erasure_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) ceiling levels defs q st v,
    (forall key, fst (enc key) = encode EV key) ->
    fst (audit_idf_queue_seeds enc ceiling levels defs q) = fold_left (idf_seed EV ceiling levels)
      defs q /\
    fst (audit_idf_queue_emit enc ceiling levels st v) = idf_emit EV ceiling levels st v.

(** Each queue event includes actual primitive source work and callback bodies. *)
Definition audit_idf_queue_event_work {V B} (weight : B -> nat) (event : audit_idf_queue_event V
  B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 +
  match event with
  | IdfQueueCase _ => 0
  | IdfQueueMap call => audit_map_source_work body [call]
  | IdfQueueSet call => audit_finset_source_work body [call]
  | IdfQueuePush call => audit_queue_recorded_full_source_work weight [call]
  | IdfQueueSub _ => 16
  | IdfQueueSucc _ => 4
  end.

(** A captured queue body contributes only its supplied encoder work. *)
Definition audit_idf_queue_push_external {V B} (weight : B -> nat)
    (event : audit_queue_nested_event V (positive * list B)) : nat :=
  let '(_, (_, calls)) := event in
  fold_right (fun call n => fold_right (fun x k => weight x + k) 0 (snd call) + n) 0 calls.

(** The external measure counts only bodies at actual encoder invocations. *)
Definition audit_idf_queue_event_external {V B} (weight : B -> nat) (event : audit_idf_queue_event
  V B) : nat :=
  match event with
  | IdfQueueMap (AuditMapGet _ _ _ _ body _)
  | IdfQueueMap (AuditMapSet _ _ _ _ _ body _)
  | IdfQueueMap (AuditMapRemove _ _ _ _ body _)
  | IdfQueueSet (AuditSetMem _ _ _ _ body _)
  | IdfQueueSet (AuditSetAdd _ _ _ _ body _)
  | IdfQueueSet (AuditSetRemove _ _ _ _ body _) =>
      fold_right (fun x n => weight x + n) 0 body
  | IdfQueuePush call => audit_idf_queue_push_external weight call
  | _ => 0
  end.

(** Trace composition charges all source events of this execution. *)
Definition audit_idf_queue_source_work {V B} (weight : B -> nat) (events : list
  (audit_idf_queue_event V B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_idf_queue_event_work weight event + n) 0 events.

(** External cost sums the same execution's supplied callback bodies. *)
Definition audit_idf_queue_source_external {V B} (weight : B -> nat)
    (events : list (audit_idf_queue_event V B)) : nat :=
  fold_right (fun event n => audit_idf_queue_event_external weight event + n) 0 events.

(** The seed bound uses original queue structure, levels, key widths and definition occurrences. *)
Definition audit_idf_queue_seed_budget {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) (q : PQueue.t V) : nat :=
  let rows := Map.elements levels in
  let width := fold_right Nat.max (Pos.size_nat ceiling)
    (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row))) (Pos.size_nat (snd row))) rows) in
  let size := audit_queue_input_scale (PQueue.pending_count q) (PQueue.pending q) in
  let qwidth := audit_queue_input_width EV (PQueue.pending q) (PQueue.live q) defs [ceiling] in
  (1024 * 1024)%nat * Nat.pow (S (size + width + qwidth + length defs + length rows)) 12.

(** The emission bound adds actual counter width to the seed bound. *)
Definition audit_idf_queue_emit_budget {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (st : IdfState.t V) (v : V) : nat :=
  let width :=
    match IdfState.output_count st with
    | N0 => 0
    | Npos p => Pos.size_nat p
    end in
  audit_idf_queue_seed_budget EV ceiling levels [v] (IdfState.pending st) + 4096 * S width * S
    width.

(** Both operations have input-derived bounds plus bodies of their actual callback calls. *)
Definition audit_idf_queue_source_bound_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) ceiling levels defs q st v (weight :
    B -> nat),
    (forall key, fst (enc key) = encode EV key) ->
    let seed_events := snd (audit_idf_queue_seeds enc ceiling levels defs q) in
    let emit_events := snd (audit_idf_queue_emit enc ceiling levels st v) in
    audit_idf_queue_source_work weight seed_events <= audit_idf_queue_seed_budget EV ceiling
      levels defs q +
      audit_idf_queue_source_external weight seed_events /\
    audit_idf_queue_source_work weight emit_events <= audit_idf_queue_emit_budget EV ceiling
      levels st v +
      audit_idf_queue_source_external weight emit_events.

(** Queue callbacks expose the key from the same captured event. *)
Definition audit_idf_queue_push_budget {V B} (encode_budget : V -> nat)
    (call : audit_queue_nested_event V (positive * list B)) : nat :=
  match fst call with
  | QGet v _
  | QSet v _ _
  | QRemove v _
  | QEncode v => encode_budget v
  | _ => 0
  end.

(** Every encoder budget is applied to the actual key of the recorded call. *)
Definition audit_idf_queue_event_budget {V B} (encode_budget : V -> nat) (event :
  audit_idf_queue_event V B) : nat :=
  match event with
  | IdfQueueMap (AuditMapGet v _ _ _ _ _)
  | IdfQueueMap (AuditMapSet v _ _ _ _ _ _)
  | IdfQueueMap (AuditMapRemove v _ _ _ _ _)
  | IdfQueueSet (AuditSetMem v _ _ _ _ _)
  | IdfQueueSet (AuditSetAdd v _ _ _ _ _)
  | IdfQueueSet (AuditSetRemove v _ _ _ _ _) =>
      encode_budget v
  | IdfQueuePush call => audit_idf_queue_push_budget encode_budget call
  | _ => 0
  end.

(** Seed and emission costs use source-and-budget laws for each actual encoder call. *)
Definition audit_idf_queue_source_adapted_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) ceiling levels defs q st v (weight :
    B -> nat)
    encode_source encode_budget,
    (forall key, fst (enc key) = encode EV key) ->
    audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
    let seed_events := snd (audit_idf_queue_seeds enc ceiling levels defs q) in
    let emit_events := snd (audit_idf_queue_emit enc ceiling levels st v) in
    audit_idf_queue_source_work weight seed_events <= audit_idf_queue_seed_budget EV ceiling
      levels defs q +
      fold_right (fun event n => audit_idf_queue_event_budget encode_budget event + n) 0
        seed_events /\
    audit_idf_queue_source_work weight emit_events <= audit_idf_queue_emit_budget EV ceiling
      levels st v +
      fold_right (fun event n => audit_idf_queue_event_budget encode_budget event + n) 0
        emit_events.

(** The component contract includes all fixed primitive and queue source obligations. *)
Definition audit_idf_queue_source_contract_statement : Prop :=
  audit_idf_queue_source_erasure_statement /\ audit_idf_queue_source_bound_statement /\
  audit_idf_queue_source_adapted_statement /\ audit_idf_sub_source_statement /\
  audit_queue_full_source_contract_statement.

(** Events retain actual forest setup, DFS and level-index primitive calls. *)
Inductive audit_idf_prepare_event (V E B : Type) : Type :=
  | IdfPrepareDom : audit_dom_source_event V E B -> audit_idf_prepare_event V E B
  | IdfPrepareDfs : audit_dfs_nested_event V V (audit_graph_callback_capture V V
    (audit_dom_source_body V B)) ->
      audit_idf_prepare_event V E B
  | IdfPrepareParent : audit_map_event V V B -> audit_idf_prepare_event V E B
  | IdfPrepareLevel : audit_map_event V positive B -> audit_idf_prepare_event V E B
  | IdfPrepareSucc : audit_nat_encoding_event -> audit_idf_prepare_event V E B
  | IdfPrepareOutput : nat -> audit_idf_prepare_event V E B
  | IdfPrepareCase : nat -> audit_idf_prepare_event V E B.
Arguments IdfPrepareDom {V E B} _.
Arguments IdfPrepareDfs {V E B} _.
Arguments IdfPrepareParent {V E B} _.
Arguments IdfPrepareLevel {V E B} _.
Arguments IdfPrepareSucc {V E B} _.
Arguments IdfPrepareOutput {V E B} _.
Arguments IdfPrepareCase {V E B} _.

(** A numbered vertex reads its actual parent and parent's previously computed level. *)
Definition audit_idf_prepare_level_step {V E B} (enc : V -> positive * list B) (parents : Map.t V V)
    (levels : Map.t V positive) (v : V) : Map.t V positive * list (audit_idf_prepare_event V E B) :=
  let '(parent, pe) := audit_map_get enc v parents in
  let '(level, calls) :=
    match parent with
    | None => (1%positive, [IdfPrepareCase 0])
    | Some u => let '(found, reads) := audit_map_get enc u levels in
        let before :=
          match found with
          | None => 1%positive
          | Some x => x
          end in
        let '(next, succ) := audit_positive_succ before in
        (next, IdfPrepareCase 1 :: map IdfPrepareLevel reads ++ map IdfPrepareSucc succ)
    end in
  let '(result, writes) := audit_map_set enc v level levels in
  (result, map IdfPrepareParent pe ++ calls ++ map IdfPrepareLevel writes).

(** The forward level fold preserves actual intermediate maps and ordered occurrences. *)
Fixpoint audit_idf_prepare_levels {V E B} (enc : V -> positive * list B) (parents : Map.t V V)
    (vertices : list V) (levels : Map.t V positive) : Map.t V positive * list
      (audit_idf_prepare_event V E B) :=
  match vertices with
  | [] => (levels, [IdfPrepareCase 2])
  | v :: rest =>
      let '(next, here) := audit_idf_prepare_level_step enc parents levels v in
      let '(result, later) := audit_idf_prepare_levels enc parents rest next in
      (result, IdfPrepareCase 3 :: here ++ later)
  end.

(** The prepared forest and levels are coupled in one dependent receipt. *)
Record audit_idf_prepare_receipt (V E B : Type) (EV : encoding V) : Type := IdfPrepareReceipt {
  audit_idf_prepare_forest : Graph.t V V;
  audit_idf_prepare_index : prepared EV audit_idf_prepare_forest;
  audit_idf_prepare_values : Map.t V positive;
  audit_idf_prepare_events : list (audit_idf_prepare_event V E B)
}.
Arguments IdfPrepareReceipt {V E B EV} _ _ _ _.
Arguments audit_idf_prepare_forest {V E B EV} _.
Arguments audit_idf_prepare_index {V E B EV} _.
Arguments audit_idf_prepare_values {V E B EV} _.
Arguments audit_idf_prepare_events {V E B EV} _.

(** Forest preparation builds the original child index and reuses it for level numbering. *)
Definition audit_idf_prepare_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (cb : audit_dfs_callback_model V E B)
    : audit_idf_prepare_receipt V E B EV :=
  let parents := idom t in
  let '(live, live_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let vertices := preorder live in
  let '(rows, elements) := audit_map_elements parents in
  let '(children, child_events) := audit_dom_source_children (audit_dfs_encode_model cb) rows in
  let '(roots, root_events) := audit_dom_source_roots (audit_dfs_encode_model cb) parents vertices
    in
  let forest := Graph.Make roots vertices (fun v => index_edges EV children v)
    (fun v =>
      match Map.get EV v parents with
      | Some u => u
      | None => v
      end) (fun v => v) in
  let prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out (audit_dfs_encode_model cb) children) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb)) in
  let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb)) in
  let '(index, prepare_events) := audit_prepare_source_counted EV forest prepare_cb in
  let '(search, search_events) := audit_dfs_source_counted index dfs_cb FinSet.empty roots in
  let order := rev_append (postorder search) [] in
  let '(levels, level_events) := audit_idf_prepare_levels (E := E) (audit_dfs_encode_model cb)
    parents order Map.empty in
  IdfPrepareReceipt forest index levels
    (map (fun x => IdfPrepareDom (DomSourceInitialDfs x)) live_events ++
     map (fun x => IdfPrepareDom (DomSourceElements x)) elements ++ map IdfPrepareDom child_events
       ++
     map IdfPrepareDom root_events ++ map (fun x => IdfPrepareDom (DomSourcePrepare x))
       prepare_events ++
     map IdfPrepareDfs search_events ++ [IdfPrepareOutput (length (postorder search))] ++
       level_events).

(** The forest and computed levels agree with the exact direct-IDF preparation. *)
Definition audit_idf_prepare_source_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_dfs_callback_model V E B),
    audit_dfs_callbacks_erase EV g cb ->
    let receipt := audit_idf_prepare_source_counted p t cb in
    audit_idf_prepare_forest receipt = dom_forest p (idom t) /\
    audit_idf_prepare_values receipt =
      idf_levels EV (idom t) (dom_forest p (idom t)) (prepare EV (dom_forest p (idom t))).

(** The actual forest-index receipt agrees after transporting along the forest equality. *)
Definition audit_idf_prepare_index_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_dfs_callback_model V E B),
    audit_dfs_callbacks_erase EV g cb ->
    let receipt := audit_idf_prepare_source_counted p t cb in
    exists Hforest : audit_idf_prepare_forest receipt = dom_forest p (idom t),
      eq_rect _ (prepared EV) (audit_idf_prepare_index receipt) _ Hforest =
        prepare EV (dom_forest p (idom t)).

(** Work prices the actual setup, DFS, map and successor source calls. *)
Definition audit_idf_prepare_event_work {V E B} (weight : B -> nat) (event :
  audit_idf_prepare_event V E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 +
  match event with
  | IdfPrepareDom call => audit_dom_source_event_work weight call
  | IdfPrepareDfs call => audit_dfs_source_event_work (audit_dom_source_body_work weight) call
  | IdfPrepareParent call => audit_map_source_work body [call]
  | IdfPrepareLevel call => audit_map_source_work body [call]
  | IdfPrepareSucc _ => 4
  | IdfPrepareOutput n => audit_graph_reverse_fast_work n
  | IdfPrepareCase _ => 0
  end.

(** External bodies are drawn only from actual encoder and target calls. *)
Definition audit_idf_prepare_event_external {V E B} (weight : B -> nat)
    (event : audit_idf_prepare_event V E B) : nat :=
  match event with
  | IdfPrepareDom call => audit_dom_source_event_external weight call
  | IdfPrepareDfs call => audit_dfs_source_body_work (audit_dom_source_body_external weight) [call]
  | IdfPrepareParent (AuditMapGet _ _ _ _ body _)
  | IdfPrepareParent (AuditMapSet _ _ _ _ _ body
    _) |
    IdfPrepareParent (AuditMapRemove _ _ _ _ body _) | IdfPrepareLevel (AuditMapGet _ _ _ _ body
      _) |
    IdfPrepareLevel (AuditMapSet _ _ _ _ _ body _) | IdfPrepareLevel (AuditMapRemove _ _ _ _ body
      _) =>
      fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Source work includes trace and output-list composition. *)
Definition audit_idf_prepare_source_work {V E B} (weight : B -> nat) (events : list
  (audit_idf_prepare_event V E B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_idf_prepare_event_work weight event + n) 0 events.

(** Sum the actual external callback bodies in the same receipt. *)
Definition audit_idf_prepare_source_external {V E B} (weight : B -> nat)
    (events : list (audit_idf_prepare_event V E B)) : nat :=
  fold_right (fun event n => audit_idf_prepare_event_external weight event + n) 0 events.

(** The bound uses only graph, prepared-index and supplied parent-map dimensions. *)
Definition audit_idf_prepare_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let rows := Map.elements (idom t) in
  let width := fold_right Nat.max 0 (map (fun row =>
    Nat.max (Pos.size_nat (encode EV (fst row))) (Pos.size_nat (encode EV (snd row)))) rows) in
  let scale := S (length rows + width + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)) in
  (1024 * 1024)%nat * Nat.pow scale 48.

(** The actual preparation receipt has bounded work and coupled output erasure. *)
Definition audit_idf_prepare_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let receipt := audit_idf_prepare_source_counted p t cb in
    audit_idf_prepare_forest receipt = dom_forest p (idom t) /\
    audit_idf_prepare_values receipt =
      idf_levels EV (idom t) (dom_forest p (idom t)) (prepare EV (dom_forest p (idom t))) /\
    audit_idf_prepare_source_work weight (audit_idf_prepare_events receipt) <=
      audit_idf_prepare_source_budget EV g p t +
      audit_idf_prepare_source_external weight (audit_idf_prepare_events receipt).

(** An internal forest callback prices its captured original encoder input. *)
Definition audit_idf_prepare_body_budget {V B} (encode_budget : V -> nat) (event :
  audit_dom_source_body V B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet v _ _ _ _ _)
  | DomSourceBodyMap (AuditMapSet v _ _ _ _ _ _)
  | DomSourceBodyMap (AuditMapRemove v _ _ _ _ _)
  | DomSourceBodyEncode v _ _ => encode_budget v
  | DomSourceBodyTarget _ => 0
  end.

(** The forest setup event prices only actual captured client callbacks. *)
Definition audit_idf_prepare_dom_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_dom_source_event V E B) : nat :=
  match event with
  | DomSourceInitialDfs (_, calls) =>
      fold_right (fun call n => audit_idf_capture_budget encode_budget target_budget call + n) 0
        calls
  | DomSourceChild (AuditMapGet v _ _ _ _ _)
  | DomSourceChild (AuditMapSet v _ _ _ _ _ _)
  | DomSourceChild (AuditMapRemove v _ _ _ _ _)
  | DomSourceParent (AuditMapGet v _ _ _ _ _)
  | DomSourceParent (AuditMapSet v _ _ _ _ _ _)
  | DomSourceParent (AuditMapRemove v _ _ _ _ _) =>
      encode_budget v
  | DomSourcePrepare call => audit_prepare_source_body_work (audit_idf_prepare_body_budget
    encode_budget) [call]
  | DomSourceDfs call => audit_dfs_source_body_work (audit_idf_prepare_body_budget encode_budget)
    [call]
  | _ => 0
  end.

(** Every preparation event prices the original client input of its captured call. *)
Definition audit_idf_prepare_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_idf_prepare_event V E B) : nat :=
  match event with
  | IdfPrepareDom call => audit_idf_prepare_dom_budget encode_budget target_budget call
  | IdfPrepareDfs call => audit_dfs_source_body_work (audit_idf_prepare_body_budget encode_budget)
    [call]
  | IdfPrepareParent (AuditMapGet v _ _ _ _ _)
  | IdfPrepareParent (AuditMapSet v _ _ _ _ _ _)
  | IdfPrepareParent (AuditMapRemove v _ _ _ _ _)
  | IdfPrepareLevel (AuditMapGet v _ _ _ _ _)
  | IdfPrepareLevel (AuditMapSet v _ _ _ _ _ _)
  | IdfPrepareLevel (AuditMapRemove v _ _ _ _ _) =>
      encode_budget v
  | _ => 0
  end.

(** The adapted bound uses the same actual preparation receipt and per-call client budgets. *)
Definition audit_idf_prepare_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    let receipt := audit_idf_prepare_source_counted p t cb in
    audit_idf_prepare_source_work weight (audit_idf_prepare_events receipt) <=
      audit_idf_prepare_source_budget EV g p t +
      fold_right (fun event n => audit_idf_prepare_event_budget encode_budget target_budget event
        + n) 0
        (audit_idf_prepare_events receipt).

(** This component contract includes the dependent index and level agreements. *)
Definition audit_idf_prepare_source_contract_statement : Prop :=
  audit_idf_prepare_source_erasure_statement /\ audit_idf_prepare_index_erasure_statement /\
  audit_idf_prepare_source_statement /\ audit_idf_prepare_source_adapted_statement.

(** Events carry the exact nested source operations and actual intermediate states. *)
Inductive audit_idf_full_event (V E B : Type) : Type :=
  | IdfFullCase : nat -> audit_idf_full_event V E B
  | IdfFullPrepare : audit_idf_prepare_event V E B -> audit_idf_full_event V E B
  | IdfFullQueue : audit_idf_queue_event V B -> audit_idf_full_event V E B
  | IdfFullPop : audit_queue_nested_event V (positive * list B) -> audit_idf_full_event V E B
  | IdfFullDfs : audit_dfs_nested_event V V (audit_graph_callback_capture V V
    (audit_dom_source_body V B)) ->
      audit_idf_full_event V E B
  | IdfFullCollect : audit_idf_collect_source_event V E B -> audit_idf_full_event V E B
  | IdfFullSet : audit_set_event V B -> audit_idf_full_event V E B
  | IdfFullAdd : audit_idf_nadd_event -> audit_idf_full_event V E B
  | IdfFullEmpty : PQueue.t V -> bool -> audit_idf_full_event V E B
  | IdfFullFuel : nat -> positive -> audit_idf_full_event V E B.
Arguments IdfFullCase {V E B} _.
Arguments IdfFullPrepare {V E B} _.
Arguments IdfFullQueue {V E B} _.
Arguments IdfFullPop {V E B} _.
Arguments IdfFullDfs {V E B} _.
Arguments IdfFullCollect {V E B} _.
Arguments IdfFullSet {V E B} _.
Arguments IdfFullAdd {V E B} _.
Arguments IdfFullEmpty {V E B} _ _.
Arguments IdfFullFuel {V E B} _ _.

(** Set insertion processes every freshly reached vertex in order. *)
Fixpoint audit_idf_full_scan {V E B} (enc : V -> positive * list B) (vertices : list V) (set :
  FinSet.t V)
    : FinSet.t V * list (audit_idf_full_event V E B) :=
  match vertices with
  | [] => (set, [IdfFullCase 0])
  | v :: rest =>
      let '(next, calls) := audit_finset_add enc v set in
      let '(result, events) := audit_idf_full_scan enc rest next in
      (result, IdfFullCase 1 :: map IdfFullSet calls ++ events)
  end.

(** Emission folds the actual priority, set and queue source operation over all collected targets.
  *)
Fixpoint audit_idf_full_emit {V E B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (vertices : list V) (state : IdfState.t V)
    : IdfState.t V * list (audit_idf_full_event V E B) :=
  match vertices with
  | [] => (state, [IdfFullCase 2])
  | v :: rest =>
      let '(next, calls) := audit_idf_queue_emit enc ceiling levels state v in
      let '(result, events) := audit_idf_full_emit enc ceiling levels rest next in
      (result, IdfFullCase 3 :: map IdfFullQueue calls ++ events)
  end.

(** A pop executes the actual fresh-subtree DFS, collection, scans and emissions. *)
Definition audit_idf_full_step {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V) (index : prepared EV forest)
    (levels : Map.t V positive) (enc : V -> positive * list B) (target : E -> V * list B)
    (live : V -> bool * list B) (state : IdfState.t V) : IdfState.t V * list (audit_idf_full_event
      V E B) :=
  let '(popped, pop_calls) := audit_queue_recorded_pop enc (IdfState.pending state) in
  match popped with
  | None => (state, map IdfFullPop pop_calls ++ [IdfFullCase 4])
  | Some (_, root, rest) =>
      let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
        (audit_dom_source_encode enc) in
      let '(search, dfs_calls) := audit_dfs_source_counted index dfs_cb (IdfState.scanned state)
        [root] in
      let fresh := preorder search in
      let '(collected, collect_calls) := audit_idf_collect_source_nodes p enc target live t root
        fresh ([], 0%N) in
      let '(scanned, scan_calls) := audit_idf_full_scan enc fresh (IdfState.scanned state) in
      let '(processed, process_calls) := audit_finset_add enc root (IdfState.processed state) in
      let '(visits, add_calls) := audit_idf_nadd_counted (IdfState.edge_visits state) (snd
        collected) in
      let started := IdfState.Make rest (IdfState.emitted state) scanned processed
        (root :: IdfState.trace state) visits (IdfState.output_count state) in
      let '(result, emit_calls) := audit_idf_full_emit enc (fuel p) levels (fst collected) started
        in
      (result, map IdfFullPop pop_calls ++ [IdfFullCase 5] ++ map IdfFullDfs dfs_calls ++
        map IdfFullCollect collect_calls ++ scan_calls ++ map IdfFullSet process_calls ++
        map IdfFullAdd add_calls ++ emit_calls)
  end.

(** Binary iteration tests the actual queue before each recursive call. *)
Fixpoint audit_idf_full_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V) (index : prepared EV forest)
    (levels : Map.t V positive) (enc : V -> positive * list B) (target : E -> V * list B)
    (live : V -> bool * list B) (fuel : positive) (state : IdfState.t V)
    : IdfState.t V * list (audit_idf_full_event V E B) :=
  let empty := PQueue.is_empty (IdfState.pending state) in
  if empty then (state, [IdfFullEmpty (IdfState.pending state) true; IdfFullCase 6]) else
    match fuel with
    | xH => let '(result, events) := audit_idf_full_step p t forest index levels enc target live
      state in
        (result, IdfFullEmpty (IdfState.pending state) false :: IdfFullCase 7 :: events)
    | xO half =>
        let '(middle, first) := audit_idf_full_run p t forest index levels enc target live half
          state in
        let '(result, later) := audit_idf_full_run p t forest index levels enc target live half
          middle in
        (result, IdfFullEmpty (IdfState.pending state) false :: IdfFullCase 8 :: first ++ later)
    | xI half =>
        let '(middle, first) := audit_idf_full_run p t forest index levels enc target live half
          state in
        let '(last, later) := audit_idf_full_run p t forest index levels enc target live half
          middle in
        let '(result, calls) := audit_idf_full_step p t forest index levels enc target live last in
        (result, IdfFullEmpty (IdfState.pending state) false :: IdfFullCase 9 :: first ++ later ++
          calls)
    end.

(** The whole direct producer shares one preparation receipt with its actual worklist run. *)
Definition audit_idf_full_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) (cb : audit_dfs_callback_model V E B)
    (live : V -> bool * list B) : FinSet.t V * list (audit_idf_full_event V E B) :=
  let receipt := audit_idf_prepare_source_counted p t cb in
  let forest := audit_idf_prepare_forest receipt in let index := audit_idf_prepare_index receipt in
  let levels := audit_idf_prepare_values receipt in let enc := audit_dfs_encode_model cb in
  let '(pending, seed_calls) := audit_idf_queue_seeds enc (fuel p) levels defs PQueue.empty in
  let initial := IdfState.Make pending FinSet.empty FinSet.empty FinSet.empty [] 0%N 0%N in
  let run_fuel := Pos.of_succ_nat (length (Graph.nodes g)) in
  let '(result, run_calls) := audit_idf_full_run p t forest index levels enc
    (audit_dfs_target_model cb)
    live run_fuel initial in
  (IdfState.emitted result, map IdfFullPrepare (audit_idf_prepare_events receipt) ++ map
    IdfFullQueue seed_calls ++
    [IdfFullFuel (length (Graph.nodes g)) run_fuel] ++ run_calls).

(** The actual same-run producer erases to the direct pruned IDF result. *)
Definition audit_idf_full_source_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (live : V -> bool * list B) (live_value : V -> bool),
    audit_dfs_callbacks_erase EV g cb -> (forall v, fst (live v) = live_value v) ->
    fst (audit_idf_full_source_counted p t defs cb live) = direct_pruned_idf p t defs live_value.

(** Source work prices every concrete nested primitive and captured callback body. *)
Definition audit_idf_full_event_work {V E B} (weight : B -> nat) (event : audit_idf_full_event V E
  B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 +
  match event with
  | IdfFullPrepare call => audit_idf_prepare_event_work weight call
  | IdfFullQueue call => audit_idf_queue_event_work weight call
  | IdfFullPop call => audit_queue_recorded_full_source_work weight [call]
  | IdfFullDfs call => audit_dfs_source_event_work (audit_dom_source_body_work weight) call
  | IdfFullCollect call => audit_idf_collect_source_event_work weight call
  | IdfFullSet call => audit_finset_source_work body [call]
  | IdfFullAdd _ => 16
  | IdfFullFuel n _ => 64 * S n * S n
  | IdfFullEmpty _ _
  | IdfFullCase _ => 0
  end.

(** External work contains only actual supplied encoder, target and live callback bodies. *)
Definition audit_idf_full_event_external {V E B} (weight : B -> nat)
    (event : audit_idf_full_event V E B) : nat :=
  match event with
  | IdfFullPrepare call => audit_idf_prepare_event_external weight call
  | IdfFullQueue call => audit_idf_queue_event_external weight call
  | IdfFullPop call => audit_idf_queue_push_external weight call
  | IdfFullDfs call => audit_dfs_source_body_work (audit_dom_source_body_external weight) [call]
  | IdfFullCollect call => audit_idf_collect_source_event_external weight call
  | IdfFullSet (AuditSetMem _ _ _ _ body _)
  | IdfFullSet (AuditSetAdd _ _ _ _ body _)
  | IdfFullSet (AuditSetRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Whole-source work charges nested frames and source trace-list concatenation. *)
Definition audit_idf_full_source_work {V E B} (weight : B -> nat) (events : list
  (audit_idf_full_event V E B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event n => audit_idf_full_event_work weight event + n) 0 events.

(** The callback charge sums bodies from the same source run. *)
Definition audit_idf_full_source_external {V E B} (weight : B -> nat)
    (events : list (audit_idf_full_event V E B)) : nat :=
  fold_right (fun event n => audit_idf_full_event_external weight event + n) 0 events.

(** The scale uses only original graph, prepared index, tree and definition inputs. *)
Definition audit_idf_full_input_scale {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  let out_rows := Map.elements (out_index p) in
  let edges := flat_map snd out_rows in
  let parents := Map.elements (idom t) in
  let tins := Map.elements (tin t) in let touts := Map.elements (tout t) in
  let vertices := defs ++ Graph.nodes g ++ Graph.entries g ++ map fst out_rows ++
    map (Graph.target g) edges ++ map fst parents ++ map snd parents ++ map fst tins ++ map fst
      touts in
  let vertex_width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices) in
  let rank_width := fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (tins ++ touts))
    in
  S (length vertices + length edges + length parents + vertex_width + rank_width +
    Pos.to_nat (fuel p) + audit_idf_prepare_source_budget EV g p t).

(** The complete bound does not depend on returned work or callback events. *)
Definition audit_idf_full_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  (1024 * 1024)%nat * Nat.pow (audit_idf_full_input_scale EV g p t defs) 128.

(** The pruned producer has the exact result and an original-input source-work bound. *)
Definition audit_idf_full_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (live : V -> bool * list B) (live_value : V -> bool)
      (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb -> (forall v, fst (live v) = live_value v) ->
    let '(result, events) := audit_idf_full_source_counted p t defs cb live in
    result = direct_pruned_idf p t defs live_value /\ audit_idf_full_source_work weight events <=
      audit_idf_full_input_budget EV g p t defs + audit_idf_full_source_external weight events.

(** The unpruned producer fixes its internal live predicate and has the same bound. *)
Definition audit_idf_full_unpruned_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_idf_full_source_counted p t defs cb (fun _ => (true, [])) in
    result = direct_idf p t defs /\ audit_idf_full_source_work weight events <=
      audit_idf_full_input_budget EV g p t defs + audit_idf_full_source_external weight events.

(** Each event prices its actual client input, including nested forest callbacks. *)
Definition audit_idf_full_event_budget {V E B} (encode_budget live_budget : V -> nat)
  (target_budget : E -> nat)
    (event : audit_idf_full_event V E B) : nat :=
  match event with
  | IdfFullPrepare call => audit_idf_prepare_event_budget encode_budget target_budget call
  | IdfFullQueue call => audit_idf_queue_event_budget encode_budget call
  | IdfFullPop call => audit_idf_queue_push_budget encode_budget call
  | IdfFullDfs call => audit_dfs_source_body_work (audit_idf_prepare_body_budget encode_budget)
    [call]
  | IdfFullCollect call => audit_idf_collect_source_event_budget encode_budget live_budget
    target_budget call
  | IdfFullSet (AuditSetMem v _ _ _ _ _)
  | IdfFullSet (AuditSetAdd v _ _ _ _ _)
  | IdfFullSet (AuditSetRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

(** The pruned source bound applies each law to actual recorded callback invocations. *)
Definition audit_idf_full_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (live : V -> bool * list B) (live_value : V -> bool)
      (weight : B -> nat)
    encode_source target_source live_source encode_budget target_budget live_budget,
    audit_dfs_callbacks_erase EV g cb -> (forall v, fst (live v) = live_value v) ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter live weight live_source live_budget ->
    let '(result, events) := audit_idf_full_source_counted p t defs cb live in
    result = direct_pruned_idf p t defs live_value /\ audit_idf_full_source_work weight events <=
      audit_idf_full_input_budget EV g p t defs +
      fold_right (fun event n => audit_idf_full_event_budget encode_budget live_budget
        target_budget event + n) 0 events.

(** The unpruned source bound has no external live-predicate assumption or charge. *)
Definition audit_idf_full_unpruned_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) encode_source target_source
      encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    let '(result, events) := audit_idf_full_source_counted p t defs cb (fun _ => (true, [])) in
    result = direct_idf p t defs /\ audit_idf_full_source_work weight events <=
      audit_idf_full_input_budget EV g p t defs +
      fold_right (fun event n => audit_idf_full_event_budget encode_budget (fun _ => 0)
        target_budget event + n) 0 events.

(** The complete direct-IDF source contract includes each actual producer and primitive boundary. *)
Definition audit_idf_full_source_contract_statement : Prop :=
  audit_idf_full_source_erasure_statement /\ audit_idf_full_source_statement /\
  audit_idf_full_unpruned_source_statement /\ audit_idf_full_source_adapted_statement /\
  audit_idf_full_unpruned_adapted_statement /\ audit_idf_prepare_source_contract_statement /\
  audit_idf_queue_source_contract_statement /\ audit_idf_collect_source_contract_statement /\
  audit_idf_nadd_source_statement /\ audit_idf_sub_source_statement /\
    audit_queue_full_source_contract_statement.
