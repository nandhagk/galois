(** * Selectable dominator source contracts

    The selector records one virtual search, the chosen backend, checks and fallback.
    For example, a missing interval stops the checker before later map reads.
    Builds on: dominator, semidominator, Semi-NCA and collection source models. *)

From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap
    CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditPrimitive
      CollectionsAuditCompare CollectionsAuditUnion CollectionsAuditMapTraverse
        CollectionsAuditEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphDominance
  GraphDominators GraphSemiDominators GraphSemiNca GraphAuditBase GraphAuditDfs GraphAuditScc
    GraphAuditVirtual GraphAuditSemiDominators GraphAuditLengauerTarjan GraphAuditSemiNca
      GraphAuditDominators.
Import List.ListNotations.

Record audit_nca_backend_trace (V E : Type) : Type := AuditNcaBackendTrace {
  audit_nca_backend_prepare : list (audit_prepare_nested_event (V + unit) (E + V)
    (audit_virtual_call V E));
  audit_nca_backend_dfs : list (audit_dfs_nested_event (V + unit) (E + V) (audit_virtual_call V E));
  audit_nca_backend_semi : list (audit_semi_outer_call (V + unit) (E + V));
  audit_nca_backend_core : list (audit_nca_call (V + unit) (E + V));
  audit_nca_backend_erase : list (audit_erase_call V)
}.
Arguments AuditNcaBackendTrace {V E} _ _ _ _ _.
Arguments audit_nca_backend_prepare {V E} _.
Arguments audit_nca_backend_dfs {V E} _.
Arguments audit_nca_backend_semi {V E} _.
Arguments audit_nca_backend_core {V E} _.
Arguments audit_nca_backend_erase {V E} _.

(** An NCA backend run connects virtual search, semidominators, NCA and erasure. *)
Definition audit_nca_backend_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (result : Map.t V V) (trace : audit_nca_backend_trace V E) : Prop :=
  let '(vp, (r, (prepare_events, dfs_events))) := audit_virtual_search_with_prepared EV g in
  exists state semi_events virtual_parents nca_events,
    audit_semi_compute_run vp r state semi_events /\
    audit_nca_compute_run (virtual_encoding EV) (virtual_graph EV g) r (SemiState.result state)
      virtual_parents nca_events /\
    let '(output, erase_events) := audit_erase_virtual_counted EV virtual_parents in
    result = output /\ trace = AuditNcaBackendTrace prepare_events dfs_events semi_events
      nca_events erase_events.

Definition audit_nca_backend_selected_work {V E} (EV : encoding V) (trace :
  audit_nca_backend_trace V E) : nat :=
  audit_graph_prepare_nested_total_work (audit_virtual_event_work EV) (audit_nca_backend_prepare
    trace) +
  audit_dfs_nested_total_work (virtual_encoding EV) (audit_virtual_event_work EV)
    (audit_nca_backend_dfs trace) +
  audit_semi_compute_work (virtual_encoding EV) (audit_nca_backend_semi trace) +
  audit_nca_compute_work (virtual_encoding EV) (audit_nca_backend_core trace) +
  audit_erase_virtual_work EV (audit_nca_backend_erase trace).

(** The NCA backend admits a run yielding the original immediate dominators. *)
Definition audit_nca_backend_erasure_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    exists result trace, audit_nca_backend_run p result trace /\ result = semi_nca_idom p.

Inductive audit_dom_backend_trace (V E : Type) : Type :=
  | AuditDomLtTrace (backend : audit_lt_backend_trace V E) (tree : list (audit_dom_call V E))
  | AuditDomNcaTrace (backend : audit_nca_backend_trace V E) (tree : list (audit_dom_call V E)).
Arguments AuditDomLtTrace {V E} _ _.
Arguments AuditDomNcaTrace {V E} _ _.

Inductive audit_dom_tree_with_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : dom_algorithm -> dom_tree V -> audit_dom_backend_trace V E -> Prop :=
  | AuditDomWithLt parents backend tree tree_events :
    audit_lt_backend_run p parents backend -> audit_dom_tree_counted p parents = (tree,
      tree_events) ->
    audit_dom_tree_with_run p SimpleLT tree (AuditDomLtTrace backend tree_events)
  | AuditDomWithNca parents backend tree tree_events :
    audit_nca_backend_run p parents backend -> audit_dom_tree_counted p parents = (tree,
      tree_events) ->
    audit_dom_tree_with_run p SemiNCA tree (AuditDomNcaTrace backend tree_events).

(** Each selectable dominator backend admits a run yielding its tree. *)
Definition audit_dom_tree_with_erasure_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) algorithm,
    exists result trace, audit_dom_tree_with_run p algorithm result trace /\
      result = dominator_tree_with p algorithm.

(** The default dominator backend admits a run yielding its tree. *)
Definition audit_dom_tree_default_erasure_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    exists result trace, audit_dom_tree_with_run p SimpleLT result trace /\ result =
      dominator_tree p.

(** A comparison retains both encoder calls and the positive equality trace. *)
Inductive audit_flat_source_event (V E B : Type) : Type :=
  | FlatSourceCase : nat -> audit_flat_source_event V E B
  | FlatSourceCompare : V -> V -> positive -> positive -> list B -> list B -> bool ->
      list audit_positive_eqb_event -> audit_flat_source_event V E B
  | FlatSourceDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
      audit_flat_source_event V E B
  | FlatSourceMap : audit_map_event V V B -> audit_flat_source_event V E B.
Arguments FlatSourceCase {V E B} _.
Arguments FlatSourceCompare {V E B} _ _ _ _ _ _ _ _.
Arguments FlatSourceDfs {V E B} _.
Arguments FlatSourceMap {V E B} _.

(** The comparison evaluates both actual encoding calls before equality. *)
Definition audit_flat_source_compare {V E B} (enc : V -> positive * list B) (v s : V)
    : bool * list (audit_flat_source_event V E B) :=
  let '(a, ea) := enc v in
  let '(b, eb) := enc s in
  let '(same, trace) := audit_positive_eqb a b in
  (same, [FlatSourceCompare v s a b ea eb same trace]).

(** The strict entry scan evaluates every occurrence, including after a false result. *)
Fixpoint audit_flat_source_entries {V E B} (enc : V -> positive * list B)
    (s : V) (entries : list V) : bool * list (audit_flat_source_event V E B) :=
  match entries with
  | [] => (true, [FlatSourceCase 0])
  | v :: rest =>
      let '(same, here) := audit_flat_source_compare enc v s in
      let '(later, events) := audit_flat_source_entries enc s rest in
      (same && later, FlatSourceCase 1 :: here ++ events)
  end.

(** The forward fold retains the actual intermediate map at every node. *)
Fixpoint audit_flat_source_fold {V E B} (enc : V -> positive * list B) (s : V)
    (vertices : list V) (parents : Map.t V V) : Map.t V V * list (audit_flat_source_event V E B) :=
  match vertices with
  | [] => (parents, [FlatSourceCase 2])
  | v :: rest =>
      let '(same, compares) := audit_flat_source_compare enc v s in
      let '(next, writes) := if same then (parents, []) else audit_map_set enc v s parents in
      let '(result, events) := audit_flat_source_fold enc s rest next in
      (result, FlatSourceCase 3 :: compares ++ map FlatSourceMap writes ++ events)
  end.

(** The fallback follows the actual empty, rejected, and accepted entry branches. *)
Definition audit_flat_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : Map.t V V * list (audit_flat_source_event V E B) :=
  match Graph.entries g with
  | [] => (Map.empty, [FlatSourceCase 4])
  | s :: rest =>
      let '(same, comparisons) := audit_flat_source_entries (audit_dfs_encode_model cb) s rest in
      if same then
        let '(search, search_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries
          g) in
        let '(result, events) := audit_flat_source_fold (audit_dfs_encode_model cb) s
          (preorder search) Map.empty in
        (result, FlatSourceCase 5 :: comparisons ++ map FlatSourceDfs search_events ++ events)
      else (Map.empty, FlatSourceCase 6 :: comparisons)
  end.

(** Source work includes each primitive and its actual callback bodies. *)
Definition audit_flat_source_event_work {V E B} (weight : B -> nat)
    (event : audit_flat_source_event V E B) : nat :=
  64 +
  match event with
  | FlatSourceCase _ => 0
  | FlatSourceCompare _ _ _ _ ea eb _ calls =>
      fold_right (fun x n => weight x + n) 0 ea +
      fold_right (fun x n => weight x + n) 0 eb + audit_positive_eqb_source_work calls
  | FlatSourceDfs call => audit_dfs_source_event_work weight call
  | FlatSourceMap call => audit_map_source_work (fun es => fold_right (fun x n => weight x + n) 0
    es) [call]
  end.

(** External work counts only recorded client callback bodies. *)
Definition audit_flat_source_event_external {V E B} (weight : B -> nat)
    (event : audit_flat_source_event V E B) : nat :=
  match event with
  | FlatSourceCompare _ _ _ _ ea eb _ _ =>
      fold_right (fun x n => weight x + n) 0 ea + fold_right (fun x n => weight x + n) 0 eb
  | FlatSourceDfs call => audit_dfs_source_body_work weight [call]
  | FlatSourceMap (AuditMapGet _ _ _ _ es _)
  | FlatSourceMap (AuditMapSet _ _ _ _ _ es _)
  | FlatSourceMap (AuditMapRemove _ _ _ _ es _) => fold_right (fun x n => weight x + n) 0 es
  | FlatSourceCase _ => 0
  end.

(** Total work sums the events of this same fallback run. *)
Definition audit_flat_source_work {V E B} (weight : B -> nat)
    (events : list (audit_flat_source_event V E B)) : nat :=
  fold_right (fun event n => audit_flat_source_event_work weight event + n) 0 events.

(** External work sums the bodies attached to this same fallback run. *)
Definition audit_flat_source_external {V E B} (weight : B -> nat)
    (events : list (audit_flat_source_event V E B)) : nat :=
  fold_right (fun event n => audit_flat_source_event_external weight event + n) 0 events.

(** The budget depends on input dimensions and the already defined DFS budget. *)
Definition audit_flat_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let scale := S (length (Graph.entries g) + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)) in
  4096 * Nat.pow scale 8.

(** The fallback returns the actual result with its complete source work bounded. *)
Definition audit_flat_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_flat_source_counted p cb in
    result = flat_idom p /\ audit_flat_source_work weight events <=
      audit_flat_source_budget EV g p + audit_flat_source_external weight events.

(** Events retain each concrete primitive call and each nested traversal. *)
Inductive audit_check_idom_event (V E B : Type) : Type :=
  | CheckIdomCase : nat -> audit_check_idom_event V E B
  | CheckIdomDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
      audit_check_idom_event V E B
  | CheckIdomDom : audit_dom_source_event V E B -> audit_check_idom_event V E B
  | CheckIdomElements : audit_elements_event (V * V) -> audit_check_idom_event V E B
  | CheckIdomSet : audit_set_event V B -> audit_check_idom_event V E B
  | CheckIdomMap : audit_map_event V positive B -> audit_check_idom_event V E B
  | CheckIdomCompare : positive -> positive -> bool -> list audit_positive_compare_event ->
      audit_check_idom_event V E B.
Arguments CheckIdomCase {V E B} _.
Arguments CheckIdomDfs {V E B} _.
Arguments CheckIdomDom {V E B} _.
Arguments CheckIdomElements {V E B} _.
Arguments CheckIdomSet {V E B} _.
Arguments CheckIdomMap {V E B} _.
Arguments CheckIdomCompare {V E B} _ _ _ _.

(** Every binding evaluates all three set membership tests. *)
Fixpoint audit_check_idom_bindings {V E B} (enc : V -> positive * list B)
    (live numbered : FinSet.t V) (rows : list (V * V)) : bool * list (audit_check_idom_event V E
      B) :=
  match rows with
  | [] => (true, [CheckIdomCase 0])
  | (v, u) :: rest =>
      let '(a, ea) := audit_finset_mem enc v live in
      let '(b, eb) := audit_finset_mem enc u live in
      let '(c, ec) := audit_finset_mem enc v numbered in
      let '(later, events) := audit_check_idom_bindings enc live numbered rest in
      ((a && b && c) && later,
        CheckIdomCase 1 :: map CheckIdomSet ea ++ map CheckIdomSet eb ++
          map CheckIdomSet ec ++ events)
  end.

(** Interval lookups stop at the first missing value. *)
Definition audit_check_idom_dominates {V E B} (enc : V -> positive * list B)
    (t : dom_tree V) (d n : V) : bool * list (audit_check_idom_event V E B) :=
  let '(a, ea) := audit_map_get enc d (tin t) in
  match a with
  | None => (false, map CheckIdomMap ea ++ [CheckIdomCase 2])
  | Some aa =>
      let '(b, eb) := audit_map_get enc n (tin t) in
      match b with
      | None => (false, map CheckIdomMap ea ++ map CheckIdomMap eb ++ [CheckIdomCase 2])
      | Some bb =>
          let '(c, ec) := audit_map_get enc d (tout t) in
          match c with
          | None => (false, map CheckIdomMap ea ++ map CheckIdomMap eb ++ map CheckIdomMap ec ++
              [CheckIdomCase 2])
          | Some cc =>
              let '(e, ee) := audit_map_get enc n (tout t) in
              let reads := map CheckIdomMap ea ++ map CheckIdomMap eb ++
                map CheckIdomMap ec ++ map CheckIdomMap ee in
              match e with
              | None => (false, reads ++ [CheckIdomCase 2])
              | Some dd =>
                  let '(lhs, el) := audit_positive_leb aa bb in
                  let '(rhs, er) := audit_positive_leb dd cc in
                  (lhs && rhs, reads ++ [CheckIdomCompare aa bb lhs el; CheckIdomCompare dd cc rhs
                    er])
              end
          end
      end
  end.

(** Every node checks blocked reachability and its interval comparison. *)
Fixpoint audit_check_idom_nodes {V E B} (enc : V -> positive * list B)
    (blocked : FinSet.t V) (t : dom_tree V) (d : V) (vertices : list V)
    : bool * list (audit_check_idom_event V E B) :=
  match vertices with
  | [] => (true, [CheckIdomCase 3])
  | n :: rest =>
      let '(seen, se) := audit_finset_mem enc n blocked in
      let '(dom, de) := audit_check_idom_dominates enc t d n in
      let '(later, events) := audit_check_idom_nodes enc blocked t d rest in
      (Bool.eqb (negb seen) dom && later, CheckIdomCase 4 :: map CheckIdomSet se ++ de ++ events)
  end.

(** Each candidate dominator performs its own blocked DFS and complete node scan. *)
Fixpoint audit_check_idom_candidates {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (t : dom_tree V)
    (all todo : list V) : bool * list (audit_check_idom_event V E B) :=
  match todo with
  | [] => (true, [CheckIdomCase 5])
  | d :: rest =>
      let '(blocked, add_events) := audit_finset_add (audit_dfs_encode_model cb) d FinSet.empty in
      let '(search, dfs_events) := audit_dfs_source_counted p cb blocked (Graph.entries g) in
      let '(ok, checks) := audit_check_idom_nodes (audit_dfs_encode_model cb) (visited search) t d
        all in
      let '(later, events) := audit_check_idom_candidates p cb t all rest in
      (ok && later, CheckIdomCase 6 :: map CheckIdomSet add_events ++
        map CheckIdomDfs dfs_events ++ checks ++ events)
  end.

(** This models the exact checker execution, including all intermediate search results. *)
Definition audit_check_idom_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) (cb : audit_dfs_callback_model V E B)
    : bool * list (audit_check_idom_event V E B) :=
  let '(live, live_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let receipt := audit_dom_search_source_counted p parents cb in
  let search := audit_dom_source_result receipt in
  let t := DomTree parents (pre_num search) (post_num search) in
  let '(rows, elements) := audit_map_elements parents in
  let '(binding_ok, bindings) := audit_check_idom_bindings (audit_dfs_encode_model cb)
    (visited live) (visited search) rows in
  let '(node_ok, nodes) := audit_check_idom_candidates p cb t (preorder live) (preorder live) in
  (binding_ok && node_ok, map CheckIdomDfs live_events ++
    map CheckIdomDom (audit_dom_source_events receipt) ++ map CheckIdomElements elements ++
    bindings ++ nodes).

(** Work charges nested source operations and the bodies attached to their actual calls. *)
Definition audit_check_idom_event_work {V E B} (weight : B -> nat)
    (event : audit_check_idom_event V E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 +
  match event with
  | CheckIdomCase _ => 0
  | CheckIdomDfs call => audit_dfs_source_event_work weight call
  | CheckIdomDom call => audit_dom_source_event_work weight call
  | CheckIdomElements call => audit_elements_frame_work call
  | CheckIdomSet call => audit_finset_source_work body [call]
  | CheckIdomMap call => audit_map_source_work body [call]
  | CheckIdomCompare _ _ _ calls => audit_positive_order_source_work calls
  end.

(** The external charge retains only client bodies from this execution. *)
Definition audit_check_idom_event_external {V E B} (weight : B -> nat)
    (event : audit_check_idom_event V E B) : nat :=
  match event with
  | CheckIdomDfs call => audit_dfs_source_body_work weight [call]
  | CheckIdomDom call => audit_dom_source_event_external weight call
  | CheckIdomSet (AuditSetAdd _ _ _ _ body _)
  | CheckIdomSet (AuditSetMem _ _ _ _ body _)
  | CheckIdomSet (AuditSetRemove _ _ _ _ body _)
  | CheckIdomMap (AuditMapGet _ _ _ _ body _)
  | CheckIdomMap (AuditMapSet _ _ _ _ _ body _)
  | CheckIdomMap (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun x n => weight x + n) 0 body
  | CheckIdomCase _
  | CheckIdomElements _
  | CheckIdomSet (AuditSetFold _ _)
  | CheckIdomCompare _ _ _ _ => 0
  end.

(** The work measure sums the recorded source events. *)
Definition audit_check_idom_source_work {V E B} (weight : B -> nat)
    (events : list (audit_check_idom_event V E B)) : nat :=
  fold_right (fun event n => audit_check_idom_event_work weight event + n) 0 events.

(** The body measure sums the same run's client callback bodies. *)
Definition audit_check_idom_source_external {V E B} (weight : B -> nat)
    (events : list (audit_check_idom_event V E B)) : nat :=
  fold_right (fun event n => audit_check_idom_event_external weight event + n) 0 events.

(** The input scale includes parent keys, values, structure, prepared input and DFS budget. *)
Definition audit_check_idom_input_scale {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  let rows := Map.elements parents in
  let width := fold_right Nat.max 0 (map (fun row =>
    Nat.max (Pos.size_nat (encode EV (fst row))) (Pos.size_nat (encode EV (snd row)))) rows) in
  S (length rows + width + audit_trie_nodes parents + Pos.to_nat (fuel p) +
    length (Graph.entries g) + audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)).

(** The complete checker budget is derived from its input dimensions. *)
Definition audit_check_idom_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  (1024 * 1024)%nat * Nat.pow (audit_check_idom_input_scale EV g p parents) 48.

(** The source model returns the checker result with bounded work. *)
Definition audit_check_idom_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) parents
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_check_idom_source_counted p parents cb in
    result = check_idom p parents /\ audit_check_idom_source_work weight events <=
      audit_check_idom_source_budget EV g p parents + audit_check_idom_source_external weight
        events.

Definition audit_virtual_nca_stage_work {V E B} (weight : B -> nat)
    (events : list (audit_nca_source_event (V + unit) (E + V)
      (audit_virtual_full_call V E B))) : nat :=
  audit_nca_source_work
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event) events.

(** External callback bodies are charged for the same recorded calls. *)
Definition audit_virtual_nca_external_work {V E B} (weight : B -> nat)
    (events : list (audit_nca_source_event (V + unit) (E + V)
      (audit_virtual_full_call V E B))) : nat :=
  audit_nca_source_body_work (audit_virtual_full_body_event_work weight) events.

Definition audit_virtual_nca_input_scale {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++
    map (Graph.target g) edges in
  4 + length (Graph.nodes g) + length (Graph.entries g) + length edges +
    fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices).

(** The whole-producer budget depends only on the original graph and encoder. *)
Definition audit_virtual_nca_input_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  (1024 * 1024)%nat * Nat.pow (audit_virtual_nca_input_scale EV g) 48.

Inductive audit_dom_select_trace (V E B : Type) : Type :=
  | DomSelectLt : list (audit_lt_nested_event (V + unit) (E + V)
      (audit_virtual_full_call V E B)) -> audit_dom_select_trace V E B
  | DomSelectNca : list (audit_nca_source_event (V + unit) (E + V)
      (audit_virtual_full_call V E B)) -> audit_dom_select_trace V E B.
Arguments DomSelectLt {V E B} _.
Arguments DomSelectNca {V E B} _.

Definition audit_dom_select_backend_work {V E B} (weight : B -> nat)
    (events : audit_dom_select_trace V E B) : nat :=
  match events with
  | DomSelectLt calls => audit_virtual_lt_stage_work weight calls
  | DomSelectNca calls => audit_virtual_nca_stage_work weight calls
  end.

(** External work charges the same chosen backend's client bodies. *)
Definition audit_dom_select_backend_external {V E B} (weight : B -> nat)
    (events : audit_dom_select_trace V E B) : nat :=
  match events with
  | DomSelectLt calls => audit_virtual_lt_external_work weight calls
  | DomSelectNca calls => audit_virtual_nca_external_work weight calls
  end.

Definition audit_dom_select_source_budget {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) (receipt : audit_dom_source_receipt V E B EV) : nat :=
  audit_virtual_lt_input_budget EV g + audit_virtual_nca_input_budget EV g +
  audit_dom_search_source_budget EV g p parents receipt.

(** The original-input budget includes the input graph and prepared traversal dimensions. *)
Definition audit_dom_select_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let scale := S (audit_virtual_nca_input_scale EV g + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)) in
  (1024 * 1024)%nat * Nat.pow scale 64.

(** The chosen backend consumes the already captured search and semidominator results. *)
Definition audit_dom_select_single_backend {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (search : dfs_result (V + unit) (E + V)) (semis : Map.t (V + unit) (V + unit))
    (choice : dom_algorithm) (trace : audit_dom_select_trace V E B)
    (parents : Map.t (V + unit) (V + unit)) : Prop :=
  match choice, trace with
  | SimpleLT, DomSelectLt events =>
      audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search semis parents events
  | SemiNCA, DomSelectNca events =>
      audit_nca_source_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search semis parents events
  | _, _ => False
  end.

(** Every bound component reads traces from the same one virtual-search invocation. *)
Definition audit_dom_select_single_run_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) choice
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat),
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents backend_events
      parents erase_events receipt result,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
        source)
        vp search semi_state semi_events /\
      audit_dom_select_single_backend EV g cb source search (SemiState.result semi_state)
        choice backend_events virtual_parents /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
        erase_events) /\
      receipt = audit_dom_search_source_counted p parents
        (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode
          cb)) /\
      result = DomTree parents (pre_num (audit_dom_source_result receipt))
        (post_num (audit_dom_source_result receipt)) /\
      result = dominator_tree_with p choice /\
      let work := audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        prepare_events +
        audit_dfs_source_work
          (fun event => audit_virtual_full_internal_event_work event +
            audit_virtual_full_body_event_work weight event)
          dfs_events + audit_virtual_semi_stage_work weight semi_events +
        audit_dom_select_backend_work weight backend_events + audit_erase_nested_work weight
          erase_events +
        audit_dom_source_work weight (audit_dom_source_events receipt) in
      let external := audit_prepare_source_body_work (audit_virtual_full_body_event_work weight)
        prepare_events +
        audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events +
        audit_virtual_semi_external_work weight semi_events + audit_dom_select_backend_external
          weight backend_events +
        audit_erase_nested_body_work weight erase_events +
        audit_dom_source_external_work weight (audit_dom_source_events receipt) in
      work <= audit_dom_select_source_budget EV g p parents receipt + external /\
      work <= audit_dom_select_input_budget EV g p + external.

(** The NCA backend itself shares one search receipt with all source-work charges. *)
Definition audit_virtual_nca_single_run_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat),
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents nca_events
      parents erase_events,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
        source)
        vp search semi_state semi_events /\
      audit_nca_source_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search (SemiState.result semi_state) virtual_parents nca_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
        erase_events) /\
      parents = semi_nca_idom p /\
      audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        prepare_events + audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events +
          audit_virtual_nca_stage_work weight nca_events +
        audit_erase_nested_work weight erase_events <= audit_virtual_nca_input_budget EV g +
      audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
      audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events +
      audit_virtual_semi_external_work weight semi_events + audit_virtual_nca_external_work weight
        nca_events +
      audit_erase_nested_body_work weight erase_events.

(** A captured DFS call charges the genuine callback at its recorded input. *)
Definition audit_flat_check_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E
  -> nat)
    (calls : list (audit_graph_callback_capture V E B)) : nat :=
  fold_right (fun call n => audit_scc_capture_budget encode_budget target_budget call + n) 0 calls.

(** Every fallback event exposes its actual external callback inputs. *)
Definition audit_flat_source_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_flat_source_event V E B) : nat :=
  match event with
  | FlatSourceCase _ => 0
  | FlatSourceCompare v s _ _ _ _ _ _ => encode_budget v + encode_budget s
  | FlatSourceDfs (_, calls) => audit_flat_check_capture_budget encode_budget target_budget calls
  | FlatSourceMap (AuditMapGet v _ _ _ _ _)
  | FlatSourceMap (AuditMapSet v _ _ _ _ _ _)
  | FlatSourceMap (AuditMapRemove v _ _ _ _ _) => encode_budget v
  end.

(** The fallback has a bound in terms of actual callback budgets. *)
Definition audit_flat_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    let '(result, events) := audit_flat_source_counted p cb in
    result = flat_idom p /\ audit_flat_source_work weight events <= audit_flat_source_budget EV g
      p +
      fold_right (fun event n => audit_flat_source_event_budget encode_budget target_budget event
        + n) 0 events.

(** The complete fallback contract includes its source and adapted work claims. *)
Definition audit_flat_source_contract_statement : Prop :=
  audit_flat_source_statement /\ audit_flat_source_adapted_statement.

(** The internal forest callback charges only its actual captured client encoder calls. *)
Definition audit_dom_source_body_budget {V B} (encode_budget : V -> nat)
    (event : audit_dom_source_body V B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet v _ _ _ _ _)
  | DomSourceBodyMap (AuditMapSet v _ _ _ _ _ _)
  | DomSourceBodyMap (AuditMapRemove v _ _ _ _ _)
  | DomSourceBodyEncode v _ _ => encode_budget v
  | DomSourceBodyTarget _ => 0
  end.

(** Forest search prices its nested calls by their original client inputs. *)
Definition audit_dom_source_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_dom_source_event V E B) : nat :=
  match event with
  | DomSourceInitialDfs (_, calls) => audit_flat_check_capture_budget encode_budget target_budget
    calls
  | DomSourceChild (AuditMapGet v _ _ _ _ _)
  | DomSourceChild (AuditMapSet v _ _ _ _ _ _)
  | DomSourceChild (AuditMapRemove v _ _ _ _ _)
  | DomSourceParent (AuditMapGet v _ _ _ _ _)
  | DomSourceParent (AuditMapSet v _ _ _ _ _ _)
  | DomSourceParent (AuditMapRemove v _ _ _ _ _) =>
      encode_budget v
  | DomSourcePrepare call => audit_prepare_source_body_work (audit_dom_source_body_budget
    encode_budget) [call]
  | DomSourceDfs call => audit_dfs_source_body_work (audit_dom_source_body_budget encode_budget)
    [call]
  | DomSourceCase _
  | DomSourceElements _ => 0
  end.

(** Each checker event exposes the actual external encoder and target inputs. *)
Definition audit_check_idom_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_check_idom_event V E B) : nat :=
  match event with
  | CheckIdomDfs (_, calls) => audit_flat_check_capture_budget encode_budget target_budget calls
  | CheckIdomDom call => audit_dom_source_event_budget encode_budget target_budget call
  | CheckIdomSet (AuditSetAdd v _ _ _ _ _)
  | CheckIdomSet (AuditSetMem v _ _ _ _ _)
  | CheckIdomSet (AuditSetRemove v _ _ _ _ _)
  | CheckIdomMap (AuditMapGet v _ _ _ _ _)
  | CheckIdomMap (AuditMapSet v _ _ _ _ _ _)
  | CheckIdomMap (AuditMapRemove v _ _ _ _ _) =>
      encode_budget v
  | _ => 0
  end.

(** The checker has a bound in terms of actual callback budgets. *)
Definition audit_check_idom_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) parents
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    let '(result, events) := audit_check_idom_source_counted p parents cb in
    result = check_idom p parents /\ audit_check_idom_source_work weight events <=
      audit_check_idom_source_budget EV g p parents +
      fold_right (fun event n => audit_check_idom_event_budget encode_budget target_budget event +
        n) 0 events.

(** The complete checker contract includes both recorded-body and adapted bounds. *)
Definition audit_check_idom_source_contract_statement : Prop :=
  audit_check_idom_source_statement /\ audit_check_idom_source_adapted_statement.

(** Every virtual event prices only genuine supplied callbacks at captured inputs. *)
Definition audit_virtual_call_budget {V E B} (encode_budget out_budget : V -> nat)
    (target_budget source_budget : E -> nat) (event : audit_virtual_full_call V E B) : nat :=
  match event with
  | VirtualFullOut v _ _ => out_budget v
  | VirtualFullTarget e _ _ => target_budget e
  | VirtualFullSource e _ _ => source_budget e
  | VirtualFullEncode v _ _ => encode_budget v
  | VirtualFullEntry (VirtualEntriesSet (AuditSetAdd v _ _ _ _ _))
  | VirtualFullEntry (VirtualEntriesSet (AuditSetMem v _ _ _ _ _))
  | VirtualFullEntry (VirtualEntriesSet (AuditSetRemove v _ _ _ _ _)) => encode_budget v
  | _ => 0
  end.

(** Erasure prices its recorded real-vertex encoder calls. *)
Definition audit_erase_nested_event_budget {V B} (encode_budget : V -> nat)
    (event : audit_erase_nested_event V B) : nat :=
  match event with
  | EraseNestedSet (AuditMapGet v _ _ _ _ _)
  | EraseNestedSet (AuditMapSet v _ _ _ _ _ _)
  | EraseNestedSet (AuditMapRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

(** The selected backend budgets the captured events of the chosen actual branch. *)
Definition audit_dom_select_backend_budget {V E B} (budget : audit_virtual_full_call V E B -> nat)
    (trace : audit_dom_select_trace V E B) : nat :=
  match trace with
  | DomSelectLt events => audit_lt_nested_body_work budget events
  | DomSelectNca events => audit_nca_source_body_work budget events
  end.

(** An adapted selector binds one search receipt and prices every actual client call. *)
Definition audit_dom_select_single_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) choice
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source encode_budget out_budget target_budget
      source_budget,
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget
      ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents backend_events
      parents erase_events receipt result,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
        source)
        vp search semi_state semi_events /\
      audit_dom_select_single_backend EV g cb source search (SemiState.result semi_state)
        choice backend_events virtual_parents /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
        erase_events) /\
      receipt = audit_dom_search_source_counted p parents
        (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode
          cb)) /\
      result = DomTree parents (pre_num (audit_dom_source_result receipt))
        (post_num (audit_dom_source_result receipt)) /\
      result = dominator_tree_with p choice /\
      let work := audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        prepare_events + audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events +
        audit_dom_select_backend_work weight backend_events + audit_erase_nested_work weight
          erase_events +
        audit_dom_source_work weight (audit_dom_source_events receipt) in
      let budget := audit_virtual_call_budget encode_budget out_budget target_budget source_budget
        in
      let external := audit_prepare_source_body_work budget prepare_events +
        audit_dfs_source_body_work budget dfs_events +
        audit_semi_producer_nested_body_work budget semi_events + audit_dom_select_backend_budget
          budget backend_events +
        fold_right (fun event n => audit_erase_nested_event_budget encode_budget event + n) 0
          erase_events +
        fold_right (fun event n => audit_dom_source_event_budget encode_budget target_budget event
          + n) 0
          (audit_dom_source_events receipt) in
      work <= audit_dom_select_input_budget EV g p + external.

(** The selector contract includes recorded-body and per-call adapted source bounds. *)
Definition audit_dom_select_source_contract_statement : Prop :=
  audit_dom_select_single_run_statement /\ audit_dom_select_single_adapted_statement.

(** The NCA backend prices the same recorded virtual invocation at actual client inputs. *)
Definition audit_virtual_nca_single_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source encode_budget out_budget target_budget
      source_budget,
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget
      ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents nca_events
      parents erase_events,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
        source)
        vp search semi_state semi_events /\
      audit_nca_source_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search (SemiState.result semi_state) virtual_parents nca_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
        erase_events) /\
      parents = semi_nca_idom p /\
      let work := audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        prepare_events + audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events +
        audit_virtual_nca_stage_work weight nca_events + audit_erase_nested_work weight
          erase_events in
      let budget := audit_virtual_call_budget encode_budget out_budget target_budget source_budget
        in
      let external := audit_prepare_source_body_work budget prepare_events +
        audit_dfs_source_body_work budget dfs_events +
        audit_semi_producer_nested_body_work budget semi_events + audit_nca_source_body_work
          budget nca_events +
        fold_right (fun event n => audit_erase_nested_event_budget encode_budget event + n) 0
          erase_events in
      work <= audit_virtual_nca_input_budget EV g + external.

(** The NCA contract includes recorded-body and actual-call adapted source bounds. *)
Definition audit_virtual_nca_source_contract_statement : Prop :=
  audit_virtual_nca_single_run_statement /\ audit_virtual_nca_single_adapted_statement.

(** The fallback contract names its map and binary equality obligations. *)
Definition audit_flat_source_full_contract_statement : Prop :=
  audit_flat_source_contract_statement /\ audit_map_get_source_work_bound_statement /\
  audit_map_set_source_work_bound_statement /\ audit_positive_eqb_erases_statement /\
  audit_positive_eqb_source_bound_statement.

(** The checker contract names membership, map, comparison and forest-search obligations. *)
Definition audit_check_idom_source_full_contract_statement : Prop :=
  audit_check_idom_source_contract_statement /\ audit_map_get_source_work_bound_statement /\
  audit_finset_mem_erases_statement /\ audit_finset_add_erases_statement /\
  audit_positive_compare_cont_statement /\ audit_positive_order_statement /\
    audit_dom_search_source_statement.

(** The NCA source contract couples the forward pass and its virtual adapted invocation. *)
Definition audit_virtual_nca_source_full_contract_statement : Prop :=
  audit_nca_source_statement /\ audit_nca_source_unique_statement /\
  audit_virtual_nca_source_contract_statement /\ audit_map_get_source_work_bound_statement /\
  audit_map_set_source_work_bound_statement /\ audit_positive_compare_cont_statement /\
  audit_positive_order_statement.

(** The selectable producer includes both backend and forest-search source obligations. *)
Definition audit_dom_select_source_full_contract_statement : Prop :=
  audit_dom_select_source_contract_statement /\ audit_virtual_nca_source_full_contract_statement /\
  audit_lt_nested_erasure_statement /\ audit_lt_nested_unique_statement /\
    audit_lt_nested_bound_statement /\
  audit_dom_search_source_statement.
