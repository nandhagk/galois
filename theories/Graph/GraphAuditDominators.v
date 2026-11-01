(** * Dominator audit model

    Models source-level events, work, and associated contract statements.
    For example, building a dominator tree records its map operations.

    Builds on: the graph and collections interfaces imported below. *)

From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsTrie CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators
  GraphSemiDominators GraphLengauerTarjan GraphAuditBase GraphAuditDfs GraphAuditVirtual
    GraphAuditSemiDominators GraphAuditLengauerTarjan.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditElements.
Import List.ListNotations.

Record audit_lt_backend_trace (V E : Type) : Type := AuditLtBackendTrace {
  audit_lt_backend_prepare : list (audit_prepare_nested_event (V + unit) (E + V)
    (audit_virtual_call V E));
  audit_lt_backend_dfs : list (audit_dfs_nested_event (V + unit) (E + V) (audit_virtual_call V E));
  audit_lt_backend_semi : list (audit_semi_outer_call (V + unit) (E + V));
  audit_lt_backend_core : list (audit_lt_call (V + unit) (E + V));
  audit_lt_backend_erase : list (audit_erase_call V)
}.
Arguments AuditLtBackendTrace {V E} _ _ _ _ _.
Arguments audit_lt_backend_prepare {V E} _.
Arguments audit_lt_backend_dfs {V E} _.
Arguments audit_lt_backend_semi {V E} _.
Arguments audit_lt_backend_core {V E} _.
Arguments audit_lt_backend_erase {V E} _.

(** An LT backend run connects virtual search, semidominators, LT and erasure. *)

Definition audit_lt_backend_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (result : Map.t V V) (trace : audit_lt_backend_trace V E) : Prop :=
  let '(vp, (r, (prepare_events, dfs_events))) := audit_virtual_search_with_prepared EV g in
  exists state semi_events virtual_parents lt_events,
    audit_semi_compute_run vp r state semi_events /\
    audit_lt_compute_run (virtual_encoding EV) (virtual_graph EV g) r (SemiState.result state)
      virtual_parents lt_events /\
    let '(output, erase_events) := audit_erase_virtual_counted EV virtual_parents in
    result = output /\ trace = AuditLtBackendTrace prepare_events dfs_events semi_events lt_events
      erase_events.

Definition audit_lt_backend_selected_work {V E} (EV : encoding V) (trace : audit_lt_backend_trace
  V E) : nat :=
  audit_graph_prepare_nested_total_work (audit_virtual_event_work EV) (audit_lt_backend_prepare
    trace) +
  audit_dfs_nested_total_work (virtual_encoding EV) (audit_virtual_event_work EV)
    (audit_lt_backend_dfs trace) +
  audit_semi_compute_work (virtual_encoding EV) (audit_lt_backend_semi trace) +
  audit_lt_model_work (virtual_encoding EV) (audit_lt_backend_core trace) +
  audit_erase_virtual_work EV (audit_lt_backend_erase trace).

(** The LT backend admits a run yielding the original immediate dominators. *)
Definition audit_lt_backend_erasure_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    exists result trace, audit_lt_backend_run p result trace /\ result = simple_lt_idom p.

Inductive audit_dom_body (V : Type) : Type :=
  | AuditDomBodyRead (v : V) (m : Map.t V (list V)) (result : option (list V))
  | AuditDomBodyTarget (v : V)
  | AuditDomBodyEncode (v : V) (code : positive).
Arguments AuditDomBodyRead {V} _ _ _.
Arguments AuditDomBodyTarget {V} _.
Arguments AuditDomBodyEncode {V} _ _.

Inductive audit_dom_call (V E : Type) : Type :=
  | AuditDomInitialDfs (event : audit_dfs_full_call V E)
  | AuditDomCase (site : nat)
  | AuditDomElements (input : Map.t V V) (rows : list (V * V))
  | AuditDomChildRead (v : V) (m : Map.t V (list V)) (result : option (list V))
  | AuditDomChildSet (v : V) (row : list V) (m : Map.t V (list V))
  | AuditDomRootGet (v : V) (m : Map.t V V) (result : option V)
  | AuditDomPrepare (event : audit_prepare_nested_event V V (audit_dom_body V))
  | AuditDomDfs (event : audit_dfs_nested_event V V (audit_dom_body V))
  | AuditDomOutput (size : nat).
Arguments AuditDomInitialDfs {V E} _.
Arguments AuditDomCase {V E} _.
Arguments AuditDomElements {V E} _ _.
Arguments AuditDomChildRead {V E} _ _ _.
Arguments AuditDomChildSet {V E} _ _ _.
Arguments AuditDomRootGet {V E} _ _ _.
Arguments AuditDomPrepare {V E} _.
Arguments AuditDomDfs {V E} _.
Arguments AuditDomOutput {V E} _.

Fixpoint audit_dom_children_counted {V E} (EV : encoding V) (bindings : list (V * V))
    : Map.t V (list V) * list (audit_dom_call V E) :=
  match bindings with
  | [] => (Map.empty, [AuditDomCase 0])
  | (v, u) :: rest => let '(children, events) := audit_dom_children_counted EV rest in
      let found := Map.get EV u children in
      let row :=
        match found with
        | Some xs => xs
        | None => []
        end in
      (Map.set EV u (v :: row) children,
       AuditDomCase 1 :: events ++ [AuditDomChildRead u children found; AuditDomChildSet u (v ::
         row) children])
  end.

Fixpoint audit_dom_roots_counted {V E} (EV : encoding V) (m : Map.t V V) (live : list V)
    : list V * list (audit_dom_call V E) :=
  match live with
  | [] => ([], [AuditDomCase 2])
  | v :: rest => let found := Map.get EV v m in
      let '(later, events) := audit_dom_roots_counted EV m rest in
      (
        match found with
        | None => v :: later
        | Some _ => later
        end,
       AuditDomCase 3 :: AuditDomRootGet v m found :: events)
  end.

Definition audit_dom_out_counted {V} (EV : encoding V) (children : Map.t V (list V)) (v : V)
    : list V * list (audit_dom_body V) :=
  let found := Map.get EV v children in
  (
    match found with
    | Some xs => xs
    | None => []
    end, [AuditDomBodyRead v children found]).

Definition audit_dom_target_counted {V} (v : V) : V * list (audit_dom_body V) :=
  (v, [AuditDomBodyTarget v]).

Definition audit_dom_encode_counted {V} (EV : encoding V) (v : V) : positive * list
  (audit_dom_body V) :=
  let code := encode EV v in (code, [AuditDomBodyEncode v code]).

Definition audit_dom_prepare_callbacks {V} (EV : encoding V) (children : Map.t V (list V))
    : audit_prepare_callback_model V V (audit_dom_body V) :=
  AuditPrepareCallbackModel _ _ _ (audit_dom_out_counted EV children)
    audit_dom_target_counted (audit_dom_encode_counted EV).

Definition audit_dom_dfs_callbacks {V} (EV : encoding V) : audit_dfs_callback_model V V
  (audit_dom_body V) :=
  AuditDfsCallbackModel _ _ _ audit_dom_target_counted (audit_dom_encode_counted EV).

Definition audit_dom_tree_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) : dom_tree V * list (audit_dom_call V E) :=
  let '(search, first_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let live := preorder search in
  let rows := Map.elements parents in
  let '(children, child_events) := audit_dom_children_counted EV rows in
  let '(roots, root_events) := audit_dom_roots_counted EV parents live in
  let forest := Graph.Make roots live (fun v => index_edges EV children v)
    (fun v =>
      match Map.get EV v parents with
      | Some u => u
      | None => v
      end) (fun v => v) in
  let '(fp, prep_events) := audit_graph_prepare_nested_counted EV forest
    (audit_dom_prepare_callbacks EV children) in
  let '(result, dfs_events) := audit_dfs_nested_counted fp (audit_dom_dfs_callbacks EV)
    FinSet.empty roots in
  (DomTree parents (pre_num result) (post_num result),
   map AuditDomInitialDfs first_events ++ [AuditDomElements parents rows] ++ child_events ++
     root_events ++
     map AuditDomPrepare prep_events ++ map AuditDomDfs dfs_events ++ [AuditDomOutput (length
       live)]).

Definition audit_dom_body_work {V} (EV : encoding V) (event : audit_dom_body V) : nat :=
  64 +
  match event with
  | AuditDomBodyRead v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_get_weight (encode EV v)
  | AuditDomBodyEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditDomBodyTarget _ => 0
  end.

Definition audit_dom_event_work {V E} (EV : encoding V) (event : audit_dom_call V E) : nat :=
  64 +
  match event with
  | AuditDomInitialDfs item => audit_dfs_full_model_event EV item
  | AuditDomElements input _ => 64 * Nat.pow (S (audit_erase_nodes input)) 3
  | AuditDomChildRead v _ _
  | AuditDomRootGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditDomChildSet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_set_weight (encode EV v)
  | AuditDomPrepare (outer, body) => audit_graph_full_event_work outer +
      fold_right (fun item n => audit_dom_body_work EV item + n) 0 body
  | AuditDomDfs (outer, body) => audit_dfs_full_model_event EV outer +
      fold_right (fun item n => audit_dom_body_work EV item + n) 0 body
  | AuditDomOutput size => S size
  | AuditDomCase _ => 0
  end.

Definition audit_dom_model_work {V E} (EV : encoding V) (events : list (audit_dom_call V E)) : nat
  :=
  1024 * S (length events) * S (length events) +
    fold_right (fun event total => audit_dom_event_work EV event + total) 0 events.

Definition audit_dom_input_scale {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  1 + length (Graph.entries g) * S (Pos.to_nat (fuel p)) + audit_erase_nodes parents.

Definition audit_dom_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  1024 * Nat.pow (S (audit_dom_input_scale p parents)) 8.

Definition audit_dom_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  let rows := Map.elements parents in
  Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) (map fst rows ++ map
      snd rows))).

Definition audit_dom_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  let count := audit_dom_input_event_bound p parents in
  let width := Nat.max (audit_dom_input_width EV g p parents)
    (audit_key_bits_weight (Pos.of_succ_nat (S count))) in
  (128 * 64)%nat * Nat.pow (S count) 3 * Nat.pow (S width) 2.

(** Counted dominator-tree construction returns the tree with bounded events and work. *)
Definition audit_dom_tree_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) parents,
    let '(result, events) := audit_dom_tree_counted p parents in
    result = dom_tree_of p parents /\ length events <= audit_dom_input_event_bound p parents /\
    audit_dom_model_work EV events <= audit_dom_input_budget EV g p parents.

Inductive audit_dom_source_body (V B : Type) : Type :=
  | DomSourceBodyMap : audit_map_event V (list V) B -> audit_dom_source_body V B
  | DomSourceBodyTarget : V -> audit_dom_source_body V B
  | DomSourceBodyEncode : V -> positive -> list B -> audit_dom_source_body V B.
Arguments DomSourceBodyMap {V B} _.
Arguments DomSourceBodyTarget {V B} _.
Arguments DomSourceBodyEncode {V B} _ _ _.

Inductive audit_dom_source_event (V E B : Type) : Type :=
  | DomSourceCase : nat -> audit_dom_source_event V E B
  | DomSourceInitialDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
  audit_dom_source_event V E B
  | DomSourceElements : audit_elements_event (V * V) -> audit_dom_source_event V E B
  | DomSourceChild : audit_map_event V (list V) B -> audit_dom_source_event V E B
  | DomSourceParent : audit_map_event V V B -> audit_dom_source_event V E B
  | DomSourcePrepare : audit_prepare_source_event V V (audit_dom_source_body V B) ->
  audit_dom_source_event V E B
  | DomSourceDfs : audit_dfs_nested_event V V (audit_graph_callback_capture V V
  (audit_dom_source_body V B)) -> audit_dom_source_event V E B.
Arguments DomSourceCase {V E B} _.
Arguments DomSourceInitialDfs {V E B} _.
Arguments DomSourceElements {V E B} _.
Arguments DomSourceChild {V E B} _.
Arguments DomSourceParent {V E B} _.
Arguments DomSourcePrepare {V E B} _.
Arguments DomSourceDfs {V E B} _.

Fixpoint audit_dom_source_children {V E B} (enc : V -> positive * list B) (rows : list (V * V))
    : Map.t V (list V) * list (audit_dom_source_event V E B) :=
  match rows with
  | [] => (Map.empty, [DomSourceCase 0])
  | (v, u) :: rest => let '(children, events) := audit_dom_source_children enc rest in
      let '(found, reads) := audit_map_get enc u children in
      let row :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(next, writes) := audit_map_set enc u (v :: row) children in
      (next, DomSourceCase 1 :: events ++ map DomSourceChild reads ++ map DomSourceChild writes)
  end.

Fixpoint audit_dom_source_roots {V E B} (enc : V -> positive * list B) (parents : Map.t V V)
  (vertices : list V)
    : list V * list (audit_dom_source_event V E B) :=
  match vertices with
  | [] => ([], [DomSourceCase 2])
  | v :: rest => let '(found, reads) := audit_map_get enc v parents in
      let '(later, events) := audit_dom_source_roots enc parents rest in
      (
        match found with
        | None => v :: later
        | Some _ => later
        end,
        DomSourceCase 3 :: map DomSourceParent reads ++ events)
  end.

Definition audit_dom_source_out {V B} (enc : V -> positive * list B) (children : Map.t V (list V))
  (v : V)
    : list V * list (audit_dom_source_body V B) :=
  let '(found, reads) := audit_map_get enc v children in
  (
    match found with
    | Some xs => xs
    | None => []
    end, map DomSourceBodyMap reads).

Definition audit_dom_source_target {V B} (v : V) : V * list (audit_dom_source_body V B) :=
  (v, [DomSourceBodyTarget v]).

Definition audit_dom_source_encode {V B} (enc : V -> positive * list B) (v : V)
    : positive * list (audit_dom_source_body V B) :=
  let '(code, body) := enc v in (code, [DomSourceBodyEncode v code body]).

Record audit_dom_source_receipt (V E B : Type) (EV : encoding V) : Type := AuditDomSourceReceipt {
  audit_dom_source_forest : Graph.t V V;
  audit_dom_source_index : prepared EV audit_dom_source_forest;
  audit_dom_source_result : dfs_result V V;
  audit_dom_source_events : list (audit_dom_source_event V E B)
}.
Arguments AuditDomSourceReceipt {V E B EV} _ _ _ _.
Arguments audit_dom_source_forest {V E B EV} _.
Arguments audit_dom_source_index {V E B EV} _.
Arguments audit_dom_source_result {V E B EV} _.
Arguments audit_dom_source_events {V E B EV} _.

Definition audit_dom_search_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) (cb : audit_dfs_callback_model V E B)
    : audit_dom_source_receipt V E B EV :=
  let '(search, search_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let vertices := preorder search in let '(rows, element_events) := audit_map_elements parents in
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
  let '(fp, prepare_events) := audit_prepare_source_counted EV forest prepare_cb in
  let '(result, dfs_events) := audit_dfs_source_counted fp dfs_cb FinSet.empty roots in
  AuditDomSourceReceipt forest fp result
    (map DomSourceInitialDfs search_events ++ map DomSourceElements element_events ++ child_events
      ++ root_events ++
     map DomSourcePrepare prepare_events ++ map DomSourceDfs dfs_events).

Definition audit_dom_source_body_work {V B} (weight : B -> nat) (event : audit_dom_source_body V
  B) : nat :=
  64 +
  match event with
  | DomSourceBodyMap item => audit_map_source_work (fun es => fold_right (fun x n => weight x + n)
    0 es) [item]
  | DomSourceBodyEncode _ _ es => fold_right (fun x n => weight x + n) 0 es
  | DomSourceBodyTarget _ => 0
  end.

Definition audit_dom_source_body_external {V B} (weight : B -> nat) (event : audit_dom_source_body
  V B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet _ _ _ _ es _)
  | DomSourceBodyMap (AuditMapSet _ _ _ _ _ es _)
  | DomSourceBodyMap (AuditMapRemove _ _ _ _ es _)
  | DomSourceBodyEncode _ _ es =>
      fold_right (fun x n => weight x + n) 0 es
  | DomSourceBodyTarget _ => 0
  end.

Definition audit_dom_source_event_work {V E B} (weight : B -> nat) (event : audit_dom_source_event
  V E B) : nat :=
  let body := fun es => fold_right (fun x n => weight x + n) 0 es in
  64 +
  match event with
  | DomSourceInitialDfs item => audit_dfs_source_event_work weight item
  | DomSourceElements item => audit_elements_frame_work item
  | DomSourceChild item => audit_map_source_work body [item]
  | DomSourceParent item => audit_map_source_work body [item]
  | DomSourcePrepare item => audit_prepare_source_event_work (audit_dom_source_body_work weight)
    item
  | DomSourceDfs item => audit_dfs_source_event_work (audit_dom_source_body_work weight) item
  | DomSourceCase _ => 0
  end.

Definition audit_dom_source_event_external {V E B} (weight : B -> nat) (event :
  audit_dom_source_event V E B) : nat :=
  match event with
  | DomSourceInitialDfs item => audit_dfs_source_body_work weight [item]
  | DomSourceChild (AuditMapGet _ _ _ _ es _)
  | DomSourceChild (AuditMapSet _ _ _ _ _ es _)
  | DomSourceChild (AuditMapRemove _ _ _ _ es _)
  | DomSourceParent (AuditMapGet _ _ _ _ es _)
  | DomSourceParent (AuditMapSet _ _ _ _ _ es _)
  | DomSourceParent (AuditMapRemove _ _ _ _ es _) =>
      fold_right (fun x n => weight x + n) 0 es
  | DomSourcePrepare item => audit_prepare_source_body_work (audit_dom_source_body_external
    weight) [item]
  | DomSourceDfs item => audit_dfs_source_body_work (audit_dom_source_body_external weight) [item]
  | DomSourceCase _
  | DomSourceElements _ => 0
  end.

Definition audit_dom_source_work {V E B} (weight : B -> nat) (events : list
  (audit_dom_source_event V E B)) : nat :=
  fold_right (fun item n => audit_dom_source_event_work weight item + n) 0 events.

Definition audit_dom_source_external_work {V E B} (weight : B -> nat) (events : list
  (audit_dom_source_event V E B)) : nat :=
  fold_right (fun item n => audit_dom_source_event_external weight item + n) 0 events.

Definition audit_dom_search_source_budget {V E B} (EV : encoding V) (g : Graph.t V E) (p :
  prepared EV g)
    (parents : Map.t V V) (receipt : audit_dom_source_receipt V E B EV) : nat :=
  let forest := audit_dom_source_forest receipt in let fp := audit_dom_source_index receipt in
  let size := S (audit_trie_nodes parents + length (Graph.nodes forest) + length (Graph.entries
    forest) +
    Pos.to_nat (fuel p) + Pos.to_nat (fuel fp)) in
  let width := audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_graph_prepare_input_width EV forest + audit_dfs_full_input_width EV forest fp
      (Graph.entries forest) +
    fold_right Nat.max 0 (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
      (Pos.size_nat (encode EV (snd row)))) (Map.elements parents)) in
  audit_dfs_source_budget EV g p (Graph.entries g) + audit_prepare_source_budget EV forest +
    audit_dfs_source_budget EV forest fp (Graph.entries forest) +
    (1024 * 1024)%nat * Nat.pow size 8 * S width * S width.

(** Source dominator search preserves the result and satisfies its source work bound. *)
Definition audit_dom_search_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) parents
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let receipt := audit_dom_search_source_counted p parents cb in
    audit_dom_source_result receipt = dom_search p parents /\
    audit_dom_source_work weight (audit_dom_source_events receipt) <=
      audit_dom_search_source_budget EV g p parents receipt +
      audit_dom_source_external_work weight (audit_dom_source_events receipt).

(** A shared virtual search, semidominator and LT run yields the default dominator tree within its
  budget. *)
Definition audit_default_dom_single_run_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat),
    audit_virtual_base_callbacks_erase EV g cb -> (forall edge, fst (source edge) = Graph.source g
      edge) ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents lt_events
      parents erase_events receipt result,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
        source)
        vp search semi_state semi_events /\
      audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search (SemiState.result semi_state) virtual_parents lt_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
        erase_events) /\
      receipt = audit_dom_search_source_counted p parents
        (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode
          cb)) /\
      result = DomTree parents (pre_num (audit_dom_source_result receipt)) (post_num
        (audit_dom_source_result receipt)) /\
      result = dominator_tree p /\
      audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        prepare_events +
      audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events +
          audit_virtual_lt_stage_work weight lt_events +
      audit_erase_nested_work weight erase_events + audit_dom_source_work weight
        (audit_dom_source_events receipt) <=
        audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents receipt +
      audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
      audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events +
      audit_virtual_semi_external_work weight semi_events + audit_virtual_lt_external_work weight
        lt_events +
      audit_erase_nested_body_work weight erase_events + audit_dom_source_external_work weight
        (audit_dom_source_events receipt).
