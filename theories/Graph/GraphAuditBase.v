(** * Graph preparation audit model

    Models source-level events, work, and associated contract statements.
    For example, preparing a graph records the outgoing-edge and encoder calls.

    Builds on: the graph and collections interfaces imported below. *)

From Galois.Collections Require Import CollectionsAuditCost.
From Stdlib Require Import List PArith Permutation.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Stdlib Require Import Bool NArith.
From Galois.Collections Require Import CollectionsAuditMap.
Import List.ListNotations.

Inductive audit_graph_prepare_map_site : Type :=
  | AuditGraphOutSet
  | AuditGraphIncomingGet
  | AuditGraphIncomingSet.

Inductive audit_graph_prepare_call (V E : Type) : Type :=
  | AuditPrepareOutCall (vertex : V) (edges : list E)
  | AuditPrepareTargetCall (edge : E) (target : V)
  | AuditPrepareEncodeCall (site : audit_graph_prepare_map_site) (vertex : V) (code : positive).
Arguments AuditPrepareOutCall {V E} _ _.
Arguments AuditPrepareTargetCall {V E} _ _.
Arguments AuditPrepareEncodeCall {V E} _ _ _.

Definition audit_graph_prepare_calls {V E} (EV : encoding V) (g : Graph.t V E)
    : list (audit_graph_prepare_call V E) :=
  flat_map (fun v =>
    let outgoing := Graph.out g v in
    [AuditPrepareOutCall v outgoing; AuditPrepareOutCall v outgoing;
     AuditPrepareOutCall v outgoing; AuditPrepareEncodeCall AuditGraphOutSet v (encode EV v)] ++
    flat_map (fun e =>
      let target := Graph.target g e in
      [AuditPrepareTargetCall e target; AuditPrepareTargetCall e target;
       AuditPrepareEncodeCall AuditGraphIncomingGet target (encode EV target);
       AuditPrepareEncodeCall AuditGraphIncomingSet target (encode EV target)]) outgoing)
    (Graph.nodes g).

Definition audit_graph_prepare_callback_count {V E} (g : Graph.t V E) : nat :=
  4 * length (Graph.nodes g) +
  4 * fold_right (fun v n => length (Graph.out g v) + n) 0 (Graph.nodes g).

Inductive audit_graph_prepare_out_execution {V E} (EV : encoding V) (g : Graph.t V E)
    : list V -> Map.t V (list E) -> Map.t V (list E) ->
      list (audit_graph_prepare_call V E) -> Prop :=
  | AuditGraphOutNil m : audit_graph_prepare_out_execution EV g [] m m []
  | AuditGraphOutCons v rest initial middle events :
      audit_graph_prepare_out_execution EV g rest initial middle events ->
      audit_graph_prepare_out_execution EV g (v :: rest) initial
        (Map.set EV v (Graph.out g v) middle)
        (events ++ [AuditPrepareOutCall v (Graph.out g v);
          AuditPrepareEncodeCall AuditGraphOutSet v (encode EV v)]).

Inductive audit_graph_prepare_edges_execution {V E} (EV : encoding V) (g : Graph.t V E)
    : list E -> Map.t V (list E) -> Map.t V (list E) ->
      list (audit_graph_prepare_call V E) -> Prop :=
  | AuditGraphEdgesNil m : audit_graph_prepare_edges_execution EV g [] m m []
  | AuditGraphEdgesCons edge rest initial middle events :
      audit_graph_prepare_edges_execution EV g rest initial middle events ->
      audit_graph_prepare_edges_execution EV g (edge :: rest) initial (index_edge EV g edge middle)
        (events ++ [AuditPrepareTargetCall edge (Graph.target g edge);
          AuditPrepareTargetCall edge (Graph.target g edge);
          AuditPrepareEncodeCall AuditGraphIncomingGet (Graph.target g edge)
            (encode EV (Graph.target g edge));
          AuditPrepareEncodeCall AuditGraphIncomingSet (Graph.target g edge)
            (encode EV (Graph.target g edge))]).

Inductive audit_graph_prepare_in_execution {V E} (EV : encoding V) (g : Graph.t V E)
    : list V -> Map.t V (list E) -> Map.t V (list E) ->
      list (audit_graph_prepare_call V E) -> Prop :=
  | AuditGraphInNil m : audit_graph_prepare_in_execution EV g [] m m []
  | AuditGraphInCons v rest initial middle final tail_events edge_events :
      audit_graph_prepare_in_execution EV g rest initial middle tail_events ->
      audit_graph_prepare_edges_execution EV g (Graph.out g v) middle final edge_events ->
      audit_graph_prepare_in_execution EV g (v :: rest) initial final
        (tail_events ++ [AuditPrepareOutCall v (Graph.out g v)] ++ edge_events).

Inductive audit_graph_prepare_execution {V E} (EV : encoding V) (g : Graph.t V E)
    : prepared EV g -> list (audit_graph_prepare_call V E) -> Prop :=
  | AuditGraphPrepareRun out incoming out_events in_events :
      audit_graph_prepare_out_execution EV g (Graph.nodes g) Map.empty out out_events ->
      audit_graph_prepare_in_execution EV g (Graph.nodes g) Map.empty incoming in_events ->
      audit_graph_prepare_execution EV g
        (Prepared out incoming (Pos.of_succ_nat (2 * length (Graph.nodes g) + edge_count g + 1)))
        (out_events ++ in_events ++ map (fun v => AuditPrepareOutCall v (Graph.out g v))
          (rev (Graph.nodes g))).

Fixpoint audit_graph_prepare_out_counted {V E} (EV : encoding V) (g : Graph.t V E)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_prepare_call V E) :=
  match nodes with
  | [] => (initial, [])
  | v :: rest =>
      let '(middle, events) := audit_graph_prepare_out_counted EV g rest initial in
      let outgoing := Graph.out g v in
      let code := encode EV v in
      let next := Trie.set code (v, outgoing) middle in
      (next, events ++ [AuditPrepareOutCall v outgoing; AuditPrepareEncodeCall AuditGraphOutSet v
        code])
  end.

Fixpoint audit_graph_prepare_edges_counted {V E} (EV : encoding V) (g : Graph.t V E)
    (edges : list E) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_prepare_call V E) :=
  match edges with
  | [] => (initial, [])
  | edge :: rest =>
      let '(middle, events) := audit_graph_prepare_edges_counted EV g rest initial in
      let write_target := Graph.target g edge in
      let read_target := Graph.target g edge in
      let read_code := encode EV read_target in
      let found := Map.code_get read_code middle in
      let row :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let write_code := encode EV write_target in
      let next := Trie.set write_code (write_target, edge :: row) middle in
      (next, events ++ [AuditPrepareTargetCall edge write_target; AuditPrepareTargetCall edge
        read_target;
        AuditPrepareEncodeCall AuditGraphIncomingGet read_target read_code;
        AuditPrepareEncodeCall AuditGraphIncomingSet write_target write_code])
  end.

Fixpoint audit_graph_prepare_in_counted {V E} (EV : encoding V) (g : Graph.t V E)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_prepare_call V E) :=
  match nodes with
  | [] => (initial, [])
  | v :: rest =>
      let '(middle, tail_events) := audit_graph_prepare_in_counted EV g rest initial in
      let outgoing := Graph.out g v in
      let '(next, edge_events) := audit_graph_prepare_edges_counted EV g outgoing middle in
      (next, tail_events ++ [AuditPrepareOutCall v outgoing] ++ edge_events)
  end.

Fixpoint audit_graph_edge_count_counted {V E} (g : Graph.t V E) (nodes : list V)
    : nat * list (audit_graph_prepare_call V E) :=
  match nodes with
  | [] => (0, [])
  | v :: rest =>
      let '(later, events) := audit_graph_edge_count_counted g rest in
      let outgoing := Graph.out g v in
      (length outgoing + later, events ++ [AuditPrepareOutCall v outgoing])
  end.

Definition audit_graph_prepare_counted {V E} (EV : encoding V) (g : Graph.t V E)
    : prepared EV g * list (audit_graph_prepare_call V E) :=
  let '(outgoing, out_events) := audit_graph_prepare_out_counted EV g (Graph.nodes g) Map.empty in
  let '(incoming, in_events) := audit_graph_prepare_in_counted EV g (Graph.nodes g) Map.empty in
  let '(edges, edge_events) := audit_graph_edge_count_counted g (Graph.nodes g) in
  (Prepared outgoing incoming (Pos.of_succ_nat (2 * length (Graph.nodes g) + edges + 1)),
   out_events ++ in_events ++ edge_events).

(** Graph preparation has an execution yielding the prepared graph. *)

Definition audit_graph_prepare_execution_exists_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    exists result events, audit_graph_prepare_execution EV g result events /\
      result = prepare EV g.

(** A traced preparation yields the graph and the expected callback multiset and count. *)
Definition audit_graph_prepare_callbacks_statement
    (traced : forall {V E} (EV : encoding V) (g : Graph.t V E),
      prepared EV g * list (audit_graph_prepare_call V E)) : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    let '(result, events) := traced EV g in
    audit_graph_prepare_execution EV g result events /\
    result = prepare EV g /\
    Permutation events (audit_graph_prepare_calls EV g) /\
    length events = audit_graph_prepare_callback_count g.

Definition audit_graph_prepare_map_model_event {V E} (event : audit_graph_prepare_call V E) : nat :=
  match event with
  | AuditPrepareEncodeCall AuditGraphIncomingGet _ code => audit_get_weight code
  | AuditPrepareEncodeCall _ _ code => audit_set_weight code
  | _ => 0
  end.

Definition audit_graph_prepare_map_model_work {V E} (events : list (audit_graph_prepare_call V E))
    : nat := fold_right (fun event n => audit_graph_prepare_map_model_event event + n) 0 events.

Definition audit_graph_prepare_map_model_expected {V E} (EV : encoding V) (g : Graph.t V E)
    : nat :=
  fold_right (fun v total =>
    audit_set_weight (encode EV v) +
    fold_right (fun edge subtotal =>
      audit_get_weight (encode EV (Graph.target g edge)) +
      audit_set_weight (encode EV (Graph.target g edge)) + subtotal)
      total (Graph.out g v)) 0 (Graph.nodes g).

(** Preparation map-event work equals its input-derived sum. *)
Definition audit_graph_prepare_map_model_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) result events,
    audit_graph_prepare_execution EV g result events ->
    audit_graph_prepare_map_model_work events = audit_graph_prepare_map_model_expected EV g.

Definition audit_graph_prepare_emission_event {V E} (event : audit_graph_prepare_call V E) : nat :=
  match event with
  | AuditPrepareEncodeCall _ _ code => audit_encoding_weight (audit_key_bits_weight code)
  | _ => 0
  end.

Definition audit_graph_prepare_emission_work {V E} (events : list (audit_graph_prepare_call V E))
    : nat := fold_right (fun event n => audit_graph_prepare_emission_event event + n) 0 events.

Definition audit_graph_prepare_emission_expected {V E} (EV : encoding V) (g : Graph.t V E)
    : nat :=
  fold_right (fun v total =>
    audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    fold_right (fun edge subtotal =>
      2 * audit_encoding_weight (audit_key_bits_weight (encode EV (Graph.target g edge))) +
        subtotal)
      total (Graph.out g v)) 0 (Graph.nodes g).

(** Preparation encoding-event work equals its input-derived sum. *)
Definition audit_graph_prepare_emission_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) result events,
    audit_graph_prepare_execution EV g result events ->
    audit_graph_prepare_emission_work events = audit_graph_prepare_emission_expected EV g.

Definition audit_graph_prepare_input_width {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  fold_right (fun v width => Nat.max (audit_key_bits_weight (encode EV v))
    (fold_right (fun edge more => Nat.max (audit_key_bits_weight (encode EV (Graph.target g
      edge))) more)
      width (Graph.out g v))) 0 (Graph.nodes g).

Definition audit_graph_prepare_input_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let n := length (Graph.nodes g) in
  let m := edge_count g in
  let events := 4 * n + 4 * m in
  let fuel_input := 2 * n + m + 1 in
  64 * S (events + fuel_input) * S (events + fuel_input) +
    events * (66 + 3 * audit_graph_prepare_input_width EV g) +
    audit_unary_conversion_weight fuel_input + fuel_input * Pos.size_nat (Pos.of_succ_nat
      fuel_input).

(** Counted preparation yields the graph with bounded callback count and work. *)
Definition audit_graph_prepare_model_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    let '(result, events) := audit_graph_prepare_counted EV g in
    audit_graph_prepare_execution EV g result events /\
    result = prepare EV g /\
    length events = audit_graph_prepare_callback_count g /\
    audit_graph_prepare_map_model_work events + audit_graph_prepare_emission_work events <=
      audit_graph_prepare_input_budget EV g.

Inductive audit_graph_full_call (V E : Type) : Type :=
  | AuditGraphFullCase (site : nat)
  | AuditGraphFullCall (call : audit_graph_prepare_call V E)
  | AuditGraphFullLength (edges : list E) (result : nat)
  | AuditGraphFullNodesLength (nodes : list V) (result : nat)
  | AuditGraphFullFuel (nodes edges : nat) (result : positive).
Arguments AuditGraphFullCase {V E} _.
Arguments AuditGraphFullCall {V E} _.
Arguments AuditGraphFullLength {V E} _ _.
Arguments AuditGraphFullNodesLength {V E} _ _.
Arguments AuditGraphFullFuel {V E} _ _ _.

Fixpoint audit_graph_full_out {V E} (EV : encoding V) (g : Graph.t V E)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_full_call V E) :=
  match nodes with
  | [] => (initial, [AuditGraphFullCase 0])
  | v :: rest =>
      let '(middle, events) := audit_graph_full_out EV g rest initial in
      let outgoing := Graph.out g v in let code := encode EV v in
      let next := Trie.set code (v, outgoing) middle in
      (next, AuditGraphFullCase 1 :: events ++
        [AuditGraphFullCall (AuditPrepareOutCall v outgoing);
         AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphOutSet v code)])
  end.

Fixpoint audit_graph_full_edges {V E} (EV : encoding V) (g : Graph.t V E)
    (edges : list E) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_full_call V E) :=
  match edges with
  | [] => (initial, [AuditGraphFullCase 2])
  | edge :: rest =>
      let '(middle, events) := audit_graph_full_edges EV g rest initial in
      let write_target := Graph.target g edge in let read_target := Graph.target g edge in
      let read_code := encode EV read_target in let found := Map.code_get read_code middle in
      let row :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let write_code := encode EV write_target in
      let next := Trie.set write_code (write_target, edge :: row) middle in
      (next, AuditGraphFullCase 3 :: events ++
        [AuditGraphFullCall (AuditPrepareTargetCall edge write_target);
         AuditGraphFullCall (AuditPrepareTargetCall edge read_target);
         AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphIncomingGet read_target read_code);
         AuditGraphFullCase (
           match found with
           | Some _ => 4
           | None => 5
           end);
         AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphIncomingSet write_target write_code)])
  end.

Fixpoint audit_graph_full_in {V E} (EV : encoding V) (g : Graph.t V E)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_full_call V E) :=
  match nodes with
  | [] => (initial, [AuditGraphFullCase 6])
  | v :: rest => let '(middle, tail_events) := audit_graph_full_in EV g rest initial in
      let outgoing := Graph.out g v in
      let '(next, edge_events) := audit_graph_full_edges EV g outgoing middle in
      (next, AuditGraphFullCase 7 :: tail_events ++
        [AuditGraphFullCall (AuditPrepareOutCall v outgoing)] ++ edge_events)
  end.

Fixpoint audit_graph_full_edge_count {V E} (g : Graph.t V E) (nodes : list V)
    : nat * list (audit_graph_full_call V E) :=
  match nodes with
  | [] => (0, [AuditGraphFullCase 8])
  | v :: rest => let '(later, events) := audit_graph_full_edge_count g rest in
      let outgoing := Graph.out g v in let len := length outgoing in
      (len + later, AuditGraphFullCase 9 :: events ++
        [AuditGraphFullCall (AuditPrepareOutCall v outgoing); AuditGraphFullLength outgoing len])
  end.

Definition audit_graph_prepare_full_counted {V E} (EV : encoding V) (g : Graph.t V E)
    : prepared EV g * list (audit_graph_full_call V E) :=
  let '(outgoing, out_events) := audit_graph_full_out EV g (Graph.nodes g) Map.empty in
  let '(incoming, in_events) := audit_graph_full_in EV g (Graph.nodes g) Map.empty in
  let nodes := length (Graph.nodes g) in
  let '(edges, edge_events) := audit_graph_full_edge_count g (Graph.nodes g) in
  let fuel := Pos.of_succ_nat (2 * nodes + edges + 1) in
  (Prepared outgoing incoming fuel, out_events ++ in_events ++
    [AuditGraphFullNodesLength (Graph.nodes g) nodes] ++ edge_events ++
    [AuditGraphFullFuel nodes edges fuel]).

Definition audit_graph_full_event_work {V E} (event : audit_graph_full_call V E) : nat :=
  64 +
  match event with
  | AuditGraphFullCall call => audit_graph_prepare_map_model_event call +
    audit_graph_prepare_emission_event call
  | AuditGraphFullLength edges _ => 2 * S (length edges)
  | AuditGraphFullNodesLength nodes _ => S (length nodes)
  | AuditGraphFullFuel nodes edges fuel =>
      let amount := 2 * nodes + edges + 1 in
      32 * S amount * S amount + audit_unary_conversion_weight amount +
        amount * audit_key_bits_weight fuel
  | AuditGraphFullCase _ => 0
  end.

Definition audit_graph_prepare_full_work {V E} (events : list (audit_graph_full_call V E)) : nat :=
  64 * S (length events) * S (length events) +
    fold_right (fun event total => audit_graph_full_event_work event + total) 0 events.

Definition audit_graph_prepare_full_event_bound {V E} (g : Graph.t V E) : nat :=
  8 + 12 * length (Graph.nodes g) + 8 * edge_count g.

Definition audit_graph_prepare_full_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let count := audit_graph_prepare_full_event_bound g in
  let amount := 2 * length (Graph.nodes g) + edge_count g + 1 in
  128 * S count * S count + count * (128 + 3 * audit_graph_prepare_input_width EV g) +
    64 * S amount * S amount + amount * audit_key_bits_weight (Pos.of_succ_nat amount).

(** Full counted preparation yields the graph with bounded events and work. *)
Definition audit_graph_prepare_full_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    let '(result, events) := audit_graph_prepare_full_counted EV g in
    result = prepare EV g /\
    length events <= audit_graph_prepare_full_event_bound g /\
    audit_graph_prepare_full_work events <= audit_graph_prepare_full_budget EV g.

Record audit_prepare_callback_model (V E B : Type) : Type := AuditPrepareCallbackModel {
  audit_prepare_out_model : V -> list E * list B;
  audit_prepare_target_model : E -> V * list B;
  audit_prepare_encode_model : V -> positive * list B
}.
Arguments audit_prepare_out_model {V E B} _ _.
Arguments audit_prepare_target_model {V E B} _ _.
Arguments audit_prepare_encode_model {V E B} _ _.

(** Preparation callbacks return the original graph and encoding values. *)
Definition audit_prepare_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) : Prop :=
  (forall v, fst (audit_prepare_out_model cb v) = Graph.out g v) /\
  (forall e, fst (audit_prepare_target_model cb e) = Graph.target g e) /\
  (forall v, fst (audit_prepare_encode_model cb v) = encode EV v).

Definition audit_prepare_nested_event (V E B : Type) : Type := audit_graph_full_call V E * list B.

Fixpoint audit_prepare_nested_out {V E B} (g : Graph.t V E) (cb : audit_prepare_callback_model V E
  B)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_prepare_nested_event V E B) :=
  match nodes with
  | [] => (initial, [(AuditGraphFullCase 0, [])])
  | v :: rest => let '(middle, events) := audit_prepare_nested_out g cb rest initial in
      let '(outgoing, out_body) := audit_prepare_out_model cb v in
      let '(code, encode_body) := audit_prepare_encode_model cb v in
      let next := Trie.set code (v, outgoing) middle in
      (next, (AuditGraphFullCase 1, []) :: events ++
        [(AuditGraphFullCall (AuditPrepareOutCall v outgoing), out_body);
         (AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphOutSet v code), encode_body)])
  end.

Fixpoint audit_prepare_nested_edges {V E B} (g : Graph.t V E) (cb : audit_prepare_callback_model V
  E B)
    (edges : list E) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_prepare_nested_event V E B) :=
  match edges with
  | [] => (initial, [(AuditGraphFullCase 2, [])])
  | edge :: rest => let '(middle, events) := audit_prepare_nested_edges g cb rest initial in
      let '(write_target, write_target_body) := audit_prepare_target_model cb edge in
      let '(read_target, read_target_body) := audit_prepare_target_model cb edge in
      let '(read_code, read_body) := audit_prepare_encode_model cb read_target in
      let found := Map.code_get read_code middle in
      let row :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(write_code, write_body) := audit_prepare_encode_model cb write_target in
      let next := Trie.set write_code (write_target, edge :: row) middle in
      (next, (AuditGraphFullCase 3, []) :: events ++
        [(AuditGraphFullCall (AuditPrepareTargetCall edge write_target), write_target_body);
         (AuditGraphFullCall (AuditPrepareTargetCall edge read_target), read_target_body);
         (AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphIncomingGet read_target read_code),
           read_body);
         (AuditGraphFullCase (
           match found with
           | Some _ => 4
           | None => 5
           end), []);
         (AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphIncomingSet write_target
           write_code), write_body)])
  end.

Fixpoint audit_prepare_nested_in {V E B} (g : Graph.t V E) (cb : audit_prepare_callback_model V E B)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_prepare_nested_event V E B) :=
  match nodes with
  | [] => (initial, [(AuditGraphFullCase 6, [])])
  | v :: rest => let '(middle, tail_events) := audit_prepare_nested_in g cb rest initial in
      let '(outgoing, body) := audit_prepare_out_model cb v in
      let '(next, edge_events) := audit_prepare_nested_edges g cb outgoing middle in
      (next, (AuditGraphFullCase 7, []) :: tail_events ++
        [(AuditGraphFullCall (AuditPrepareOutCall v outgoing), body)] ++ edge_events)
  end.

Fixpoint audit_prepare_nested_edge_count {V E B} (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) (nodes : list V)
    : nat * list (audit_prepare_nested_event V E B) :=
  match nodes with
  | [] => (0, [(AuditGraphFullCase 8, [])])
  | v :: rest => let '(later, events) := audit_prepare_nested_edge_count g cb rest in
      let '(outgoing, body) := audit_prepare_out_model cb v in let len := length outgoing in
      (len + later, (AuditGraphFullCase 9, []) :: events ++
        [(AuditGraphFullCall (AuditPrepareOutCall v outgoing), body); (AuditGraphFullLength
          outgoing len, [])])
  end.

Definition audit_graph_prepare_nested_counted {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B)
    : prepared EV g * list (audit_prepare_nested_event V E B) :=
  let '(outgoing, out_events) := audit_prepare_nested_out g cb (Graph.nodes g) Map.empty in
  let '(incoming, in_events) := audit_prepare_nested_in g cb (Graph.nodes g) Map.empty in
  let nodes := length (Graph.nodes g) in
  let '(edges, edge_events) := audit_prepare_nested_edge_count g cb (Graph.nodes g) in
  let fuel := Pos.of_succ_nat (2 * nodes + edges + 1) in
  (Prepared outgoing incoming fuel, out_events ++ in_events ++
    [(AuditGraphFullNodesLength (Graph.nodes g) nodes, [])] ++ edge_events ++
    [(AuditGraphFullFuel nodes edges fuel, [])]).

Definition audit_prepare_nested_body_work {V E B} (weight : B -> nat)
    (events : list (audit_prepare_nested_event V E B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd event) + total)
    0 events.

(** Nested preparation erases to the full trace and obeys its bounds. *)
Definition audit_graph_prepare_nested_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_prepare_callback_model V E B),
    audit_prepare_callbacks_erase EV g cb ->
    let '(result, events) := audit_graph_prepare_nested_counted EV g cb in
    result = prepare EV g /\
    map fst events = snd (audit_graph_prepare_full_counted EV g) /\
    length events <= audit_graph_prepare_full_event_bound g /\
    audit_graph_prepare_full_work (map fst events) <= audit_graph_prepare_full_budget EV g.

Definition audit_graph_prepare_nested_total_work {V E B} (weight : B -> nat)
    (events : list (audit_prepare_nested_event V E B)) : nat :=
  audit_graph_prepare_full_work (map fst events) + audit_prepare_nested_body_work weight events.

Inductive audit_comb_event (C : Type) : Type :=
  | AuditCombCase (site : nat)
  | AuditCombBody (event : C).
Arguments AuditCombCase {C} _.
Arguments AuditCombBody {C} _.

Definition audit_comb_call_count {C} (events : list (audit_comb_event C)) : nat :=
  fold_right (fun event n =>
    match event with
    | AuditCombCase 0 => S n
    | _ => n
    end) 0 events.

Fixpoint audit_pos_iter {A C} (step : A -> A * list C) (x : A) (fuel : positive)
    : A * list (audit_comb_event C) :=
  match fuel with
  | xH => let '(result, events) := step x in
      (result, AuditCombCase 0 :: map AuditCombBody events)
  | xO rest => let '(middle, first) := audit_pos_iter step x rest in
      let '(result, second) := audit_pos_iter step middle rest in
      (result, AuditCombCase 1 :: first ++ second)
  | xI rest => let '(middle, first) := audit_pos_iter step x rest in
      let '(last, second) := audit_pos_iter step middle rest in
      let '(result, events) := step last in
      (result, AuditCombCase 2 :: first ++ second ++ AuditCombCase 0 :: map AuditCombBody events)
  end.

Definition audit_n_iter {A C} (fuel : N) (step : A -> A * list C) (x : A)
    : A * list (audit_comb_event C) :=
  match fuel with
  | N0 => (x, [AuditCombCase 3])
  | Npos p => let '(result, events) := audit_pos_iter step x p in
      (result, AuditCombCase 4 :: events)
  end.

Fixpoint audit_fold_left {A S C} (step : S -> A -> S * list C) (xs : list A) (initial : S)
    : S * list (audit_comb_event C) :=
  match xs with
  | [] => (initial, [AuditCombCase 5])
  | a :: rest => let '(next, body) := step initial a in
      let '(result, events) := audit_fold_left step rest next in
      (result, AuditCombCase 6 :: map AuditCombBody body ++ events)
  end.

Fixpoint audit_fold_right {A S C} (step : A -> S -> S * list C) (xs : list A) (initial : S)
    : S * list (audit_comb_event C) :=
  match xs with
  | [] => (initial, [AuditCombCase 7])
  | a :: rest => let '(middle, events) := audit_fold_right step rest initial in
      let '(result, body) := step a middle in
      (result, AuditCombCase 8 :: events ++ map AuditCombBody body)
  end.

Fixpoint audit_map {A B C} (f : A -> B * list C) (xs : list A)
    : list B * list (audit_comb_event C) :=
  match xs with
  | [] => ([], [AuditCombCase 9])
  | a :: rest => let '(b, body) := f a in
      let '(later, events) := audit_map f rest in
      (b :: later, AuditCombCase 10 :: map AuditCombBody body ++ events)
  end.

Fixpoint audit_filter {A C} (f : A -> bool * list C) (xs : list A)
    : list A * list (audit_comb_event C) :=
  match xs with
  | [] => ([], [AuditCombCase 11])
  | a :: rest => let '(keep, body) := f a in
      let '(later, events) := audit_filter f rest in
      ((if keep then a :: later else later),
       AuditCombCase 12 :: map AuditCombBody body ++ AuditCombCase (if keep then 13 else 14) ::
         events)
  end.

Fixpoint audit_existsb_strict {A C} (f : A -> bool * list C) (xs : list A)
    : bool * list (audit_comb_event C) :=
  match xs with
  | [] => (false, [AuditCombCase 15])
  | a :: rest => let '(here, body) := f a in
      let '(later, events) := audit_existsb_strict f rest in
      (here || later, AuditCombCase 16 :: map AuditCombBody body ++ events)
  end.

(** Counted positive iteration erases to iteration and records its number of calls. *)
Definition audit_pos_iter_statement : Prop :=
  forall A C (step : A -> A * list C) (f : A -> A) x fuel,
    (forall a, fst (step a) = f a) ->
    let '(result, events) := audit_pos_iter step x fuel in
    result = Pos.iter f x fuel /\ audit_comb_call_count events = Pos.to_nat fuel.

(** Counted binary-natural iteration erases to iteration and records its number of calls. *)
Definition audit_n_iter_statement : Prop :=
  forall A C (step : A -> A * list C) (f : A -> A) x fuel,
    (forall a, fst (step a) = f a) ->
    let '(result, events) := audit_n_iter fuel step x in
    result = N.iter fuel f x /\ audit_comb_call_count events = N.to_nat fuel.

(** Counted left and right folds erase to their ordinary folds. *)
Definition audit_fold_statement : Prop :=
  (forall A S C (step : S -> A -> S * list C) (f : S -> A -> S) xs initial,
    (forall s a, fst (step s a) = f s a) ->
    fst (audit_fold_left step xs initial) = fold_left f xs initial) /\
  (forall A S C (step : A -> S -> S * list C) (f : A -> S -> S) xs initial,
    (forall a s, fst (step a s) = f a s) ->
    fst (audit_fold_right step xs initial) = fold_right f initial xs).

(** Counted map, filter and strict exists erase to their ordinary operations. *)
Definition audit_list_map_filter_exists_statement : Prop :=
  (forall A B C (step : A -> B * list C) (f : A -> B) xs,
    (forall a, fst (step a) = f a) -> fst (audit_map step xs) = map f xs) /\
  (forall A C (step : A -> bool * list C) (f : A -> bool) xs,
    (forall a, fst (step a) = f a) -> fst (audit_filter step xs) = filter f xs) /\
  (forall A C (step : A -> bool * list C) (f : A -> bool) xs,
    (forall a, fst (step a) = f a) -> fst (audit_existsb_strict step xs) = existsb f xs).

(** Source work for the pinned naive [List.rev] and its append frames. *)
Fixpoint audit_graph_reverse_work (size : nat) : nat :=
  match size with
  | 0 => 1
  | S rest => 3 + rest + audit_graph_reverse_work rest
  end.

Inductive audit_graph_reverse_run {A} : list A -> list A -> nat -> Prop :=
  | GraphReverseNil : audit_graph_reverse_run [] [] 1
  | GraphReverseCons x xs reversed work :
    audit_graph_reverse_run xs reversed work ->
    audit_graph_reverse_run (x :: xs) (reversed ++ [x]) (3 + length reversed + work).

(** Legacy reverse admits a run with the exact result and bounded work. *)
Definition audit_graph_reverse_run_statement : Prop :=
  forall A (xs : list A), exists result work,
    audit_graph_reverse_run xs result work /\ result = rev xs /\
    work = audit_graph_reverse_work (length xs) /\ work <= 4 * S (length xs) * S (length xs).

(** The selected source body uses the standard tail-recursive [rev_append]. *)
Definition audit_graph_reverse_fast_work (size : nat) : nat := 1 + 2 * size.

Fixpoint audit_graph_reverse_fast_counted {A} (xs acc : list A) : list A * nat :=
  match xs with
  | [] => (acc, 1)
  | x :: rest => let '(result, work) := audit_graph_reverse_fast_counted rest (x :: acc) in
      (result, 2 + work)
  end.

Inductive audit_graph_reverse_fast_run {A} : list A -> list A -> list A -> nat -> Prop :=
  | GraphReverseFastNil acc : audit_graph_reverse_fast_run [] acc acc 1
  | GraphReverseFastCons x xs acc result work :
    audit_graph_reverse_fast_run xs (x :: acc) result work ->
    audit_graph_reverse_fast_run (x :: xs) acc result (2 + work).

(** Tail-recursive reverse admits a run with the exact result and work. *)
Definition audit_graph_reverse_fast_run_statement : Prop :=
  forall A (xs acc : list A), exists result work,
    audit_graph_reverse_fast_run xs acc result work /\ result = rev_append xs acc /\
    result = rev xs ++ acc /\ work = audit_graph_reverse_fast_work (length xs).

(** Counted tail-recursive reverse realizes its run, result and work. *)
Definition audit_graph_reverse_fast_counted_statement : Prop :=
  forall A (xs acc : list A),
    let '(result, work) := audit_graph_reverse_fast_counted xs acc in
    audit_graph_reverse_fast_run xs acc result work /\ result = rev_append xs acc /\
    result = rev xs ++ acc /\ work = audit_graph_reverse_fast_work (length xs).

(** A reusable source/budget law only for genuinely external callback bodies. *)
Record audit_graph_external_callback_adapter {A R B} (call : A -> R * list B) (weight : B -> nat)
    (source : A -> R -> list B -> nat -> Prop) (budget : A -> nat) : Prop := {
  audit_graph_external_callback_source : forall arg result body,
    call arg = (result, body) ->
    source arg result body (fold_right (fun item n => weight item + n) 0 body) /\
    fold_right (fun item n => weight item + n) 0 body <= budget arg
}.

Inductive audit_prepare_source_event (V E B : Type) : Type :=
  | PrepareSourceCase : nat -> audit_prepare_source_event V E B
  | PrepareSourceOut : V -> list E -> list B -> audit_prepare_source_event V E B
  | PrepareSourceTarget : E -> V -> list B -> audit_prepare_source_event V E B
  | PrepareSourceMap : audit_map_event V (list E) B -> audit_prepare_source_event V E B
  | PrepareSourceLength : nat -> audit_prepare_source_event V E B
  | PrepareSourceFuel : nat -> nat -> positive -> audit_prepare_source_event V E B.
Arguments PrepareSourceCase {V E B} _.
Arguments PrepareSourceOut {V E B} _ _ _.
Arguments PrepareSourceTarget {V E B} _ _ _.
Arguments PrepareSourceMap {V E B} _.
Arguments PrepareSourceLength {V E B} _.
Arguments PrepareSourceFuel {V E B} _ _ _.

Fixpoint audit_prepare_source_out {V E B} (cb : audit_prepare_callback_model V E B)
    (nodes : list V) (initial : Map.t V (list E)) : Map.t V (list E) * list
      (audit_prepare_source_event V E B) :=
  match nodes with
  | [] => (initial, [PrepareSourceCase 0])
  | v :: rest => let '(middle, events) := audit_prepare_source_out cb rest initial in
      let '(outgoing, body) := audit_prepare_out_model cb v in
      let '(next, writes) := audit_map_set (audit_prepare_encode_model cb) v outgoing middle in
      (next, PrepareSourceCase 1 :: events ++ [PrepareSourceOut v outgoing body] ++ map
        PrepareSourceMap writes)
  end.

Fixpoint audit_prepare_source_edges {V E B} (cb : audit_prepare_callback_model V E B)
    (edges : list E) (initial : Map.t V (list E)) : Map.t V (list E) * list
      (audit_prepare_source_event V E B) :=
  match edges with
  | [] => (initial, [PrepareSourceCase 2])
  | edge :: rest => let '(middle, events) := audit_prepare_source_edges cb rest initial in
      let '(write_target, write_body) := audit_prepare_target_model cb edge in
      let '(read_target, read_body) := audit_prepare_target_model cb edge in
      let '(found, reads) := audit_map_get (audit_prepare_encode_model cb) read_target middle in
      let row :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(next, writes) := audit_map_set (audit_prepare_encode_model cb) write_target (edge ::
        row) middle in
      (next, PrepareSourceCase 3 :: events ++
        [PrepareSourceTarget edge write_target write_body; PrepareSourceTarget edge read_target
          read_body] ++
        map PrepareSourceMap reads ++ [PrepareSourceCase
          (match found with
           | Some _ => 4
           | None => 5
           end)] ++
        map PrepareSourceMap writes)
  end.

Fixpoint audit_prepare_source_in {V E B} (cb : audit_prepare_callback_model V E B)
    (nodes : list V) (initial : Map.t V (list E)) : Map.t V (list E) * list
      (audit_prepare_source_event V E B) :=
  match nodes with
  | [] => (initial, [PrepareSourceCase 6])
  | v :: rest => let '(middle, later) := audit_prepare_source_in cb rest initial in
      let '(outgoing, body) := audit_prepare_out_model cb v in
      let '(result, edges) := audit_prepare_source_edges cb outgoing middle in
      (result, PrepareSourceCase 7 :: later ++ [PrepareSourceOut v outgoing body] ++ edges)
  end.

Fixpoint audit_prepare_source_edge_count {V E B} (cb : audit_prepare_callback_model V E B)
    (nodes : list V) : nat * list (audit_prepare_source_event V E B) :=
  match nodes with
  | [] => (0, [PrepareSourceCase 8])
  | v :: rest => let '(later, events) := audit_prepare_source_edge_count cb rest in
      let '(outgoing, body) := audit_prepare_out_model cb v in
      (length outgoing + later, PrepareSourceCase 9 :: events ++
        [PrepareSourceOut v outgoing body; PrepareSourceLength (length outgoing)])
  end.

Definition audit_prepare_source_counted {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) : prepared EV g * list (audit_prepare_source_event V
      E B) :=
  let '(outgoing, out_events) := audit_prepare_source_out cb (Graph.nodes g) Map.empty in
  let '(incoming, in_events) := audit_prepare_source_in cb (Graph.nodes g) Map.empty in
  let nodes := length (Graph.nodes g) in
  let '(edges, edge_events) := audit_prepare_source_edge_count cb (Graph.nodes g) in
  let fuel := Pos.of_succ_nat (2 * nodes + edges + 1) in
  (Prepared outgoing incoming fuel, out_events ++ in_events ++ [PrepareSourceLength nodes] ++
    edge_events ++
    [PrepareSourceFuel nodes edges fuel]).

Definition audit_prepare_source_event_work {V E B} (weight : B -> nat) (event :
  audit_prepare_source_event V E B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 +
  match event with
  | PrepareSourceOut _ _ events
  | PrepareSourceTarget _ _ events => body events
  | PrepareSourceMap item => audit_map_source_work body [item]
  | PrepareSourceLength n => 2 * S n
  | PrepareSourceFuel nodes edges fuel =>
      let amount := 2 * nodes + edges + 1 in
      32 * S amount * S amount + audit_unary_conversion_weight amount + amount * Pos.size_nat fuel
  | PrepareSourceCase _ => 0
  end.

Definition audit_prepare_source_body_event_work {V E B} (weight : B -> nat)
    (event : audit_prepare_source_event V E B) : nat :=
  match event with
  | PrepareSourceOut _ _ body
  | PrepareSourceTarget _ _ body
  | PrepareSourceMap (AuditMapGet _ _ _ _ body _)
  | PrepareSourceMap (AuditMapSet _ _ _ _ _ body
      _) |
    PrepareSourceMap (AuditMapRemove _ _ _ _ body _) => fold_right (fun item n => weight item + n)
      0 body
  | PrepareSourceCase _
  | PrepareSourceLength _
  | PrepareSourceFuel _ _ _ => 0
  end.

Definition audit_prepare_source_work {V E B} (weight : B -> nat) (events : list
  (audit_prepare_source_event V E B)) : nat :=
  fold_right (fun item n => audit_prepare_source_event_work weight item + n) 0 events.

Definition audit_prepare_source_body_work {V E B} (weight : B -> nat) (events : list
  (audit_prepare_source_event V E B)) : nat :=
  fold_right (fun item n => audit_prepare_source_body_event_work weight item + n) 0 events.

Definition audit_prepare_source_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let count := audit_graph_prepare_full_event_bound g in
  let width := audit_graph_prepare_input_width EV g in
  let amount := 2 * length (Graph.nodes g) + edge_count g + 1 in
  1024 * S count * S count + count * (512 + 64 * width) +
    64 * S amount * S amount + amount * Pos.size_nat (Pos.of_succ_nat amount).

(** Source preparation returns the prepared graph with bounded events and work. *)
Definition audit_prepare_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_prepare_callback_model V E B)
    (weight : B -> nat),
    audit_prepare_callbacks_erase EV g cb ->
    let '(result, events) := audit_prepare_source_counted EV g cb in
    result = prepare EV g /\ length events <= audit_graph_prepare_full_event_bound g /\
    audit_prepare_source_work weight events <= audit_prepare_source_budget EV g +
      audit_prepare_source_body_work weight events.

Definition audit_prepare_source_event_budget {V E B} (encode_budget out_budget : V -> nat)
    (target_budget : E -> nat) (event : audit_prepare_source_event V E B) : nat :=
  match event with
  | PrepareSourceOut v _ _ => out_budget v
  | PrepareSourceTarget e _ _ => target_budget e
  | PrepareSourceMap (AuditMapGet key _ _ _ _ _)
  | PrepareSourceMap (AuditMapSet key _ _ _ _ _ _)
  | PrepareSourceMap (AuditMapRemove key _ _ _ _ _) => encode_budget key
  | PrepareSourceCase _
  | PrepareSourceLength _
  | PrepareSourceFuel _ _ _ => 0
  end.

(** Adapted preparation bounds external callback work by the supplied budgets. *)
Definition audit_prepare_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_prepare_callback_model V E B)
    (weight : B -> nat)
    encode_source out_source target_source encode_budget out_budget target_budget,
    audit_prepare_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_prepare_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_prepare_out_model cb) weight out_source
      out_budget ->
    audit_graph_external_callback_adapter (audit_prepare_target_model cb) weight target_source
      target_budget ->
    let '(result, events) := audit_prepare_source_counted EV g cb in
    result = prepare EV g /\
    audit_prepare_source_work weight events <= audit_prepare_source_budget EV g +
      fold_right (fun event n => audit_prepare_source_event_budget encode_budget out_budget
        target_budget event + n) 0 events.

(** The preparation source contract combines its primitive and source obligations. *)
Definition audit_prepare_source_contract_statement : Prop :=
  audit_prepare_source_statement /\ audit_prepare_source_adapted_statement /\
  audit_map_get_source_work_bound_statement /\ audit_map_set_source_work_bound_statement.
