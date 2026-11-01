(** * Weak topological order audit model

    Models source-level events, work, and associated contract statements.
    For example, choosing a component header records comparisons.

    Builds on: the graph and collections interfaces imported below. *)

From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsTrie CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphWto GraphAuditBase
  GraphAuditDfs GraphAuditScc.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditPrimitive
  CollectionsAuditCompare CollectionsAuditEncoding.
Import List.ListNotations.

Inductive audit_wto_call (V E : Type) : Type :=
  | AuditWtoCase (site : nat)
  | AuditWtoDfs (event : audit_dfs_full_call V E)
  | AuditWtoScc (event : audit_tarjan_call V E)
  | AuditWtoRead (v : V) (m : Map.t V positive) (result : option positive)
  | AuditWtoEdges (v : V) (m : Map.t V (list E)) (result : option (list E))
  | AuditWtoWrite (v : V) (value : positive) (m : Map.t V positive)
  | AuditWtoSucc (before after : positive)
  | AuditWtoLe (a b : positive) (result : bool)
  | AuditWtoEncode (v : V) (code : positive)
  | AuditWtoTarget (e : E) (v : V)
  | AuditWtoEqual (a b : positive) (result : bool)
  | AuditWtoDepth (length : nat) (depth : positive)
  | AuditWtoOutput (size : nat).
Arguments AuditWtoCase {V E} _.
Arguments AuditWtoDfs {V E} _.
Arguments AuditWtoScc {V E} _.
Arguments AuditWtoRead {V E} _ _ _.
Arguments AuditWtoEdges {V E} _ _ _.
Arguments AuditWtoWrite {V E} _ _ _.
Arguments AuditWtoSucc {V E} _ _.
Arguments AuditWtoLe {V E} _ _ _.
Arguments AuditWtoEncode {V E} _ _.
Arguments AuditWtoTarget {V E} _ _.
Arguments AuditWtoEqual {V E} _ _ _.
Arguments AuditWtoDepth {V E} _ _.
Arguments AuditWtoOutput {V E} _.

Fixpoint audit_wto_ranks_counted {V E} (EV : encoding V) (order : list V)
    (clock : positive) (m : Map.t V positive) : Map.t V positive * list (audit_wto_call V E) :=
  match order with
  | [] => (m, [AuditWtoCase 0])
  | v :: rest => let next_clock := Pos.succ clock in let next_map := Map.set EV v clock m in
      let '(result, events) := audit_wto_ranks_counted EV rest next_clock next_map in
      (result, AuditWtoCase 1 :: AuditWtoSucc clock next_clock :: AuditWtoWrite v clock m :: events)
  end.

Definition audit_wto_earlier_counted {V E} (EV : encoding V) (ranks : Map.t V positive) (u v : V)
    : V * list (audit_wto_call V E) :=
  let a := Map.get EV u ranks in let av :=
    match a with
    | Some n => n
    | None => 1%positive
    end in
  let b := Map.get EV v ranks in let bv :=
    match b with
    | Some n => n
    | None => 1%positive
    end in
  let choose := Pos.leb av bv in
  (if choose then u else v, [AuditWtoRead u ranks a; AuditWtoRead v ranks b; AuditWtoLe av bv
    choose]).

Fixpoint audit_wto_choose_counted {V E} (EV : encoding V) (ranks : Map.t V positive)
    (rest : list V) (header : V) : V * list (audit_wto_call V E) :=
  match rest with
  | [] => (header, [AuditWtoCase 2])
  | v :: tail => let '(next, here) := audit_wto_earlier_counted EV ranks header v in
      let '(result, later) := audit_wto_choose_counted EV ranks tail next in
      (result, AuditWtoCase 3 :: here ++ later)
  end.

Fixpoint audit_wto_remove_counted {V E} (EV : encoding V) (header : V) (vertices : list V)
    : list V * list (audit_wto_call V E) :=
  match vertices with
  | [] => ([], [AuditWtoCase 4])
  | v :: rest => let h := encode EV header in let k := encode EV v in let eq := Pos.eqb h k in
      let '(tail, later) := audit_wto_remove_counted EV header rest in
      (if eq then tail else v :: tail,
       AuditWtoCase 5 :: AuditWtoEncode header h :: AuditWtoEncode v k :: AuditWtoEqual h k eq ::
         later)
  end.

Fixpoint audit_wto_self_edges {V E} (EV : encoding V) (g : Graph.t V E) (v : V) (edges : list E)
    : bool * list (audit_wto_call V E) :=
  match edges with
  | [] => (false, [AuditWtoCase 6])
  | edge :: rest => let a := encode EV v in let target := Graph.target g edge in
      let b := encode EV target in let eq := Pos.eqb a b in
      let '(later, events) := audit_wto_self_edges EV g v rest in
      (eq || later, AuditWtoCase 7 :: AuditWtoEncode v a :: AuditWtoTarget edge target ::
        AuditWtoEncode target b :: AuditWtoEqual a b eq :: events)
  end.

Definition audit_wto_component_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (ranks : Map.t V positive) (recur : list V -> wto V * list (audit_wto_call
      V E))
    (component : list V) : wto V * list (audit_wto_call V E) :=
  match component with
  | [] => ([], [AuditWtoCase 8])
  | h :: rest => let '(header, choose_events) := audit_wto_choose_counted EV ranks rest h in
    match rest with
    | [] => let outgoing := Map.get EV h (out_index p) in
        let edges :=
          match outgoing with
          | Some xs => xs
          | None => []
          end in
        let '(self, events) := audit_wto_self_edges EV g h edges in
        (if self then [WOpen h; WClose] else [WVertex h],
         AuditWtoCase 9 :: choose_events ++ AuditWtoCase 10 :: AuditWtoEdges h (out_index p)
           outgoing ::
           events ++ [AuditWtoOutput (if self then 2 else 1)])
    | _ :: _ => let '(smaller, remove_events) := audit_wto_remove_counted EV header component in
        let '(inside, events) := recur smaller in
        (WOpen header :: inside ++ [WClose], AuditWtoCase 9 :: choose_events ++ AuditWtoCase 11 ::
          remove_events ++ events ++ [AuditWtoOutput (2 + length inside)])
    end
  end.

Fixpoint audit_wto_components_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (ranks : Map.t V positive) (recur : list V -> wto V * list (audit_wto_call
      V E))
    (components : list (list V)) : wto V * list (audit_wto_call V E) :=
  match components with
  | [] => ([], [AuditWtoCase 12])
  | component :: rest => let '(first, here) := audit_wto_component_counted p ranks recur component
    in
      let '(later, events) := audit_wto_components_counted p ranks recur rest in
      (first ++ later, AuditWtoCase 13 :: here ++ events ++ [AuditWtoOutput (length first)])
  end.

Definition audit_wto_layer_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (ranks : Map.t V positive) (recur : list V -> wto V * list (audit_wto_call
      V E))
    (region : list V) : wto V * list (audit_wto_call V E) :=
  let '(sccs, scc_events) := audit_scc_within_counted p region in
  let '(result, events) := audit_wto_components_counted p ranks recur (rev (components sccs)) in
  (result, map AuditWtoScc scc_events ++ [AuditWtoOutput (length (components sccs))] ++ events).

Definition audit_wto_iter_event {V E} (event : audit_comb_event (audit_wto_call V E)) :
  audit_wto_call V E :=
  match event with
  | AuditCombCase site => AuditWtoCase (20 + site)
  | AuditCombBody body => body
  end.

Definition audit_wto_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : wto V * list (audit_wto_call V E) :=
  let '(search, dfs_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let order := rpo search in
  let '(ranks, rank_events) := audit_wto_ranks_counted EV order 1%positive Map.empty in
  let depth := Pos.of_succ_nat (length order) in
  let base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_call V E)) in
  let step := fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)) in
  let '(run, iter_events) := audit_pos_iter step base depth in
  let '(result, events) := run order in
  (result, map AuditWtoDfs dfs_events ++ [AuditWtoOutput (length (postorder search))] ++
    rank_events ++ [AuditWtoDepth (length order) depth] ++ map audit_wto_iter_event iter_events ++
      events ++ [AuditWtoOutput (length result)]).

Definition audit_wto_event_work {V E} (EV : encoding V) (event : audit_wto_call V E) : nat :=
  64 +
  match event with
  | AuditWtoDfs item => audit_dfs_full_model_event EV item
  | AuditWtoScc item => audit_tarjan_event_work EV item
  | AuditWtoRead v _ _
  | AuditWtoEdges v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditWtoWrite v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditWtoSucc a _ => audit_binary_weight (Z.pos a) 1
  | AuditWtoLe a b _
  | AuditWtoEqual a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | AuditWtoEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditWtoOutput size => S size
  | AuditWtoDepth len depth => audit_unary_conversion_weight len + len * audit_key_bits_weight depth
  | _ => 0
  end.

Definition audit_wto_model_work {V E} (EV : encoding V) (events : list (audit_wto_call V E)) : nat
  :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_wto_event_work EV event + total) 0 events.

Definition audit_wto_input_order_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat := length (Graph.entries g) * S (Pos.to_nat (fuel p)).

Definition audit_wto_input_max_out {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat :=
  fold_right (fun row n => Nat.max (length (snd row)) n) 0 (Map.elements (out_index p)).

Definition audit_wto_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat :=
  let n := audit_wto_input_order_bound p in
  let f := S (Pos.to_nat (fuel p)) in
  let m := audit_wto_input_max_out p in
  let scc_bound := (3 + n * (12 + 12 * f)) * (12 + 6 * S (n * f)) in
  1024 * Nat.pow (S n) (S n) * Nat.pow (S (scc_bound + n * (m + n) + f)) 3.

Definition audit_wto_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let n := audit_wto_input_order_bound p in
  let events := audit_wto_input_event_bound p in
  let width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (audit_key_bits_weight (Pos.of_succ_nat (2 + n * S (Pos.to_nat (fuel p))))) in
  1024 * S events * S events + events * (512 + 24 * width).

(** Counted WTO construction returns the WTO with bounded events and work. *)

Definition audit_wto_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    let '(result, events) := audit_wto_counted p in
    result = wto_of p /\
    length events <= audit_wto_input_event_bound p /\
    audit_wto_model_work EV events <= audit_wto_input_budget EV g p.

Definition audit_wto_nested_event (V E B : Type) : Type := audit_wto_call V E * list B.

Fixpoint audit_wto_nested_ranks {V E B} (cb : audit_dfs_callback_model V E B) (order : list V)
    (clock : positive) (m : Map.t V positive) : Map.t V positive * list (audit_wto_nested_event V
      E B) :=
  match order with
  | [] => (m, [(AuditWtoCase 0, [])])
  | v :: rest => let next_clock := Pos.succ clock in
      let '(next_map, body) := audit_tarjan_nested_set cb v clock m in
      let '(result, events) := audit_wto_nested_ranks cb rest next_clock next_map in
      (result, (AuditWtoCase 1, []) :: (AuditWtoSucc clock next_clock, []) :: (AuditWtoWrite v
        clock m, body) :: events)
  end.

Definition audit_wto_nested_earlier {V E B} (cb : audit_dfs_callback_model V E B)
    (ranks : Map.t V positive) (u v : V) : V * list (audit_wto_nested_event V E B) :=
  let '(a, a_body) := audit_tarjan_nested_get cb u ranks in
  let av :=
    match a with
    | Some n => n
    | None => 1%positive
    end in
  let '(b, b_body) := audit_tarjan_nested_get cb v ranks in
  let bv :=
    match b with
    | Some n => n
    | None => 1%positive
    end in let choose := Pos.leb av bv in
  (if choose then u else v, [(AuditWtoRead u ranks a, a_body); (AuditWtoRead v ranks b, b_body);
    (AuditWtoLe av bv choose, [])]).

Fixpoint audit_wto_nested_choose {V E B} (cb : audit_dfs_callback_model V E B)
    (ranks : Map.t V positive) (rest : list V) (header : V) : V * list (audit_wto_nested_event V E
      B) :=
  match rest with
  | [] => (header, [(AuditWtoCase 2, [])])
  | v :: tail => let '(next, here) := audit_wto_nested_earlier cb ranks header v in
      let '(result, later) := audit_wto_nested_choose cb ranks tail next in
      (result, (AuditWtoCase 3, []) :: here ++ later)
  end.

Fixpoint audit_wto_nested_remove {V E B} (cb : audit_dfs_callback_model V E B) (header : V)
  (vertices : list V)
    : list V * list (audit_wto_nested_event V E B) :=
  match vertices with
  | [] => ([], [(AuditWtoCase 4, [])])
  | v :: rest => let '(h, h_body) := audit_dfs_encode_model cb header in
      let '(k, k_body) := audit_dfs_encode_model cb v in let equal := Pos.eqb h k in
      let '(tail, later) := audit_wto_nested_remove cb header rest in
      (if equal then tail else v :: tail, [(AuditWtoCase 5, []); (AuditWtoEncode header h, h_body);
        (AuditWtoEncode v k, k_body); (AuditWtoEqual h k equal, [])] ++ later)
  end.

Fixpoint audit_wto_nested_self_edges {V E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (edges : list E) : bool * list (audit_wto_nested_event V E B) :=
  match edges with
  | [] => (false, [(AuditWtoCase 6, [])])
  | edge :: rest => let '(a, a_body) := audit_dfs_encode_model cb v in
      let '(target, target_body) := audit_dfs_target_model cb edge in
      let '(b, b_body) := audit_dfs_encode_model cb target in let equal := Pos.eqb a b in
      let '(later, events) := audit_wto_nested_self_edges cb v rest in
      (equal || later, [(AuditWtoCase 7, []); (AuditWtoEncode v a, a_body); (AuditWtoTarget edge
        target, target_body);
        (AuditWtoEncode target b, b_body); (AuditWtoEqual a b equal, [])] ++ events)
  end.

Definition audit_wto_nested_component {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (ranks : Map.t V positive)
    (recur : list V -> wto V * list (audit_wto_nested_event V E B)) (component : list V)
    : wto V * list (audit_wto_nested_event V E B) :=
  match component with
  | [] => ([], [(AuditWtoCase 8, [])])
  | h :: rest => let '(header, choose_events) := audit_wto_nested_choose cb ranks rest h in
    match rest with
    | [] => let '(outgoing, out_body) := audit_tarjan_nested_get cb h (out_index p) in
        let edges :=
          match outgoing with
          | Some xs => xs
          | None => []
          end in
        let '(self, events) := audit_wto_nested_self_edges cb h edges in
        (if self then [WOpen h; WClose] else [WVertex h],
         (AuditWtoCase 9, []) :: choose_events ++ [(AuditWtoCase 10, []); (AuditWtoEdges h
           (out_index p) outgoing, out_body)] ++
           events ++ [(AuditWtoOutput (if self then 2 else 1), [])])
    | _ :: _ => let '(smaller, remove_events) := audit_wto_nested_remove cb header component in
        let '(inside, events) := recur smaller in
        (WOpen header :: inside ++ [WClose], (AuditWtoCase 9, []) :: choose_events ++
          [(AuditWtoCase 11, [])] ++
          remove_events ++ events ++ [(AuditWtoOutput (2 + length inside), [])])
    end
  end.

Fixpoint audit_wto_nested_components {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (ranks : Map.t V positive)
    (recur : list V -> wto V * list (audit_wto_nested_event V E B)) (components : list (list V))
    : wto V * list (audit_wto_nested_event V E B) :=
  match components with
  | [] => ([], [(AuditWtoCase 12, [])])
  | component :: rest => let '(first, here) := audit_wto_nested_component p cb ranks recur
    component in
      let '(later, events) := audit_wto_nested_components p cb ranks recur rest in
      (first ++ later, (AuditWtoCase 13, []) :: here ++ events ++ [(AuditWtoOutput (length first),
        [])])
  end.

Definition audit_wto_nested_layer {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (ranks : Map.t V positive)
    (recur : list V -> wto V * list (audit_wto_nested_event V E B)) (region : list V)
    : wto V * list (audit_wto_nested_event V E B) :=
  let '(sccs, scc_events) := audit_scc_within_nested_counted p cb region in
  let '(result, events) := audit_wto_nested_components p cb ranks recur (rev (components sccs)) in
  (result, map (fun item => (AuditWtoScc (fst item), snd item)) scc_events ++
    [(AuditWtoOutput (length (components sccs)), [])] ++ events).

Definition audit_wto_nested_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : wto V * list (audit_wto_nested_event V E B) :=
  let '(search, dfs_events) := audit_dfs_nested_counted p cb FinSet.empty (Graph.entries g) in
  let order := rpo search in let '(ranks, rank_events) := audit_wto_nested_ranks cb order
    1%positive Map.empty in
  let depth := Pos.of_succ_nat (length order) in
  let base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_nested_event V E B)) in
  let step := fun recur => (audit_wto_nested_layer p cb ranks recur, @nil (audit_wto_call V E)) in
  let '(run, iter_events) := audit_pos_iter step base depth in let '(result, events) := run order in
  (result, map (fun item => (AuditWtoDfs (fst item), snd item)) dfs_events ++
    [(AuditWtoOutput (length (postorder search)), [])] ++ rank_events ++ [(AuditWtoDepth (length
      order) depth, [])] ++
    map (fun e => (audit_wto_iter_event e, [])) iter_events ++ events ++ [(AuditWtoOutput (length
      result), [])]).

Definition audit_wto_nested_body_work {V E B} (weight : B -> nat) (events : list
  (audit_wto_nested_event V E B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd event) + total)
    0 events.

Definition audit_wto_nested_total_work {V E B} (EV : encoding V) (weight : B -> nat)
    (events : list (audit_wto_nested_event V E B)) : nat :=
  audit_wto_model_work EV (map fst events) + audit_wto_nested_body_work weight events.

(** Nested WTO construction erases to the counted trace and bounds total work. *)
Definition audit_wto_nested_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_wto_nested_counted p cb in
    result = wto_of p /\ map fst events = snd (audit_wto_counted p) /\
    length events <= audit_wto_input_event_bound p /\
    audit_wto_nested_total_work EV weight events <= audit_wto_input_budget EV g p +
      audit_wto_nested_body_work weight events.

Definition audit_wto_source_layer {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (ranks : Map.t V positive)
    (recur : list V -> wto V * list (audit_wto_nested_event V E (audit_graph_callback_capture V E
      B)))
    (region : list V) : wto V * list (audit_wto_nested_event V E (audit_graph_callback_capture V E
      B)) :=
  let '(sccs, scc_events) := audit_scc_source_counted p cb region in
  let '(result, events) := audit_wto_nested_components p (audit_graph_capture_callbacks cb) ranks
    recur
    (rev_append (components sccs) []) in
  (result, map (fun item => (AuditWtoScc (fst item), snd item)) scc_events ++
    [(AuditWtoOutput (length (components sccs)), [])] ++ events).

Definition audit_wto_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : wto V * list (audit_wto_nested_event V E (audit_graph_callback_capture V E B)) :=
  let '(search, dfs_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let order := rev_append (postorder search) [] in
  let captured := audit_graph_capture_callbacks cb in
  let '(ranks, rank_events) := audit_wto_nested_ranks captured order 1%positive Map.empty in
  let depth := Pos.of_succ_nat (length order) in
  let base := fun _ : list V => (@nil (wto_token V),
    @nil (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) in
  let step := fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)) in
  let '(run, iter_events) := audit_pos_iter step base depth in let '(result, events) := run order in
  (result, map (fun item => (AuditWtoDfs (fst item), snd item)) dfs_events ++
    [(AuditWtoOutput (length (postorder search)), [])] ++ rank_events ++ [(AuditWtoDepth (length
      order) depth, [])] ++
    map (fun event => (audit_wto_iter_event event, [])) iter_events ++ events ++ [(AuditWtoOutput
      (length result), [])]).

Definition audit_wto_source_event_work {V E B} (weight : B -> nat)
    (item : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : nat :=
  let '(event, body) := item in let code := audit_dfs_source_code body in
  let callback := fold_right (fun event n => audit_graph_capture_work weight event + n) 0 body in
  match event with
  | AuditWtoDfs event => 64 + audit_dfs_source_event_work weight (event, body)
  | AuditWtoScc event => 64 + audit_scc_source_event_work weight (event, body)
  | AuditWtoRead _ input _ => 69 + callback + audit_trie_get_source_work code input
  | AuditWtoEdges _ input _ => 69 + callback + audit_trie_get_source_work code input
  | AuditWtoWrite v value input => 66 + callback + audit_trie_update_source_work code (Some (v,
    value)) input
  | AuditWtoSucc before _ => 64 + callback + 2 * Pos.size_nat before
  | AuditWtoLe a b _
  | AuditWtoEqual a b _ => 68 + callback + 2 * Nat.min (Pos.size_nat a)
    (Pos.size_nat b)
  | AuditWtoDepth n depth => 64 + callback + audit_unary_conversion_weight n + 2 * S n * S
    (Pos.size_nat depth)
  | AuditWtoOutput n => 64 + callback + audit_graph_reverse_fast_work n + S n
  | AuditWtoCase _
  | AuditWtoEncode _ _
  | AuditWtoTarget _ _ => 64 + callback
  end.

Definition audit_wto_source_work {V E B} (weight : B -> nat)
    (events : list (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun event n => audit_wto_source_event_work weight event + n) 0 events.

Definition audit_wto_source_body_work {V E B} (weight : B -> nat)
    (events : list (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_graph_capture_work weight event + k)
    0 (snd item) + n) 0 events.

Definition audit_wto_source_budget {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  nat :=
  let count := audit_wto_input_event_bound p in
  let width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Pos.size_nat (Pos.of_succ_nat (2 + audit_wto_input_order_bound p * S (Pos.to_nat (fuel p)))))
      in
  4096 * Nat.pow (S count) 3 + count * (1024 + 128 * width).

(** Source WTO construction returns the WTO with bounded events and work. *)
Definition audit_wto_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_wto_source_counted p cb in
    result = wto_of p /\ length events <= audit_wto_input_event_bound p /\
    audit_wto_source_work weight events <= audit_wto_source_budget EV g p +
      audit_wto_source_body_work weight events.

Definition audit_wto_source_external_budget {V E B} (encode_budget : V -> nat) (target_budget : E
  -> nat)
    (events : list (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_scc_capture_budget encode_budget
    target_budget event + k)
    0 (snd item) + n) 0 events.

(** A WTO source event carries the matching callback captures. *)
Definition audit_wto_source_event_wellformed {V E B}
    (item : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditWtoDfs nested => audit_dfs_source_event_wellformed (nested, body)
  | AuditWtoScc nested => audit_scc_source_event_wellformed (nested, body)
  | AuditWtoRead v _ _
  | AuditWtoEdges v _ _
  | AuditWtoWrite v _ _ =>
      exists code trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditWtoEncode v code => exists trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditWtoTarget edge v => exists trace, body = [AuditGraphTargetCapture V E B edge v trace]
  | _ => body = []
  end.

(** A WTO source event agrees with its corresponding primitive result. *)
Definition audit_wto_source_event_primitive {V E B}
    (item : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditWtoDfs nested => audit_dfs_source_successor_event (nested, body)
  | AuditWtoScc nested => audit_scc_source_event_primitive (nested, body)
  | AuditWtoSucc before after => fst (audit_positive_succ before) = after
  | AuditWtoLe a b result => fst (audit_positive_leb a b) = result
  | AuditWtoEqual a b result => fst (audit_positive_eqb a b) = result
  | AuditWtoDepth size depth => fst (audit_nat_encode size) = depth
  | _ => True
  end.

(** Every WTO source event is well formed and satisfies primitive correspondence. *)
Definition audit_wto_source_event_correspondence_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B), audit_dfs_callbacks_erase EV g cb ->
    let '(_, events) := audit_wto_source_counted p cb in
    Forall audit_wto_source_event_wellformed events /\ Forall audit_wto_source_event_primitive
      events.

(** Adapted WTO construction bounds external callback work by the supplied budgets. *)
Definition audit_wto_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) encode_source target_source
      encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    let '(result, events) := audit_wto_source_counted p cb in
    result = wto_of p /\ audit_wto_source_work weight events <= audit_wto_source_budget EV g p +
      audit_wto_source_external_budget encode_budget target_budget events.

(** The WTO source contract combines its primitive and source obligations. *)
Definition audit_wto_source_contract_statement : Prop :=
  audit_wto_source_statement /\ audit_wto_source_adapted_statement /\
    audit_scc_source_contract_statement /\
  audit_dfs_source_contract_statement /\ audit_graph_reverse_fast_counted_statement /\
  audit_nat_encode_run_total_statement /\ audit_nat_encode_run_correct_statement /\
  audit_positive_order_statement /\ audit_wto_source_event_correspondence_statement.
