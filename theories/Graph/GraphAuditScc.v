(** * Strongly connected component audit model

    Models source-level events, work, and associated contract statements.
    For example, Tarjan traversal records stack and map operations.

    Builds on: the graph and collections interfaces imported below. *)

From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.
From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsTrie
  CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditPrimitive
  CollectionsAuditCompare CollectionsAuditEncoding.
Import List.ListNotations.

Inductive audit_thelper_event (V E : Type) : Type :=
  | THCase (site : nat)
  | THGet (key : V) (m : Map.t V positive) (result : option positive)
  | THGetEdges (key : V) (m : Map.t V (list E)) (result : option (list E))
  | THSet (key : V) (value : positive) (m : Map.t V positive)
  | THRemove (key : V) (m : Map.t V positive)
  | THCompare (left right : V) (result : bool)
  | THPosCompare (left right : positive) (result : bool)
  | THMin (left right result : positive)
  | THSucc (input result : positive)
  | THTrieSet (key : positive) (members : list V) (m : Trie.t (list V)).
Arguments THCase {V E} _.
Arguments THGet {V E} _ _ _.
Arguments THGetEdges {V E} _ _ _.
Arguments THSet {V E} _ _ _.
Arguments THRemove {V E} _ _.
Arguments THCompare {V E} _ _ _.
Arguments THPosCompare {V E} _ _ _.
Arguments THMin {V E} _ _ _.
Arguments THSucc {V E} _ _.
Arguments THTrieSet {V E} _ _ _.

Definition audit_tarjan_discover_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (v : V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_thelper_event V E) :=
  let adjacent := Map.get EV v (out_index p) in
  let edges :=
    match adjacent with
    | Some xs => xs
    | None => []
    end in
  let d := Map.set EV v (clock st) (disc st) in
  let l := Map.set EV v (clock st) (low st) in
  let next := Pos.succ (clock st) in
  (TarjanState (TarjanFrame v edges :: frames st) d l
    (v :: pending st) next (emitted st),
   [THGetEdges v (out_index p) adjacent; THSet v (clock st) (disc st);
    THSet v (clock st) (low st); THSucc (clock st) next]).

Definition audit_tarjan_lower_counted {V E} (EV : encoding V) (v : V) (n : positive)
    (st : tarjan_state V E) : tarjan_state V E * list (audit_thelper_event V E) :=
  let found := Map.get EV v (low st) in
  match found with
  | None => (st, [THGet v (low st) found; THCase 0])
  | Some old => let minimum := Pos.min old n in
      let next := TarjanState (frames st) (disc st) (Map.set EV v minimum (low st))
        (pending st) (clock st) (emitted st) in
      (next, [THGet v (low st) found; THCase 1; THMin old n minimum;
        THSet v minimum (low st)])
  end.

Fixpoint audit_tarjan_pop_counted {V E} (EV : encoding V) (root : V) (i : positive)
    (xs : list V) (links owners : Map.t V positive)
    : (list V * list V * Map.t V positive * Map.t V positive) * list (audit_thelper_event V E) :=
  match xs with
  | [] => (([], [], links, owners), [THCase 2])
  | v :: rest =>
      let links' := Map.remove EV v links in
      let owners' := Map.set EV v i owners in
      let equal := Pos.eqb (encode EV v) (encode EV root) in
      if equal then
        (([v], rest, links', owners'),
         [THCase 3; THRemove v links; THSet v i owners; THCompare v root equal; THCase 4])
      else
        let '(answer, later) := audit_tarjan_pop_counted EV root i rest links' owners' in
        let '(members, tail, links'', owners'') := answer in
        ((v :: members, tail, links'', owners''),
         [THCase 3; THRemove v links; THSet v i owners; THCompare v root equal; THCase 5] ++ later)
  end.

Definition audit_tarjan_emit_counted {V E} (EV : encoding V) (root : V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_thelper_event V E) :=
  let r := emitted st in
  let '(i, id_events) :=
    match component_ids r with
    | [] => (1%positive, [THCase 6])
    | previous :: _ => let next := Pos.succ previous in (next, [THCase 7; THSucc previous next])
    end in
  let '(answer, pop_events) := audit_tarjan_pop_counted EV root i (pending st) (low st) (comp_of
    r) in
  let '(members, tail, links, owners) := answer in
  let component_map := Trie.set i members (component_at r) in
  (TarjanState (frames st) (disc st) links tail (clock st)
    (SccResult (members :: components r) (i :: component_ids r) component_map owners),
   id_events ++ pop_events ++ [THTrieSet i members (component_at r)]).

Definition audit_tarjan_close_counted {V E} (EV : encoding V) (v : V)
    (rest : list (tarjan_frame V E)) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_thelper_event V E) :=
  let closed := TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st) in
  let lo := Map.get EV v (low st) in
  match lo with
  | None => (closed, [THGet v (low st) lo; THCase 8])
  | Some l => let di := Map.get EV v (disc st) in
    match di with
    | None => (closed, [THGet v (low st) lo; THGet v (disc st) di; THCase 9])
    | Some d => let eq := Pos.eqb l d in
      if eq then let '(next, events) := audit_tarjan_emit_counted EV v closed in
        (next, [THGet v (low st) lo; THGet v (disc st) di; THPosCompare l d eq; THCase 10] ++
          events)
      else
        match rest with
        | [] => (closed, [THGet v (low st) lo; THGet v (disc st) di; THPosCompare l d eq; THCase
          11])
        | parent :: _ => let '(next, events) := audit_tarjan_lower_counted EV (frame_node parent)
          l closed in
            (next, [THGet v (low st) lo; THGet v (disc st) di; THPosCompare l d eq; THCase 12] ++
              events)
        end
    end
  end.

Definition audit_thelper_event_work {V E} (EV : encoding V) (event : audit_thelper_event V E) :
  nat :=
  let enc v := audit_encoding_weight (audit_key_bits_weight (encode EV v)) in
  64 +
  match event with
  | THGet v _ _
  | THGetEdges v _ _ => enc v + audit_get_weight (encode EV v)
  | THSet v _ _ => enc v + audit_set_weight (encode EV v)
  | THRemove v _ => enc v + audit_remove_weight (encode EV v)
  | THCompare a b _ => enc a + enc b + audit_binary_weight (Z.pos (encode EV a)) (Z.pos (encode EV
    b))
  | THPosCompare a b _
  | THMin a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | THSucc a _ => audit_binary_weight (Z.pos a) 1
  | THTrieSet key _ _ => audit_set_weight key
  | THCase _ => 0
  end.

Definition audit_thelper_work {V E} (EV : encoding V) (events : list (audit_thelper_event V E)) :
  nat :=
  fold_right (fun event total => audit_thelper_event_work EV event + total) 0 events.

(** Counted Tarjan helpers erase to the original helper results. *)

Definition audit_tarjan_helpers_erasure_statement : Prop :=
  (forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) v st,
    fst (audit_tarjan_discover_counted p v st) = tarjan_discover p v st) /\
  (forall V E (EV : encoding V) v n (st : tarjan_state V E),
    fst (audit_tarjan_lower_counted EV v n st) = tarjan_lower EV v n st) /\
  (forall V E (EV : encoding V) root i xs links owners,
    fst (@audit_tarjan_pop_counted V E EV root i xs links owners) = tarjan_pop EV root i xs links
      owners) /\
  (forall V E (EV : encoding V) root (st : tarjan_state V E),
    fst (audit_tarjan_emit_counted EV root st) = tarjan_emit EV root st) /\
  (forall V E (EV : encoding V) v rest (st : tarjan_state V E),
    fst (audit_tarjan_close_counted EV v rest st) = tarjan_close EV v rest st).

(** Counted Tarjan helper traces obey their stated event bounds. *)
Definition audit_tarjan_helpers_event_bound_statement : Prop :=
  (forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) v st,
    length (snd (audit_tarjan_discover_counted p v st)) = 4) /\
  (forall V E (EV : encoding V) v n (st : tarjan_state V E),
    length (snd (audit_tarjan_lower_counted EV v n st)) <= 4) /\
  (forall V E (EV : encoding V) root i xs links owners,
    length (snd (@audit_tarjan_pop_counted V E EV root i xs links owners)) <= 1 + 5 * length xs) /\
  (forall V E (EV : encoding V) root (st : tarjan_state V E),
    length (snd (audit_tarjan_emit_counted EV root st)) <= 4 + 5 * length (pending st)) /\
  (forall V E (EV : encoding V) v rest (st : tarjan_state V E),
    length (snd (audit_tarjan_close_counted EV v rest st)) <= 8 + 5 * length (pending st)).

Inductive audit_tarjan_call (V E : Type) : Type :=
  | AuditTarjanCase (site : nat)
  | AuditTarjanTarget (edge : E) (target : V)
  | AuditTarjanMember (v : V) (region : FinSet.t V) (result : bool)
  | AuditTarjanGet (v : V) (map : Map.t V positive) (result : option positive)
  | AuditTarjanDiscover (v : V) (before after : tarjan_state V E)
  | AuditTarjanLower (v : V) (n : positive) (before after : tarjan_state V E)
  | AuditTarjanClose (v : V) (rest : list (tarjan_frame V E)) (before after : tarjan_state V E)
  | AuditTarjanHelper (event : audit_thelper_event V E)
  | AuditTarjanSet (v : V) (before : FinSet.t V)
  | AuditTarjanOutput (components identifiers : nat).
Arguments AuditTarjanCase {V E} _.
Arguments AuditTarjanTarget {V E} _ _.
Arguments AuditTarjanMember {V E} _ _ _.
Arguments AuditTarjanGet {V E} _ _ _.
Arguments AuditTarjanDiscover {V E} _ _ _.
Arguments AuditTarjanLower {V E} _ _ _ _.
Arguments AuditTarjanClose {V E} _ _ _ _.
Arguments AuditTarjanHelper {V E} _.
Arguments AuditTarjanSet {V E} _ _.
Arguments AuditTarjanOutput {V E} _ _.

Definition audit_tarjan_step_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_call V E) :=
  match frames st with
  | [] => (st, [AuditTarjanCase 0])
  | TarjanFrame v [] :: rest =>
      let '(next, detail) := audit_tarjan_close_counted EV v rest st in
      (next, AuditTarjanCase 1 :: map AuditTarjanHelper detail ++ [AuditTarjanClose v rest st next])
  | TarjanFrame v (edge :: edges) :: rest =>
      let advanced := TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st) in
      let target := Graph.target g edge in
      let inside := FinSet.mem EV target region in
      if inside then
        let found := Map.get EV target (disc st) in
        match found with
        | None => let '(next, detail) := audit_tarjan_discover_counted p target advanced in
            (next, [AuditTarjanTarget edge target; AuditTarjanMember target region inside;
              AuditTarjanCase 2; AuditTarjanGet target (disc st) found] ++
              map AuditTarjanHelper detail ++ [AuditTarjanDiscover target advanced next])
        | Some d => let on_stack := Map.get EV target (low st) in
            match on_stack with
            | None => (advanced, [AuditTarjanTarget edge target; AuditTarjanMember target region
              inside;
                AuditTarjanCase 2; AuditTarjanGet target (disc st) found;
                AuditTarjanGet target (low st) on_stack; AuditTarjanCase 3])
            | Some _ => let '(next, detail) := audit_tarjan_lower_counted EV v d advanced in
                (next, [AuditTarjanTarget edge target; AuditTarjanMember target region inside;
                  AuditTarjanCase 2; AuditTarjanGet target (disc st) found;
                  AuditTarjanGet target (low st) on_stack; AuditTarjanCase 4] ++
                  map AuditTarjanHelper detail ++ [AuditTarjanLower v d advanced next])
            end
        end
      else (advanced, [AuditTarjanTarget edge target; AuditTarjanMember target region inside;
        AuditTarjanCase 5])
  end.

Fixpoint audit_tarjan_run_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (fuel : positive) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_call V E) :=
  match frames st with
  | [] => (st, [AuditTarjanCase 6])
  | _ :: _ =>
    match fuel with
    | xH => let '(result, events) := audit_tarjan_step_counted p region st in
        (result, AuditTarjanCase 7 :: events)
    | xO rest => let '(middle, first) := audit_tarjan_run_counted p region rest st in
        let '(result, second) := audit_tarjan_run_counted p region rest middle in
        (result, AuditTarjanCase 8 :: first ++ second)
    | xI rest => let '(middle, first) := audit_tarjan_run_counted p region rest st in
        let '(last, second) := audit_tarjan_run_counted p region rest middle in
        let '(result, steps) := audit_tarjan_step_counted p region last in
        (result, AuditTarjanCase 9 :: first ++ second ++ steps)
    end
  end.

Definition audit_tarjan_root_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (st : tarjan_state V E) (v : V)
    : tarjan_state V E * list (audit_tarjan_call V E) :=
  let found := Map.get EV v (disc st) in
  match found with
  | Some _ => (st, [AuditTarjanGet v (disc st) found; AuditTarjanCase 10])
  | None => let '(next, detail) := audit_tarjan_discover_counted p v st in
      let '(result, events) := audit_tarjan_run_counted p region (fuel p) next in
      (result, [AuditTarjanGet v (disc st) found; AuditTarjanCase 11] ++
        map AuditTarjanHelper detail ++ [AuditTarjanDiscover v st next] ++ events)
  end.

Fixpoint audit_tarjan_roots_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (roots : list V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_call V E) :=
  match roots with
  | [] => (st, [AuditTarjanCase 12])
  | root :: rest => let '(next, first) := audit_tarjan_root_counted p region st root in
      let '(result, later) := audit_tarjan_roots_counted p region rest next in
      (result, AuditTarjanCase 13 :: first ++ later)
  end.

Fixpoint audit_tarjan_region_counted {V E} (EV : encoding V) (region : list V) (set : FinSet.t V)
    : FinSet.t V * list (audit_tarjan_call V E) :=
  match region with
  | [] => (set, [AuditTarjanCase 14])
  | v :: rest => let next := FinSet.add EV v set in
      let '(result, events) := audit_tarjan_region_counted EV rest next in
      (result, AuditTarjanSet v set :: events)
  end.

Definition audit_scc_within_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : list V) : scc_result V * list (audit_tarjan_call V E) :=
  let '(keep, setup) := audit_tarjan_region_counted EV region FinSet.empty in
  let '(st, events) := audit_tarjan_roots_counted p keep region tarjan_initial in
  let r := emitted st in
  (tarjan_result st, setup ++ events ++ [AuditTarjanOutput (length (components r)) (length
    (component_ids r))]).

Definition audit_tarjan_event_work {V E} (EV : encoding V) (event : audit_tarjan_call V E) : nat :=
  64 +
  match event with
  | AuditTarjanMember v _ _
  | AuditTarjanGet v _ _ =>
      audit_get_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight (encode EV v))
  | AuditTarjanSet v _ => audit_set_weight (encode EV v) + audit_encoding_weight
    (audit_key_bits_weight (encode EV v))
  | AuditTarjanHelper nested => audit_thelper_event_work EV nested
  | AuditTarjanOutput a b => a + b
  | _ => 0
  end.

Definition audit_tarjan_model_work {V E} (EV : encoding V) (events : list (audit_tarjan_call V E))
  : nat :=
  64 * S (length events) * S (length events) +
    fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 events.

Definition audit_tarjan_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : list V) : nat :=
  let steps := length region * S (Pos.to_nat (fuel p)) in
  (3 + length region * (12 + 12 * S (Pos.to_nat (fuel p)))) * (12 + 6 * S steps).

Definition audit_tarjan_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (region : list V) : nat :=
  let events := audit_tarjan_input_event_bound p region in
  let width := Nat.max (audit_dfs_input_width EV g p region)
    (audit_key_bits_weight (Pos.of_succ_nat (2 + length region * S (Pos.to_nat (fuel p))))) in
  128 * S events * S events + events * (140 + 12 * width).

(** Counted SCC traversal returns SCCs with bounded events and work. *)
Definition audit_scc_within_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) region,
    let '(result, events) := audit_scc_within_counted p region in
    result = scc_within p region /\
    length events <= audit_tarjan_input_event_bound p region /\
    audit_tarjan_model_work EV events <= audit_tarjan_input_budget EV g p region.

Definition audit_tarjan_nested_event (V E B : Type) : Type := audit_tarjan_call V E * list B.

Definition audit_tarjan_nested_get {V E B A} (cb : audit_dfs_callback_model V E B) (v : V) (m :
  Map.t V A)
    : option A * list B := let '(code, body) := audit_dfs_encode_model cb v in (Map.code_get code
      m, body).

Definition audit_tarjan_nested_set {V E B A} (cb : audit_dfs_callback_model V E B) (v : V) (value
  : A) (m : Map.t V A)
    : Map.t V A * list B := let '(code, body) := audit_dfs_encode_model cb v in (Trie.set code (v,
      value) m, body).

Definition audit_tarjan_nested_remove {V E B A} (cb : audit_dfs_callback_model V E B) (v : V) (m :
  Map.t V A)
    : Map.t V A * list B := let '(code, body) := audit_dfs_encode_model cb v in (Trie.remove code
      m, body).

Definition audit_tarjan_nested_discover {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (v : V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  let '(adjacent, out_body) := audit_tarjan_nested_get cb v (out_index p) in
  let edges :=
    match adjacent with
    | Some xs => xs
    | None => []
    end in
  let '(d, d_body) := audit_tarjan_nested_set cb v (clock st) (disc st) in
  let '(l, l_body) := audit_tarjan_nested_set cb v (clock st) (low st) in
  let next := Pos.succ (clock st) in
  (TarjanState (TarjanFrame v edges :: frames st) d l (v :: pending st) next (emitted st),
   [(AuditTarjanHelper (THGetEdges v (out_index p) adjacent), out_body);
    (AuditTarjanHelper (THSet v (clock st) (disc st)), d_body);
    (AuditTarjanHelper (THSet v (clock st) (low st)), l_body);
    (AuditTarjanHelper (THSucc (clock st) next), [])]).

Definition audit_tarjan_nested_lower {V E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (n : positive) (st : tarjan_state V E) : tarjan_state V E * list
      (audit_tarjan_nested_event V E B) :=
  let '(found, get_body) := audit_tarjan_nested_get cb v (low st) in
  match found with
  | None => (st, [(AuditTarjanHelper (THGet v (low st) found), get_body); (AuditTarjanHelper
    (THCase 0), [])])
  | Some old => let minimum := Pos.min old n in
      let '(low_map, set_body) := audit_tarjan_nested_set cb v minimum (low st) in
      (TarjanState (frames st) (disc st) low_map (pending st) (clock st) (emitted st),
       [(AuditTarjanHelper (THGet v (low st) found), get_body); (AuditTarjanHelper (THCase 1), []);
        (AuditTarjanHelper (THMin old n minimum), []); (AuditTarjanHelper (THSet v minimum (low
          st)), set_body)])
  end.

Fixpoint audit_tarjan_nested_pop {V E B} (cb : audit_dfs_callback_model V E B) (root : V) (i :
  positive)
    (xs : list V) (links owners : Map.t V positive)
    : (list V * list V * Map.t V positive * Map.t V positive) * list (audit_tarjan_nested_event V
      E B) :=
  match xs with
  | [] => (([], [], links, owners), [(AuditTarjanHelper (THCase 2), [])])
  | v :: rest => let '(links', remove_body) := audit_tarjan_nested_remove cb v links in
      let '(owners', set_body) := audit_tarjan_nested_set cb v i owners in
      let '(v_code, v_body) := audit_dfs_encode_model cb v in
      let '(root_code, root_body) := audit_dfs_encode_model cb root in let equal := Pos.eqb v_code
        root_code in
      let head := [(AuditTarjanHelper (THCase 3), []); (AuditTarjanHelper (THRemove v links),
        remove_body);
        (AuditTarjanHelper (THSet v i owners), set_body); (AuditTarjanHelper (THCompare v root
          equal), v_body ++ root_body)] in
      if equal then (([v], rest, links', owners'), head ++ [(AuditTarjanHelper (THCase 4), [])])
      else let '(answer, later) := audit_tarjan_nested_pop cb root i rest links' owners' in
        let '(members, tail, links'', owners'') := answer in
        ((v :: members, tail, links'', owners''), head ++ [(AuditTarjanHelper (THCase 5), [])] ++
          later)
  end.

Definition audit_tarjan_nested_emit {V E B} (cb : audit_dfs_callback_model V E B) (root : V) (st :
  tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  let r := emitted st in
  let '(i, id_events) :=
    match component_ids r with
    | [] => (1%positive, [(AuditTarjanHelper (THCase 6), [])])
    | previous :: _ => let next := Pos.succ previous in
        (next, [(AuditTarjanHelper (THCase 7), []); (AuditTarjanHelper (THSucc previous next),
          [])]) end in
  let '(answer, pop_events) := audit_tarjan_nested_pop cb root i (pending st) (low st) (comp_of r)
    in
  let '(members, tail, links, owners) := answer in let component_map := Trie.set i members
    (component_at r) in
  (TarjanState (frames st) (disc st) links tail (clock st)
    (SccResult (members :: components r) (i :: component_ids r) component_map owners),
   id_events ++ pop_events ++ [(AuditTarjanHelper (THTrieSet i members (component_at r)), [])]).

Definition audit_tarjan_nested_close {V E B} (cb : audit_dfs_callback_model V E B) (v : V)
    (rest : list (tarjan_frame V E)) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  let closed := TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st) in
  let '(lo, lo_body) := audit_tarjan_nested_get cb v (low st) in
  match lo with
  | None => (closed, [(AuditTarjanHelper (THGet v (low st) lo), lo_body); (AuditTarjanHelper
    (THCase 8), [])])
  | Some l => let '(di, di_body) := audit_tarjan_nested_get cb v (disc st) in
    let reads := [(AuditTarjanHelper (THGet v (low st) lo), lo_body);
      (AuditTarjanHelper (THGet v (disc st) di), di_body)] in
    match di with
    | None => (closed, reads ++ [(AuditTarjanHelper (THCase 9), [])])
    | Some d => let equal := Pos.eqb l d in
      if equal then let '(next, events) := audit_tarjan_nested_emit cb v closed in
        (next, reads ++ [(AuditTarjanHelper (THPosCompare l d equal), []); (AuditTarjanHelper
          (THCase 10), [])] ++ events)
      else
        match rest with
        | [] => (closed, reads ++ [(AuditTarjanHelper (THPosCompare l d equal), []);
          (AuditTarjanHelper (THCase 11), [])])
        | parent :: _ => let '(next, events) := audit_tarjan_nested_lower cb (frame_node parent) l
          closed in
            (next, reads ++ [(AuditTarjanHelper (THPosCompare l d equal), []); (AuditTarjanHelper
              (THCase 12), [])] ++ events)
        end
    end
  end.

Definition audit_tarjan_nested_step {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : FinSet.t V) (st :
      tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  match frames st with
  | [] => (st, [(AuditTarjanCase 0, [])])
  | TarjanFrame v [] :: rest => let '(next, detail) := audit_tarjan_nested_close cb v rest st in
      (next, (AuditTarjanCase 1, []) :: detail ++ [(AuditTarjanClose v rest st next, [])])
  | TarjanFrame v (edge :: edges) :: rest =>
      let advanced := TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st) in
      let '(target, target_body) := audit_dfs_target_model cb edge in
      let '(member, member_body) := audit_tarjan_nested_get cb target region in
      let inside :=
        match member with
        | Some _ => true
        | None => false
        end in
      if inside then let '(found, found_body) := audit_tarjan_nested_get cb target (disc st) in
        match found with
        | None => let '(next, detail) := audit_tarjan_nested_discover p cb target advanced in
            (next, [(AuditTarjanTarget edge target, target_body); (AuditTarjanMember target region
              inside, member_body);
              (AuditTarjanCase 2, []); (AuditTarjanGet target (disc st) found, found_body)] ++
                detail ++
              [(AuditTarjanDiscover target advanced next, [])])
        | Some d => let '(on_stack, low_body) := audit_tarjan_nested_get cb target (low st) in
          match on_stack with
          | None => (advanced, [(AuditTarjanTarget edge target, target_body); (AuditTarjanMember
            target region inside, member_body);
              (AuditTarjanCase 2, []); (AuditTarjanGet target (disc st) found, found_body);
              (AuditTarjanGet target (low st) on_stack, low_body); (AuditTarjanCase 3, [])])
          | Some _ => let '(next, detail) := audit_tarjan_nested_lower cb v d advanced in
              (next, [(AuditTarjanTarget edge target, target_body); (AuditTarjanMember target
                region inside, member_body);
                (AuditTarjanCase 2, []); (AuditTarjanGet target (disc st) found, found_body);
                (AuditTarjanGet target (low st) on_stack, low_body); (AuditTarjanCase 4, [])] ++
                  detail ++
                [(AuditTarjanLower v d advanced next, [])])
          end
        end
      else (advanced, [(AuditTarjanTarget edge target, target_body); (AuditTarjanMember target
        region inside, member_body);
        (AuditTarjanCase 5, [])])
  end.

Fixpoint audit_tarjan_nested_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : FinSet.t V) (fuel :
      positive)
    (st : tarjan_state V E) : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  match frames st with
  | [] => (st, [(AuditTarjanCase 6, [])])
  | _ :: _ =>
    match fuel with
    | xH => let '(result, events) := audit_tarjan_nested_step p cb region st in
        (result, (AuditTarjanCase 7, []) :: events)
    | xO rest => let '(middle, first) := audit_tarjan_nested_run p cb region rest st in
        let '(result, second) := audit_tarjan_nested_run p cb region rest middle in
        (result, (AuditTarjanCase 8, []) :: first ++ second)
    | xI rest => let '(middle, first) := audit_tarjan_nested_run p cb region rest st in
        let '(last, second) := audit_tarjan_nested_run p cb region rest middle in
        let '(result, steps) := audit_tarjan_nested_step p cb region last in
        (result, (AuditTarjanCase 9, []) :: first ++ second ++ steps)
    end
  end.

Definition audit_tarjan_nested_root {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : FinSet.t V)
    (st : tarjan_state V E) (v : V) : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  let '(found, body) := audit_tarjan_nested_get cb v (disc st) in
  match found with
  | Some _ => (st, [(AuditTarjanGet v (disc st) found, body); (AuditTarjanCase 10, [])])
  | None => let '(next, detail) := audit_tarjan_nested_discover p cb v st in
      let '(result, events) := audit_tarjan_nested_run p cb region (fuel p) next in
      (result, [(AuditTarjanGet v (disc st) found, body); (AuditTarjanCase 11, [])] ++
        detail ++ [(AuditTarjanDiscover v st next, [])] ++ events)
  end.

Fixpoint audit_tarjan_nested_roots {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : FinSet.t V)
    (roots : list V) (st : tarjan_state V E) : tarjan_state V E * list (audit_tarjan_nested_event
      V E B) :=
  match roots with
  | [] => (st, [(AuditTarjanCase 12, [])])
  | root :: rest => let '(next, here) := audit_tarjan_nested_root p cb region st root in
      let '(result, later) := audit_tarjan_nested_roots p cb region rest next in
      (result, (AuditTarjanCase 13, []) :: here ++ later)
  end.

Fixpoint audit_tarjan_nested_region {V E B} (cb : audit_dfs_callback_model V E B)
    (region : list V) (set : FinSet.t V) : FinSet.t V * list (audit_tarjan_nested_event V E B) :=
  match region with
  | [] => (set, [(AuditTarjanCase 14, [])])
  | v :: rest => let '(next, body) := audit_tarjan_nested_set cb v tt set in
      let '(result, events) := audit_tarjan_nested_region cb rest next in
      (result, (AuditTarjanSet v set, body) :: events)
  end.

Definition audit_scc_within_nested_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : list V)
    : scc_result V * list (audit_tarjan_nested_event V E B) :=
  let '(keep, setup) := audit_tarjan_nested_region cb region FinSet.empty in
  let '(st, events) := audit_tarjan_nested_roots p cb keep region tarjan_initial in
  let r := emitted st in
  (tarjan_result st, setup ++ events ++ [(AuditTarjanOutput (length (components r)) (length
    (component_ids r)), [])]).

Definition audit_tarjan_nested_body_work {V E B} (weight : B -> nat)
    (events : list (audit_tarjan_nested_event V E B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd event) + total)
    0 events.

Definition audit_tarjan_nested_total_work {V E B} (EV : encoding V) (weight : B -> nat)
    (events : list (audit_tarjan_nested_event V E B)) : nat :=
  audit_tarjan_model_work EV (map fst events) + audit_tarjan_nested_body_work weight events.

(** Nested SCC traversal erases to the counted trace and obeys its bounds. *)
Definition audit_scc_within_nested_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B) region,
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_scc_within_nested_counted p cb region in
    result = scc_within p region /\ map fst events = snd (audit_scc_within_counted p region) /\
    length events <= audit_tarjan_input_event_bound p region /\
    audit_tarjan_model_work EV (map fst events) <= audit_tarjan_input_budget EV g p region.

(** Nested SCC total work is bounded by internal and callback body work. *)
Definition audit_scc_within_nested_total_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B) (weight : B -> nat) region,
    audit_dfs_callbacks_erase EV g cb ->
    let '(_, events) := audit_scc_within_nested_counted p cb region in
    audit_tarjan_nested_total_work EV weight events <= audit_tarjan_input_budget EV g p region +
      audit_tarjan_nested_body_work weight events.

Definition audit_scc_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : list V) :=
  let captured := audit_graph_capture_callbacks cb in
  let '(keep, setup) := audit_tarjan_nested_region captured region FinSet.empty in
  let '(st, events) := audit_tarjan_nested_roots p captured keep region tarjan_initial in
  let r := emitted st in
  (SccResult (rev_append (components r) []) (rev_append (component_ids r) [])
    (component_at r) (comp_of r),
    setup ++ events ++ [(AuditTarjanOutput (length (components r)) (length (component_ids r)),
      [])]).

Definition audit_scc_source_codes {V E B} (body : list (audit_graph_callback_capture V E B)) :
  positive * positive :=
  match body with
  | [AuditGraphEncodeCapture _ _ _ _ first _; AuditGraphEncodeCapture _ _ _ _ second _] => (first,
    second)
  | _ => (1%positive, 1%positive)
  end.

Definition audit_scc_reverse_work := audit_graph_reverse_fast_work.

(** Both reverse models satisfy their run and counted contracts. *)
Definition audit_scc_reverse_run_statement : Prop :=
  audit_graph_reverse_run_statement /\ audit_graph_reverse_fast_run_statement /\
  audit_graph_reverse_fast_counted_statement.

Definition audit_scc_source_helper_work {V E B} (body : list (audit_graph_callback_capture V E B))
    (event : audit_thelper_event V E) : nat :=
  let code := audit_dfs_source_code body in
  match event with
  | THGet _ input _ => 5 + audit_trie_get_source_work code input
  | THGetEdges _ input _ => 5 + audit_trie_get_source_work code input
  | THSet key value input => 2 + audit_trie_update_source_work code (Some (key, value)) input
  | THRemove _ input => 2 + audit_trie_update_source_work code None input
  | THCompare _ _ _ => let '(a, b) := audit_scc_source_codes body in 4 + 2 * Nat.min (Pos.size_nat
    a) (Pos.size_nat b)
  | THPosCompare a b _
  | THMin a b _ => 4 + 2 * Nat.min (Pos.size_nat a) (Pos.size_nat b)
  | THSucc a _ => 2 * Pos.size_nat a
  | THTrieSet key members input => 2 + audit_trie_update_source_work key (Some members) input
  | THCase _ => 0
  end.

Definition audit_scc_source_event_work {V E B} (weight : B -> nat)
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) : nat :=
  let '(event, body) := item in let code := audit_dfs_source_code body in
  let callback := fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body in
  64 + callback +
  match event with
  | AuditTarjanMember _ input _ => 5 + audit_trie_get_source_work code input
  | AuditTarjanGet _ input _ => 5 + audit_trie_get_source_work code input
  | AuditTarjanSet v input => 2 + audit_trie_update_source_work code (Some (v, tt)) input
  | AuditTarjanHelper helper => audit_scc_source_helper_work body helper
  | AuditTarjanOutput components identifiers =>
      audit_scc_reverse_work components + audit_scc_reverse_work identifiers
  | _ => 0
  end.

(** An SCC source event carries the matching callback captures. *)
Definition audit_scc_source_event_wellformed {V E B}
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditTarjanMember v _ _
  | AuditTarjanGet v _ _
  | AuditTarjanSet v _
  | AuditTarjanHelper (THGet v _ _)
  | AuditTarjanHelper (THGetEdges v _ _)
  | AuditTarjanHelper (THSet v _ _)
  | AuditTarjanHelper (THRemove v _) =>
      exists code trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditTarjanHelper (THCompare a b _) =>
      exists ac bc trace_a trace_b,
        body = [AuditGraphEncodeCapture V E B a ac trace_a; AuditGraphEncodeCapture V E B b bc
          trace_b]
  | AuditTarjanTarget edge vertex => exists trace, body = [AuditGraphTargetCapture V E B edge
    vertex trace]
  | _ => body = []
  end.

Definition audit_scc_source_work {V E B} (weight : B -> nat)
    (events : list (audit_tarjan_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun event n => audit_scc_source_event_work weight event + n) 0 events.

Definition audit_scc_source_body_work {V E B} (weight : B -> nat)
    (events : list (audit_tarjan_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_graph_capture_work weight event + k)
    0 (snd item) + n) 0 events.

Definition audit_scc_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (region : list V) : nat :=
  let count := audit_tarjan_input_event_bound p region in
  let width := Nat.max (audit_dfs_input_width EV g p region)
    (Pos.size_nat (Pos.of_succ_nat (2 + length region * S (Pos.to_nat (fuel p))))) in
  1024 * S count * S count + count * (512 + 64 * width).

(** Source SCC traversal returns SCCs with well-formed events and bounded work. *)
Definition audit_scc_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) region,
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_scc_source_counted p cb region in
    result = scc_within p region /\ Forall audit_scc_source_event_wellformed events /\
    length events <= audit_tarjan_input_event_bound p region /\
    audit_scc_source_work weight events <= audit_scc_source_budget EV g p region +
      audit_scc_source_body_work weight events.

Definition audit_scc_min_source_model (left right : positive) : positive * list
  audit_positive_compare_event :=
  let '(order, events) := audit_positive_compare left right in
  (
    match order with
    | Gt => right
    | _ => left
    end, events).

(** Counted positive minimum returns the minimum with a width-based event bound. *)
Definition audit_scc_min_source_model_statement : Prop :=
  forall left right,
    let '(result, events) := audit_scc_min_source_model left right in
    result = Pos.min left right /\ 2 * length events <= 2 * Nat.min (Pos.size_nat left)
      (Pos.size_nat right).

(** An SCC source event agrees with its corresponding primitive result. *)
Definition audit_scc_source_event_primitive {V E B}
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditTarjanHelper (THCompare _ _ result) =>
      let '(a, b) := audit_scc_source_codes body in fst (audit_positive_eqb a b) = result
  | AuditTarjanHelper (THPosCompare a b result) => fst (audit_positive_eqb a b) = result
  | AuditTarjanHelper (THMin a b result) => fst (audit_scc_min_source_model a b) = result
  | AuditTarjanHelper (THSucc input result) => fst (audit_positive_succ input) = result
  | _ => True
  end.

(** Each SCC source event satisfies the primitive correspondence. *)
Definition audit_scc_source_primitive_correspondence_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) region,
    audit_dfs_callbacks_erase EV g cb ->
    Forall audit_scc_source_event_primitive (snd (audit_scc_source_counted p cb region)).

(** SCC source adequacy requires its collection and arithmetic contracts. *)
Definition audit_scc_source_library_obligations : Prop :=
  audit_trie_get_trace_adequate_statement /\ audit_trie_update_trace_adequate_statement /\
  audit_trie_get_source_work_bound_statement /\ audit_trie_update_source_work_bound_statement /\
  audit_positive_eqb_erases_statement /\ audit_positive_eqb_source_bound_statement /\
  audit_positive_compare_cont_statement /\ audit_positive_compare_statement /\
  audit_positive_succ_run_total_statement /\ audit_positive_succ_run_correct_statement /\
  audit_scc_min_source_model_statement /\ audit_scc_source_primitive_correspondence_statement /\
  audit_scc_reverse_run_statement.

Definition audit_scc_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E -> nat)
    (event : audit_graph_callback_capture V E B) : nat :=
  match event with
  | AuditGraphEncodeCapture _ _ _ vertex _ _ => encode_budget vertex
  | AuditGraphTargetCapture _ _ _ edge _ _ => target_budget edge
  end.

Definition audit_scc_source_external_budget {V E B} (encode_budget : V -> nat) (target_budget : E
  -> nat)
    (events : list (audit_tarjan_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_scc_capture_budget encode_budget
    target_budget event + k)
    0 (snd item) + n) 0 events.

(** Adapted SCC traversal bounds external callback work by the supplied budgets. *)
Definition audit_scc_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) region
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    let '(result, events) := audit_scc_source_counted p cb region in
    result = scc_within p region /\
    audit_scc_source_work weight events <= audit_scc_source_budget EV g p region +
      audit_scc_source_external_budget encode_budget target_budget events.

(** The SCC source contract combines its primitive and source obligations. *)
Definition audit_scc_source_contract_statement : Prop :=
  audit_scc_source_statement /\ audit_scc_source_library_obligations /\
    audit_scc_source_adapted_statement.
