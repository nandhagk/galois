(** * Virtual-root graph audit model

    Models source-level events, work, and associated contract statements.
    For example, encoding a virtual entry records the underlying callback.

    Builds on: the graph and collections interfaces imported below. *)

From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsTrie CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators GraphAuditBase
  GraphAuditDfs GraphDominance GraphSemiDominators.
From Galois.Collections Require Import CollectionsAuditElements CollectionsAuditMap
  CollectionsAuditTrie CollectionsAuditFinSet.
Import List.ListNotations.

Inductive audit_virtual_call (V E : Type) : Type :=
  | AuditVirtualCase (site : nat)
  | AuditVirtualMem (v : V) (seen : FinSet.t V) (result : bool)
  | AuditVirtualAdd (v : V) (seen : FinSet.t V)
  | AuditVirtualOut (v : V) (edges : list E)
  | AuditVirtualSource (e : E) (v : V)
  | AuditVirtualTarget (e : E) (v : V)
  | AuditVirtualEncode (v : V) (code : positive)
  | AuditVirtualMap (size : nat).
Arguments AuditVirtualCase {V E} _.
Arguments AuditVirtualMem {V E} _ _ _.
Arguments AuditVirtualAdd {V E} _ _.
Arguments AuditVirtualOut {V E} _ _.
Arguments AuditVirtualSource {V E} _ _.
Arguments AuditVirtualTarget {V E} _ _.
Arguments AuditVirtualEncode {V E} _ _.
Arguments AuditVirtualMap {V E} _.

Fixpoint audit_virtual_entries_counted {V E} (EV : encoding V) (seen : FinSet.t V) (entries : list
  V)
    : list V * list (audit_virtual_call V E) :=
  match entries with
  | [] => ([], [AuditVirtualCase 0])
  | v :: rest => let found := FinSet.mem EV v seen in
    if found then let '(result, events) := audit_virtual_entries_counted EV seen rest in
      (result, AuditVirtualCase 1 :: AuditVirtualMem v seen found :: AuditVirtualCase 2 :: events)
    else let next := FinSet.add EV v seen in
      let '(result, events) := audit_virtual_entries_counted EV next rest in
      (v :: result, AuditVirtualCase 1 :: AuditVirtualMem v seen found :: AuditVirtualCase 3 ::
        AuditVirtualAdd v seen :: events)
  end.

Definition audit_virtual_out_counted {V E} (EV : encoding V) (g : Graph.t V E) (v : V + unit)
    : list (E + V) * list (audit_virtual_call V E) :=
  match v with
  | inl x => let edges := Graph.out g x in
      (map (@inl E V) edges, [AuditVirtualCase 4; AuditVirtualOut x edges; AuditVirtualMap (length
        edges)])
  | inr _ => let '(entries, events) := audit_virtual_entries_counted EV FinSet.empty
    (Graph.entries g) in
      (map (@inr E V) entries, AuditVirtualCase 5 :: events ++ [AuditVirtualMap (length entries)])
  end.

Definition audit_virtual_source_counted {V E} (g : Graph.t V E) (e : E + V)
    : (V + unit) * list (audit_virtual_call V E) :=
  match e with
  | inl original => let source := Graph.source g original in
      (inl source, [AuditVirtualCase 6; AuditVirtualSource original source])
  | inr _ => (inr tt, [AuditVirtualCase 7])
  end.

Definition audit_virtual_target_counted {V E} (g : Graph.t V E) (e : E + V)
    : (V + unit) * list (audit_virtual_call V E) :=
  match e with
  | inl original => let target := Graph.target g original in
      (inl target, [AuditVirtualCase 8; AuditVirtualTarget original target])
  | inr v => (inl v, [AuditVirtualCase 9])
  end.

Definition audit_virtual_encode_counted {V E} (EV : encoding V) (v : V + unit)
    : positive * list (audit_virtual_call V E) :=
  match v with
  | inl x => let code := encode EV x in (xO code, [AuditVirtualCase 10; AuditVirtualEncode x code])
  | inr _ => (xI xH, [AuditVirtualCase 11])
  end.

Definition audit_virtual_prepare_callbacks {V E} (EV : encoding V) (g : Graph.t V E)
    : audit_prepare_callback_model (V + unit) (E + V) (audit_virtual_call V E) :=
  AuditPrepareCallbackModel _ _ _ (audit_virtual_out_counted EV g)
    (audit_virtual_target_counted g) (audit_virtual_encode_counted EV).

Definition audit_virtual_dfs_callbacks {V E} (EV : encoding V) (g : Graph.t V E)
    : audit_dfs_callback_model (V + unit) (E + V) (audit_virtual_call V E) :=
  AuditDfsCallbackModel _ _ _ (audit_virtual_target_counted g) (audit_virtual_encode_counted EV).

(** Virtual preparation, DFS, source and entry callbacks erase to their ordinary operations. *)

Definition audit_virtual_callbacks_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    audit_prepare_callbacks_erase (virtual_encoding EV) (virtual_graph EV g)
      (audit_virtual_prepare_callbacks EV g) /\
    audit_dfs_callbacks_erase (virtual_encoding EV) (virtual_graph EV g)
      (audit_virtual_dfs_callbacks EV g) /\
    (forall edge, fst (audit_virtual_source_counted g edge) = Graph.source (virtual_graph EV g)
      edge) /\
    (forall seen entries, fst (@audit_virtual_entries_counted V E EV seen entries) =
      virtual_entries_from EV seen entries).

Definition audit_virtual_search_with_prepared {V E} (EV : encoding V) (g : Graph.t V E) :=
  let '(p, prep_events) := audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph
    EV g)
    (audit_virtual_prepare_callbacks EV g) in
  let '(result, dfs_events) := audit_dfs_nested_counted p (audit_virtual_dfs_callbacks EV g)
    FinSet.empty [inr tt] in
  (p, (result, (prep_events, dfs_events))).

Definition audit_virtual_search_counted {V E} (EV : encoding V) (g : Graph.t V E) :=
  let '(_, (result, traces)) := audit_virtual_search_with_prepared EV g in (result, traces).

(** Counted virtual search erases to virtual DFS. *)
Definition audit_virtual_search_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    fst (audit_virtual_search_counted EV g) = virtual_dfs p.

Definition audit_virtual_event_work {V E} (EV : encoding V) (event : audit_virtual_call V E) : nat
  :=
  64 +
  match event with
  | AuditVirtualMem v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_get_weight (encode EV v)
  | AuditVirtualAdd v _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_set_weight (encode EV v)
  | AuditVirtualEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditVirtualMap size => S size
  | _ => 0
  end.

Definition audit_virtual_entries_work {V E} (EV : encoding V) (events : list (audit_virtual_call V
  E)) : nat :=
  fold_right (fun event n => audit_virtual_event_work EV event + n) 0 events.

Definition audit_virtual_entries_width {V} (EV : encoding V) (entries : list V) : nat :=
  fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) entries).

Definition audit_virtual_entries_budget {V} (EV : encoding V) (entries : list V) : nat :=
  (1 + 4 * length entries) * (70 + 3 * audit_virtual_entries_width EV entries).

(** Counted virtual entries return the entry set with bounded events and work. *)
Definition audit_virtual_entries_statement : Prop :=
  forall V E (EV : encoding V) seen entries,
    let '(result, events) := @audit_virtual_entries_counted V E EV seen entries in
    result = virtual_entries_from EV seen entries /\ length events <= 1 + 4 * length entries /\
    audit_virtual_entries_work EV events <= audit_virtual_entries_budget EV entries.

Definition audit_virtual_search_work {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let '(_, (prep_events, dfs_events)) := audit_virtual_search_counted EV g in
  audit_graph_prepare_nested_total_work (audit_virtual_event_work EV) prep_events +
  audit_dfs_nested_total_work (virtual_encoding EV) (audit_virtual_event_work EV) dfs_events.

Definition audit_virtual_search_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let vg := virtual_graph EV g in
  let encoding := virtual_encoding EV in
  let p := prepare encoding vg in
  let prep_count := audit_graph_prepare_full_event_bound vg in
  let dfs_count := audit_dfs_full_input_event_bound p [inr tt] in
  let width := Nat.max (audit_graph_prepare_input_width encoding vg)
    (audit_dfs_full_input_width encoding vg p [inr tt]) in
  let list_size := 1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g in
  let body_budget := 8 * S (length (Graph.entries g)) * (256 + 6 * width + list_size) in
  audit_graph_prepare_full_budget encoding vg + audit_dfs_full_input_budget encoding vg p [inr tt] +
    (prep_count + dfs_count) * body_budget.

(** Virtual search work obeys its input-derived budget. *)
Definition audit_virtual_search_bound_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    audit_virtual_search_work EV g <= audit_virtual_search_budget EV g.

Inductive audit_erase_call (V : Type) : Type :=
  | AuditEraseCase (site : nat)
  | AuditEraseElements (input : Map.t (V + unit) (V + unit)) (rows : list ((V + unit) * (V + unit)))
  | AuditEraseSet (key value : V) (before : Map.t V V).
Arguments AuditEraseCase {V} _.
Arguments AuditEraseElements {V} _ _.
Arguments AuditEraseSet {V} _ _ _.

Fixpoint audit_erase_rows_counted {V} (EV : encoding V) (rows : list ((V + unit) * (V + unit)))
    : Map.t V V * list (audit_erase_call V) :=
  match rows with
  | [] => (Map.empty, [AuditEraseCase 0])
  | row :: rest => let '(middle, events) := audit_erase_rows_counted EV rest in
      match row with
      | (inl v, inl parent) => (Map.set EV v parent middle,
          AuditEraseCase 1 :: events ++ [AuditEraseCase 2; AuditEraseSet v parent middle])
      | _ => (middle, AuditEraseCase 1 :: events ++ [AuditEraseCase 3])
      end
  end.

Definition audit_erase_virtual_counted {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit))
    : Map.t V V * list (audit_erase_call V) :=
  let rows := Map.elements m in let '(result, events) := audit_erase_rows_counted EV rows in
  (result, AuditEraseElements m rows :: events).

Fixpoint audit_erase_nodes_ne {A} (node : Trie.ne A) : nat :=
  match node with
  | Trie.N001 r => S (audit_erase_nodes_ne r)
  | Trie.N010 _ => 1
  | Trie.N011 _ r => S (audit_erase_nodes_ne r)
  | Trie.N100 l => S (audit_erase_nodes_ne l)
  | Trie.N101 l r => S (audit_erase_nodes_ne l + audit_erase_nodes_ne r)
  | Trie.N110 l _ => S (audit_erase_nodes_ne l)
  | Trie.N111 l _ r => S (audit_erase_nodes_ne l + audit_erase_nodes_ne r)
  end.

Definition audit_erase_nodes {A} (m : Trie.t A) : nat :=
  match m with
  | Trie.Empty => 0
  | Trie.Nodes node => audit_erase_nodes_ne node
  end.

Definition audit_erase_event_work {V} (EV : encoding V) (event : audit_erase_call V) : nat :=
  64 +
  match event with
  | AuditEraseElements input _ => 64 * Nat.pow (S (audit_erase_nodes input)) 3
  | AuditEraseSet key _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV key)) +
    audit_set_weight (encode EV key)
  | AuditEraseCase _ => 0
  end.

Definition audit_erase_virtual_work {V} (EV : encoding V) (events : list (audit_erase_call V)) :
  nat :=
  128 * S (length events) * S (length events) +
    fold_right (fun event total => audit_erase_event_work EV event + total) 0 events.

Definition audit_erase_width {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) : nat :=
  fold_right (fun row n =>
    match fst row with
    | inl v => Nat.max (audit_key_bits_weight (encode EV v)) n
    | inr _ => n
    end)
    0 (Map.elements m).

Definition audit_erase_event_bound {V} (m : Map.t (V + unit) (V + unit)) : nat :=
  2 + 3 * length (Map.elements m).

Definition audit_erase_virtual_budget {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) :
  nat :=
  let count := audit_erase_event_bound m in
  256 * Nat.pow (S (audit_erase_nodes m)) 3 + 256 * S count * S count +
    count * (80 + 4 * audit_erase_width EV m).

(** Counted virtual-parent erasure returns the original result with bounded events and work. *)
Definition audit_erase_virtual_statement : Prop :=
  forall V (EV : encoding V) m,
    let '(result, events) := audit_erase_virtual_counted EV m in
    result = erase_virtual_parents EV m /\ length events <= audit_erase_event_bound m /\
    audit_erase_virtual_work EV events <= audit_erase_virtual_budget EV m.

Inductive audit_erase_nested_event (V B : Type) : Type :=
  | EraseNestedCase : nat -> audit_erase_nested_event V B
  | EraseNestedElements : audit_elements_event ((V + unit) * (V + unit)) -> audit_erase_nested_event
  V B
  | EraseNestedSet : audit_map_event V V B -> audit_erase_nested_event V B.
Arguments EraseNestedCase {V B} _.
Arguments EraseNestedElements {V B} _.
Arguments EraseNestedSet {V B} _.

Fixpoint audit_erase_nested_rows {V B} (enc : V -> positive * list B)
    (rows : list ((V + unit) * (V + unit))) : Map.t V V * list (audit_erase_nested_event V B) :=
  match rows with
  | [] => (Map.empty, [EraseNestedCase 0])
  | row :: rest => let '(middle, events) := audit_erase_nested_rows enc rest in
      match row with
      | (inl v, inl parent) => let '(result, writes) := audit_map_set enc v parent middle in
          (result, [EraseNestedCase 1] ++ events ++ [EraseNestedCase 2] ++ map EraseNestedSet
            writes)
      | _ => (middle, [EraseNestedCase 1] ++ events ++ [EraseNestedCase 3])
      end
  end.

Definition audit_erase_virtual_nested {V B} (enc : V -> positive * list B)
    (m : Map.t (V + unit) (V + unit)) : Map.t V V * list (audit_erase_nested_event V B) :=
  let '(rows, elements) := audit_map_elements m in
  let '(result, events) := audit_erase_nested_rows enc rows in
  (result, map EraseNestedElements elements ++ events).

Definition audit_erase_nested_event_work {V B} (weight : B -> nat) (event :
  audit_erase_nested_event V B) : nat :=
  64 +
  match event with
  | EraseNestedElements item => audit_elements_frame_work item
  | EraseNestedSet item => audit_map_source_work (fun body => fold_right (fun x n => weight x + n)
    0 body) [item]
  | EraseNestedCase _ => 0
  end.

Definition audit_erase_nested_body_event_work {V B} (weight : B -> nat)
    (event : audit_erase_nested_event V B) : nat :=
  match event with
  | EraseNestedSet (AuditMapGet _ _ _ _ body _)
  | EraseNestedSet (AuditMapSet _ _ _ _ _ body _)
  | EraseNestedSet (AuditMapRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | EraseNestedCase _
  | EraseNestedElements _ => 0
  end.

Definition audit_erase_nested_work {V B} (weight : B -> nat) (events : list
  (audit_erase_nested_event V B)) : nat :=
  fold_right (fun item n => audit_erase_nested_event_work weight item + n) 0 events.

Definition audit_erase_nested_body_work {V B} (weight : B -> nat) (events : list
  (audit_erase_nested_event V B)) : nat :=
  fold_right (fun item n => audit_erase_nested_body_event_work weight item + n) 0 events.

Definition audit_erase_nested_width {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) : nat :=
  fold_right (fun row n =>
    match fst row with
    | inl v => Nat.max (Pos.size_nat (encode EV v)) n
    | inr _ => n
    end)
    0 (Map.elements m).

Definition audit_erase_nested_budget {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) : nat
  :=
  let n := S (audit_trie_nodes m) in
  1024 * n * n + 128 * audit_trie_output_bits m + 128 * n * S (audit_erase_nested_width EV m).

(** Nested virtual-parent erasure preserves the result and bounds total work. *)
Definition audit_erase_nested_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) m,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_erase_virtual_nested enc m in
    result = erase_virtual_parents EV m /\
    audit_erase_nested_work weight events <= audit_erase_nested_budget EV m +
      audit_erase_nested_body_work weight events.

Inductive audit_virtual_entries_full_event (V B : Type) : Type :=
  | VirtualEntriesCase : nat -> audit_virtual_entries_full_event V B
  | VirtualEntriesSet : audit_set_event V B -> audit_virtual_entries_full_event V B.
Arguments VirtualEntriesCase {V B} _.
Arguments VirtualEntriesSet {V B} _.

Fixpoint audit_virtual_entries_full_counted {V B}
    (enc : V -> positive * list B) (seen : FinSet.t V) (entries : list V)
    : list V * list (audit_virtual_entries_full_event V B) :=
  match entries with
  | [] => ([], [VirtualEntriesCase 0])
  | v :: rest =>
      let '(found, reads) := audit_finset_mem enc v seen in
      if found then
        let '(result, later) := audit_virtual_entries_full_counted enc seen rest in
        (result, [VirtualEntriesCase 1] ++ map VirtualEntriesSet reads ++
          [VirtualEntriesCase 2] ++ later)
      else
        let '(next, writes) := audit_finset_add enc v seen in
        let '(result, later) := audit_virtual_entries_full_counted enc next rest in
        (v :: result, [VirtualEntriesCase 1] ++ map VirtualEntriesSet reads ++
          [VirtualEntriesCase 3] ++ map VirtualEntriesSet writes ++ later)
  end.

Definition audit_virtual_entries_full_internal_event_work {V B}
    (event : audit_virtual_entries_full_event V B) : nat :=
  64 +
  match event with
  | VirtualEntriesSet (AuditSetMem _ code input _ _ _) =>
      5 + audit_trie_get_source_work code input
  | VirtualEntriesSet (AuditSetAdd key code input _ _ _) =>
      5 + audit_trie_update_source_work code (Some (key, tt)) input
  | VirtualEntriesSet (AuditSetRemove _ code input _ _ _) =>
      5 + audit_trie_update_source_work code None input
  | VirtualEntriesSet (AuditSetFold _ _)
  | VirtualEntriesCase _ => 0
  end.

Definition audit_virtual_entries_full_body_event_work {V B} (weight : B -> nat)
    (event : audit_virtual_entries_full_event V B) : nat :=
  match event with
  | VirtualEntriesSet (AuditSetMem _ _ _ _ body _)
  | VirtualEntriesSet (AuditSetAdd _ _ _ _ body _)
  | VirtualEntriesSet (AuditSetRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | VirtualEntriesSet (AuditSetFold _ _)
  | VirtualEntriesCase _ => 0
  end.

Definition audit_virtual_entries_full_internal_work {V B}
    (events : list (audit_virtual_entries_full_event V B)) : nat :=
  fold_right (fun item n => audit_virtual_entries_full_internal_event_work item + n) 0 events.

Definition audit_virtual_entries_full_body_work {V B} (weight : B -> nat)
    (events : list (audit_virtual_entries_full_event V B)) : nat :=
  fold_right (fun item n => audit_virtual_entries_full_body_event_work weight item + n) 0 events.

Definition audit_virtual_entries_full_width {V} (EV : encoding V) (entries : list V) : nat :=
  fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) entries).

Definition audit_virtual_entries_full_budget {V} (EV : encoding V) (entries : list V) : nat :=
  128 + length entries * (512 + 32 * audit_virtual_entries_full_width EV entries).

(** Full virtual entry construction preserves the result and bounds events and internal work. *)
Definition audit_virtual_entries_full_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) seen entries,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_virtual_entries_full_counted enc seen entries in
    result = virtual_entries_from EV seen entries /\
    length events <= 1 + 4 * length entries /\
    audit_virtual_entries_full_internal_work events <= audit_virtual_entries_full_budget EV entries.

(** Full virtual entry construction preserves the result and bounds total work. *)
Definition audit_virtual_entries_full_total_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) seen entries,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_virtual_entries_full_counted enc seen entries in
    result = virtual_entries_from EV seen entries /\
    audit_virtual_entries_full_internal_work events + audit_virtual_entries_full_body_work weight
      events <=
      audit_virtual_entries_full_budget EV entries + audit_virtual_entries_full_body_work weight
        events.

Record audit_virtual_base_callbacks (V E B : Type) : Type := AuditVirtualBaseCallbacks {
  audit_virtual_base_out : V -> list E * list B;
  audit_virtual_base_target : E -> V * list B;
  audit_virtual_base_encode : V -> positive * list B
}.
Arguments audit_virtual_base_out {V E B} _ _.
Arguments audit_virtual_base_target {V E B} _ _.
Arguments audit_virtual_base_encode {V E B} _ _.

Inductive audit_virtual_full_call (V E B : Type) : Type :=
  | VirtualFullCase : nat -> audit_virtual_full_call V E B
  | VirtualFullOut : V -> list E -> list B -> audit_virtual_full_call V E B
  | VirtualFullTarget : E -> V -> list B -> audit_virtual_full_call V E B
  | VirtualFullSource : E -> V -> list B -> audit_virtual_full_call V E B
  | VirtualFullEncode : V -> positive -> list B -> audit_virtual_full_call V E B
  | VirtualFullEntry : audit_virtual_entries_full_event V B -> audit_virtual_full_call V E B
  | VirtualFullMap : nat -> audit_virtual_full_call V E B.
Arguments VirtualFullCase {V E B} _.
Arguments VirtualFullOut {V E B} _ _ _.
Arguments VirtualFullTarget {V E B} _ _ _.
Arguments VirtualFullSource {V E B} _ _ _.
Arguments VirtualFullEncode {V E B} _ _ _.
Arguments VirtualFullEntry {V E B} _.
Arguments VirtualFullMap {V E B} _.

(** Virtual base callbacks return the original graph and encoding values. *)
Definition audit_virtual_base_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) : Prop :=
  (forall v, fst (audit_virtual_base_out cb v) = Graph.out g v) /\
  (forall e, fst (audit_virtual_base_target cb e) = Graph.target g e) /\
  (forall v, fst (audit_virtual_base_encode cb v) = encode EV v).

Definition audit_virtual_full_out {V E B} (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (v : V + unit)
    : list (E + V) * list (audit_virtual_full_call V E B) :=
  match v with
  | inl vertex => let '(edges, body) := audit_virtual_base_out cb vertex in
      (map (@inl E V) edges,
        [VirtualFullCase 0; VirtualFullOut vertex edges body; VirtualFullMap (length edges)])
  | inr _ =>
      let '(entries, events) := audit_virtual_entries_full_counted
        (audit_virtual_base_encode cb) FinSet.empty (Graph.entries g) in
      (map (@inr E V) entries,
        [VirtualFullCase 1] ++ map VirtualFullEntry events ++ [VirtualFullMap (length entries)])
  end.

Definition audit_virtual_full_target {V E B} (cb : audit_virtual_base_callbacks V E B)
    (edge : E + V) : (V + unit) * list (audit_virtual_full_call V E B) :=
  match edge with
  | inl original => let '(target, body) := audit_virtual_base_target cb original in
      (inl target, [VirtualFullCase 2; VirtualFullTarget original target body])
  | inr vertex => (inl vertex, [VirtualFullCase 3])
  end.

Definition audit_virtual_full_source {V E B} (source : E -> V * list B)
    (edge : E + V) : (V + unit) * list (audit_virtual_full_call V E B) :=
  match edge with
  | inl original => let '(vertex, body) := source original in
      (inl vertex, [VirtualFullCase 6; VirtualFullSource original vertex body])
  | inr _ => (inr tt, [VirtualFullCase 7])
  end.

(** The lifted source callback erases to the virtual graph source. *)
Definition audit_virtual_full_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (source : E -> V * list B),
    (forall edge, fst (source edge) = Graph.source g edge) ->
    forall edge, fst (audit_virtual_full_source source edge) = Graph.source (virtual_graph EV g)
      edge.

Definition audit_virtual_full_encode {V E B} (cb : audit_virtual_base_callbacks V E B)
    (vertex : V + unit) : positive * list (audit_virtual_full_call V E B) :=
  match vertex with
  | inl original => let '(code, body) := audit_virtual_base_encode cb original in
      (xO code, [VirtualFullCase 4; VirtualFullEncode original code body])
  | inr _ => (xI xH, [VirtualFullCase 5])
  end.

Definition audit_virtual_full_prepare_callbacks {V E B} (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B)
    : audit_prepare_callback_model (V + unit) (E + V) (audit_virtual_full_call V E B) :=
  AuditPrepareCallbackModel _ _ _ (audit_virtual_full_out g cb)
    (audit_virtual_full_target cb) (audit_virtual_full_encode cb).

Definition audit_virtual_full_dfs_callbacks {V E B} (cb : audit_virtual_base_callbacks V E B)
    : audit_dfs_callback_model (V + unit) (E + V) (audit_virtual_full_call V E B) :=
  AuditDfsCallbackModel _ _ _ (audit_virtual_full_target cb) (audit_virtual_full_encode cb).

(** Lifted callbacks erase to virtual preparation and DFS callbacks. *)
Definition audit_virtual_full_callbacks_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_virtual_base_callbacks V E B),
    audit_virtual_base_callbacks_erase EV g cb ->
    audit_prepare_callbacks_erase (virtual_encoding EV) (virtual_graph EV g)
      (audit_virtual_full_prepare_callbacks g cb) /\
    audit_dfs_callbacks_erase (virtual_encoding EV) (virtual_graph EV g)
      (audit_virtual_full_dfs_callbacks cb).

Definition audit_virtual_full_search_with_prepared {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) :=
  let '(p, prepare_events) := audit_graph_prepare_nested_counted (virtual_encoding EV)
    (virtual_graph EV g) (audit_virtual_full_prepare_callbacks g cb) in
  let '(result, dfs_events) := audit_dfs_nested_counted p (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty [inr tt] in
  (p, (result, (prepare_events, dfs_events))).

Definition audit_virtual_full_search_counted {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) :=
  let '(_, (result, events)) := audit_virtual_full_search_with_prepared EV g cb in (result, events).

(** Full virtual search erases to virtual DFS. *)
Definition audit_virtual_full_search_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_virtual_base_callbacks V E B)
    (p : prepared EV g), audit_virtual_base_callbacks_erase EV g cb ->
    fst (audit_virtual_full_search_counted EV g cb) = virtual_dfs p.

Definition audit_virtual_full_internal_event_work {V E B}
    (event : audit_virtual_full_call V E B) : nat :=
  64 +
  match event with
  | VirtualFullEntry inner => audit_virtual_entries_full_internal_event_work inner
  | VirtualFullMap size => S size
  | VirtualFullCase _
  | VirtualFullOut _ _ _
  | VirtualFullTarget _ _ _
  | VirtualFullSource _ _ _
  | VirtualFullEncode _ _ _ => 0
  end.

Definition audit_virtual_full_body_event_work {V E B} (weight : B -> nat)
    (event : audit_virtual_full_call V E B) : nat :=
  match event with
  | VirtualFullEntry inner => audit_virtual_entries_full_body_event_work weight inner
  | VirtualFullOut _ _ body
  | VirtualFullTarget _ _ body
  | VirtualFullSource _ _ body
  | VirtualFullEncode _ _ body =>
      fold_right (fun item n => weight item + n) 0 body
  | VirtualFullCase _
  | VirtualFullMap _ => 0
  end.

Definition audit_virtual_full_events_body_work {V E B} (weight : B -> nat)
    (events : list (audit_virtual_full_call V E B)) : nat :=
  fold_right (fun item n => audit_virtual_full_body_event_work weight item + n) 0 events.

Definition audit_virtual_full_search_input_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let vg := virtual_graph EV g in
  let encoding := virtual_encoding EV in
  let p := prepare encoding vg in
  let prepare_count := audit_graph_prepare_full_event_bound vg in
  let dfs_count := audit_dfs_full_input_event_bound p [inr tt] in
  let width := Nat.max (audit_graph_prepare_input_width encoding vg)
    (audit_dfs_full_input_width encoding vg p [inr tt]) in
  let size := 1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g in
  let body_budget := 8 * S (length (Graph.entries g)) * (1024 + 128 * S width + size) in
  audit_graph_prepare_full_budget encoding vg + audit_dfs_full_input_budget encoding vg p [inr tt] +
    (prepare_count + dfs_count) * body_budget.

Definition audit_virtual_source_search {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) :=
  let '(p, prepare_events) := audit_prepare_source_counted (virtual_encoding EV) (virtual_graph EV
    g)
    (audit_virtual_full_prepare_callbacks g cb) in
  let '(result, dfs_events) := audit_dfs_source_counted p (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty [inr tt] in
  (p, (result, (prepare_events, dfs_events))).

Definition audit_virtual_source_search_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let vg := virtual_graph EV g in let enc := virtual_encoding EV in let p := prepare enc vg in
  audit_prepare_source_budget enc vg + audit_dfs_source_budget enc vg p [inr tt] +
    audit_virtual_full_search_input_budget EV g.

(** Virtual source search preserves the result and satisfies its source work bound. *)
Definition audit_virtual_source_search_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (weight : B -> nat),
    audit_virtual_base_callbacks_erase EV g cb ->
    let '(vp, (result, (prepare_events, dfs_events))) := audit_virtual_source_search EV g cb in
    vp = virtual_prepared p /\ result = virtual_dfs p /\
    audit_prepare_source_work
      (fun item => audit_virtual_full_internal_event_work item +
        audit_virtual_full_body_event_work weight item)
      prepare_events +
    audit_dfs_source_work
      (fun item => audit_virtual_full_internal_event_work item +
        audit_virtual_full_body_event_work weight item)
      dfs_events <= audit_virtual_source_search_budget EV g +
    audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
    audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events.
