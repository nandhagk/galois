(** * Loop forest source contracts

    The model records component searches, header removal and loop forest packing.
    For example, each cyclic component retains its actual SCC and child-map events.
    Builds on: graph DFS and SCC source models and collection source models. *)

From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap
    CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditPrimitive
      CollectionsAuditCompare CollectionsAuditUnion CollectionsAuditMapTraverse
        CollectionsAuditEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphLoops
  GraphAuditBase GraphAuditDfs GraphAuditScc GraphAuditWto.
Import List.ListNotations.

Inductive audit_loop_call (V E : Type) : Type :=
  | AuditLoopCase (site : nat)
  | AuditLoopDfs (event : audit_dfs_full_call V E)
  | AuditLoopScc (event : audit_tarjan_call V E)
  | AuditLoopRead (v : V) (m : Map.t V positive) (result : option positive)
  | AuditLoopEdges (v : V) (m : Map.t V (list E)) (result : option (list E))
  | AuditLoopEncode (v : V) (code : positive)
  | AuditLoopTarget (e : E) (v : V)
  | AuditLoopCompare (a b : positive) (result : bool)
  | AuditLoopSet (v : V) (before : FinSet.t V)
  | AuditLoopNodeWrite (v : V) (value : FinSet.t V) (before : Map.t V (FinSet.t V))
  | AuditLoopParentWrite (v value : V) (before : Map.t V V)
  | AuditLoopMap (head : V) (input : FinSet.t V) (result : Map.t V V)
  | AuditLoopUnion (left right result : Map.t V V)
  | AuditLoopOutput (size : nat)
  | AuditLoopDepth (size : nat) (depth : N).
Arguments AuditLoopCase {V E} _.
Arguments AuditLoopDfs {V E} _.
Arguments AuditLoopScc {V E} _.
Arguments AuditLoopRead {V E} _ _ _.
Arguments AuditLoopEdges {V E} _ _ _.
Arguments AuditLoopEncode {V E} _ _.
Arguments AuditLoopTarget {V E} _ _.
Arguments AuditLoopCompare {V E} _ _ _.
Arguments AuditLoopSet {V E} _ _.
Arguments AuditLoopNodeWrite {V E} _ _ _.
Arguments AuditLoopParentWrite {V E} _ _ _.
Arguments AuditLoopMap {V E} _ _ _.
Arguments AuditLoopUnion {V E} _ _ _.
Arguments AuditLoopOutput {V E} _.
Arguments AuditLoopDepth {V E} _ _.

Fixpoint audit_loop_choose_counted {V E} (EV : encoding V) (numbers : Map.t V positive)
    (component : list V) : option V * list (audit_loop_call V E) :=
  match component with
  | [] => (None, [AuditLoopCase 0])
  | v :: rest => let '(chosen, events) := audit_loop_choose_counted EV numbers rest in
    match chosen with
    | None => (Some v, AuditLoopCase 1 :: events ++ [AuditLoopCase 2])
    | Some w =>
      let a := Map.get EV w numbers in
      let av :=
        match a with
        | Some n => n
        | None => 1%positive
        end in
      let b := Map.get EV v numbers in
      let bv :=
        match b with
        | Some n => n
        | None => 1%positive
        end in
        let le := Pos.leb av bv in
        (Some (if le then v else w), AuditLoopCase 1 :: events ++
          [AuditLoopCase 3; AuditLoopRead w numbers a; AuditLoopRead v numbers b; AuditLoopCompare
            av bv le])
    end
  end.

Fixpoint audit_loop_without_counted {V E} (EV : encoding V) (header : V) (component : list V)
    : list V * list (audit_loop_call V E) :=
  match component with
  | [] => ([], [AuditLoopCase 4])
  | v :: rest => let a := encode EV v in let b := encode EV header in let eq := Pos.eqb a b in
      let '(tail, events) := audit_loop_without_counted EV header rest in
      (if eq then tail else v :: tail,
       AuditLoopCase 5 :: AuditLoopEncode v a :: AuditLoopEncode header b :: AuditLoopCompare a b
         eq :: events)
  end.

Fixpoint audit_loop_self_edges {V E} (EV : encoding V) (g : Graph.t V E) (v : V) (edges : list E)
    : bool * list (audit_loop_call V E) :=
  match edges with
  | [] => (false, [AuditLoopCase 6])
  | e :: rest => let target := Graph.target g e in let a := encode EV target in
      let b := encode EV v in let eq := Pos.eqb a b in
      let '(later, events) := audit_loop_self_edges EV g v rest in
      (eq || later, AuditLoopCase 7 :: AuditLoopTarget e target :: AuditLoopEncode target a ::
        AuditLoopEncode v b :: AuditLoopCompare a b eq :: events)
  end.

Definition audit_loop_cyclic_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (component : list V) : bool * list (audit_loop_call V E) :=
  match component with
  | [] => (false, [AuditLoopCase 8])
  | [v] => let found := Map.get EV v (out_index p) in
      let edges :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(result, events) := audit_loop_self_edges EV g v edges in
      (result, AuditLoopCase 9 :: AuditLoopEdges v (out_index p) found :: events)
  | _ :: _ :: _ => (true, [AuditLoopCase 10])
  end.

Definition audit_loop_block_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_call V E))
    (parent : option V) (region component : list V) : list (loop_entry V) * list (audit_loop_call
      V E) :=
  let '(cyclic, cyclic_events) := audit_loop_cyclic_counted p component in
  if cyclic then let '(chosen, choose_events) := audit_loop_choose_counted EV numbers component in
    match chosen with
    | None => ([], cyclic_events ++ AuditLoopCase 11 :: choose_events ++ [AuditLoopCase 12])
    | Some header => let '(smaller, remove_events) := audit_loop_without_counted EV header
      component in
        let '(children, child_events) := descend (Some header) smaller in
        (LoopEntry header component parent region :: children,
         cyclic_events ++ AuditLoopCase 11 :: choose_events ++ AuditLoopCase 13 ::
           remove_events ++ child_events ++ [AuditLoopOutput 1])
    end
  else ([], cyclic_events ++ [AuditLoopCase 14]).

Fixpoint audit_loop_blocks_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_call V E))
    (parent : option V) (region : list V) (components : list (list V))
    : list (loop_entry V) * list (audit_loop_call V E) :=
  match components with
  | [] => ([], [AuditLoopCase 15])
  | component :: rest => let '(first, here) := audit_loop_block_counted p numbers descend parent
    region component in
      let '(later, events) := audit_loop_blocks_counted p numbers descend parent region rest in
      (first ++ later, AuditLoopCase 16 :: here ++ events ++ [AuditLoopOutput (length first)])
  end.

Definition audit_loop_layer_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_call V E))
    (parent : option V) (region : list V) : list (loop_entry V) * list (audit_loop_call V E) :=
  let '(sccs, scc_events) := audit_scc_within_counted p region in
  let '(result, events) := audit_loop_blocks_counted p numbers descend parent region (components
    sccs) in
  (result, map AuditLoopScc scc_events ++ events).

Definition audit_loop_iter_event {V E} (event : audit_comb_event (audit_loop_call V E)) :
  audit_loop_call V E :=
  match event with
  | AuditCombCase site => AuditLoopCase (20 + site)
  | AuditCombBody body => body
  end.

Definition audit_loop_entries_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : list (loop_entry V) * list (audit_loop_call V E) :=
  let '(search, dfs_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let depth := N.of_nat (length (preorder search)) in
  let base := fun (_ : option V) (_ : list V) => (@nil (loop_entry V), @nil (audit_loop_call V E))
    in
  let step := fun descend => (audit_loop_layer_counted p (post_num search) descend, @nil
    (audit_loop_call V E)) in
  let '(run, iter_events) := audit_n_iter depth step base in
  let '(result, events) := run None (preorder search) in
  (result, map AuditLoopDfs dfs_events ++ [AuditLoopDepth (length (preorder search)) depth] ++
    map audit_loop_iter_event iter_events ++ events).

Fixpoint audit_loop_set_counted {V E} (EV : encoding V) (vertices : list V) (set : FinSet.t V)
    : FinSet.t V * list (audit_loop_call V E) :=
  match vertices with
  | [] => (set, [AuditLoopCase 25])
  | v :: rest => let next := FinSet.add EV v set in
      let '(result, events) := audit_loop_set_counted EV rest next in
      (result, AuditLoopCase 26 :: AuditLoopSet v set :: events)
  end.

Fixpoint audit_loop_nodes_counted {V E} (EV : encoding V) (entries : list (loop_entry V))
    : Map.t V (FinSet.t V) * list (audit_loop_call V E) :=
  match entries with
  | [] => (Map.empty, [AuditLoopCase 27])
  | entry :: rest => let '(middle, later) := audit_loop_nodes_counted EV rest in
      let '(members, events) := audit_loop_set_counted EV (loop_members entry) FinSet.empty in
      let result := Map.set EV (loop_head entry) members middle in
      (result, AuditLoopCase 28 :: later ++ events ++ [AuditLoopNodeWrite (loop_head entry)
        members middle])
  end.

Fixpoint audit_loop_parents_counted {V E} (EV : encoding V) (entries : list (loop_entry V))
    : Map.t V V * list (audit_loop_call V E) :=
  match entries with
  | [] => (Map.empty, [AuditLoopCase 29])
  | entry :: rest => let '(middle, later) := audit_loop_parents_counted EV rest in
      match loop_enclosing entry with
      | None => (middle, AuditLoopCase 30 :: later ++ [AuditLoopCase 31])
      | Some parent => (Map.set EV (loop_head entry) parent middle,
          AuditLoopCase 30 :: later ++ [AuditLoopCase 32; AuditLoopParentWrite (loop_head entry)
            parent middle])
      end
  end.

Fixpoint audit_loop_owners_counted {V E} (EV : encoding V) (entries : list (loop_entry V))
    : Map.t V V * list (audit_loop_call V E) :=
  match entries with
  | [] => (Map.empty, [AuditLoopCase 33])
  | entry :: rest => let '(members, here) := audit_loop_set_counted EV (loop_members entry)
    FinSet.empty in
      let mapped := Map.map (fun _ => loop_head entry) members in
      let '(deeper, later) := audit_loop_owners_counted EV rest in
      let result := Map.union_with (fun _ deeper_value => deeper_value) mapped deeper in
      (result, AuditLoopCase 34 :: here ++ [AuditLoopMap (loop_head entry) members mapped] ++
        later ++ [AuditLoopUnion mapped deeper result])
  end.

Definition audit_loop_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : loop_forest V * list (audit_loop_call V E) :=
  let '(entries, entry_events) := audit_loop_entries_counted p in
  let headers := map loop_head entries in
  let '(nodes, node_events) := audit_loop_nodes_counted EV entries in
  let '(parents, parent_events) := audit_loop_parents_counted EV entries in
  let '(owners, owner_events) := audit_loop_owners_counted EV entries in
  (LoopForest headers nodes parents owners, entry_events ++ [AuditLoopOutput (length headers)] ++
    node_events ++ parent_events ++ owner_events).

Fixpoint audit_loop_trie_nodes_ne {A} (node : Trie.ne A) : nat :=
  match node with
  | Trie.N001 r => S (audit_loop_trie_nodes_ne r)
  | Trie.N010 _ => 1
  | Trie.N011 _ r => S (audit_loop_trie_nodes_ne r)
  | Trie.N100 l => S (audit_loop_trie_nodes_ne l)
  | Trie.N101 l r => S (audit_loop_trie_nodes_ne l + audit_loop_trie_nodes_ne r)
  | Trie.N110 l _ => S (audit_loop_trie_nodes_ne l)
  | Trie.N111 l _ r => S (audit_loop_trie_nodes_ne l + audit_loop_trie_nodes_ne r)
  end.

Definition audit_loop_trie_nodes {A} (m : Trie.t A) : nat :=
  match m with
  | Trie.Empty => 0
  | Trie.Nodes node => audit_loop_trie_nodes_ne node
  end.

Definition audit_loop_event_work {V E} (EV : encoding V) (event : audit_loop_call V E) : nat :=
  64 +
  match event with
  | AuditLoopDfs item => audit_dfs_full_model_event EV item
  | AuditLoopScc item => audit_tarjan_event_work EV item
  | AuditLoopRead v _ _
  | AuditLoopEdges v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditLoopSet v _
  | AuditLoopNodeWrite v _ _
  | AuditLoopParentWrite v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditLoopEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditLoopCompare a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | AuditLoopMap _ input _ => 64 * S (audit_loop_trie_nodes input) * S (audit_loop_trie_nodes input)
  | AuditLoopUnion lhs rhs _ => let nodes := audit_loop_trie_nodes lhs + audit_loop_trie_nodes rhs
    in
      64 * S nodes * S nodes
  | AuditLoopOutput size => S size
  | AuditLoopDepth size depth => audit_unary_conversion_weight size + size * S (N.to_nat depth)
  | _ => 0
  end.

Definition audit_loop_model_work {V E} (EV : encoding V) (events : list (audit_loop_call V E)) :
  nat :=
  512 * S (length events) * S (length events) +
    fold_right (fun event total => audit_loop_event_work EV event + total) 0 events.

Definition audit_loop_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat := 64 * S (audit_wto_input_event_bound p) * S
      (audit_wto_input_event_bound p).

Definition audit_loop_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let n := audit_wto_input_order_bound p in
  let events := audit_loop_input_event_bound p in
  let width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (audit_key_bits_weight (Pos.of_succ_nat (2 + n * S (Pos.to_nat (fuel p))))) in
  4096 * Nat.pow (S events) 4 * Nat.pow (S width) 2.

(** Counted loop-forest construction returns the forest with bounded events and work. *)
Definition audit_loop_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    let '(result, events) := audit_loop_counted p in
    result = loop_forest_of p /\
    length events <= audit_loop_input_event_bound p /\
    audit_loop_model_work EV events <= audit_loop_input_budget EV g p.

Definition audit_loop_singleton_graph : Graph.t positive positive :=
  Graph.Make [1%positive] [1%positive] (fun _ => [1%positive]) (fun e => e) (fun e => e).

(** Events retain actual operands, callbacks and primitive traces. *)
Inductive audit_loop_steps_event (V E B : Type) : Type :=
  | LoopStepsCase : nat -> audit_loop_steps_event V E B
  | LoopStepsRank : audit_map_event V positive B -> audit_loop_steps_event V E B
  | LoopStepsEdges : audit_map_event V (list E) B -> audit_loop_steps_event V E B
  | LoopStepsTarget : E -> V -> list B -> audit_loop_steps_event V E B
  | LoopStepsEncode : V -> positive -> list B -> audit_loop_steps_event V E B
  | LoopStepsEq : positive -> positive -> bool -> list audit_positive_eqb_event ->
    audit_loop_steps_event V E B
  | LoopStepsLe : positive -> positive -> bool -> list audit_positive_compare_event ->
    audit_loop_steps_event V E B.
Arguments LoopStepsCase {V E B} _.
Arguments LoopStepsRank {V E B} _.
Arguments LoopStepsEdges {V E B} _.
Arguments LoopStepsTarget {V E B} _ _ _.
Arguments LoopStepsEncode {V E B} _ _ _.
Arguments LoopStepsEq {V E B} _ _ _ _.
Arguments LoopStepsLe {V E B} _ _ _ _.

(** Header selection compares actual ranks after recursively inspecting the suffix. *)
Fixpoint audit_loop_steps_choose {V E B} (enc : V -> positive * list B)
    (numbers : Map.t V positive) (vertices : list V) : option V * list (audit_loop_steps_event V E
      B) :=
  match vertices with
  | [] => (None, [LoopStepsCase 0])
  | v :: rest =>
      let '(chosen, later) := audit_loop_steps_choose enc numbers rest in
      match chosen with
      | None => (Some v, LoopStepsCase 1 :: later)
      | Some w =>
          let '(ra, ea) := audit_map_get enc w numbers in
          let '(rb, eb) := audit_map_get enc v numbers in
          let a :=
            match ra with
            | Some x => x
            | None => 1%positive
            end in
          let b :=
            match rb with
            | Some x => x
            | None => 1%positive
            end in
          let '(le, ec) := audit_positive_leb a b in
          (Some (if le then v else w), LoopStepsCase 2 :: later ++ map LoopStepsRank ea ++
            map LoopStepsRank eb ++ [LoopStepsLe a b le ec])
      end
  end.

(** Equality compares both actual encoder calls and the positive primitive trace. *)
Definition audit_loop_steps_equal {V E B} (enc : V -> positive * list B) (v h : V)
    : bool * list (audit_loop_steps_event V E B) :=
  let '(a, ea) := enc v in let '(b, eb) := enc h in
  let '(eq, events) := audit_positive_eqb a b in
  (eq, [LoopStepsEncode v a ea; LoopStepsEncode h b eb; LoopStepsEq a b eq events]).

(** Removing a header tests every component occurrence. *)
Fixpoint audit_loop_steps_without {V E B} (enc : V -> positive * list B) (h : V) (vertices : list V)
    : list V * list (audit_loop_steps_event V E B) :=
  match vertices with
  | [] => ([], [LoopStepsCase 3])
  | v :: rest =>
      let '(eq, here) := audit_loop_steps_equal enc v h in
      let '(later, events) := audit_loop_steps_without enc h rest in
      (if eq then later else v :: later, LoopStepsCase 4 :: here ++ events)
  end.

(** The strict edge scan retains calls after the first self edge. *)
Fixpoint audit_loop_steps_self {V E B} (enc : V -> positive * list B) (target : E -> V * list B)
    (v : V) (edges : list E) : bool * list (audit_loop_steps_event V E B) :=
  match edges with
  | [] => (false, [LoopStepsCase 5])
  | edge :: rest =>
      let '(dst, body) := target edge in
      let '(eq, here) := audit_loop_steps_equal enc dst v in
      let '(later, events) := audit_loop_steps_self enc target v rest in
      (eq || later, LoopStepsCase 6 :: LoopStepsTarget edge dst body :: here ++ events)
  end.

(** Empty, singleton and larger components follow their source branches. *)
Definition audit_loop_steps_cyclic {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (enc : V -> positive * list B) (target : E -> V * list B)
    (vertices : list V) : bool * list (audit_loop_steps_event V E B) :=
  match vertices with
  | [] => (false, [LoopStepsCase 7])
  | [v] =>
      let '(found, reads) := audit_map_get enc v (out_index p) in
      let edges :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(result, events) := audit_loop_steps_self enc target v edges in
      (result, LoopStepsCase 8 :: map LoopStepsEdges reads ++ events)
  | _ :: _ :: _ => (true, [LoopStepsCase 9])
  end.

(** These primitive source models erase to the actual loop operations. *)
Definition audit_loop_steps_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (enc : V -> positive * list B) (target : E -> V * list B),
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall numbers vertices, fst (audit_loop_steps_choose (E := E) enc numbers vertices) =
      loop_choose EV numbers vertices) /\
    (forall h vertices, fst (audit_loop_steps_without (E := E) enc h vertices) = loop_without EV h
      vertices) /\
    (forall vertices, fst (audit_loop_steps_cyclic p enc target vertices) = loop_cyclic p vertices).

(** Work charges actual primitive operations and their attached callback bodies. *)
Definition audit_loop_steps_event_work {V E B} (weight : B -> nat) (event : audit_loop_steps_event
  V E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 +
  match event with
  | LoopStepsCase _ => 0
  | LoopStepsRank call => audit_map_source_work body [call]
  | LoopStepsEdges call => audit_map_source_work body [call]
  | LoopStepsTarget _ _ xs
  | LoopStepsEncode _ _ xs => body xs
  | LoopStepsEq _ _ _ calls => audit_positive_eqb_source_work calls
  | LoopStepsLe _ _ _ calls => audit_positive_order_source_work calls
  end.

(** External charges are the bodies of the actual supplied callbacks. *)
Definition audit_loop_steps_event_external {V E B} (weight : B -> nat)
    (event : audit_loop_steps_event V E B) : nat :=
  match event with
  | LoopStepsTarget _ _ body
  | LoopStepsEncode _ _ body
  | LoopStepsRank (AuditMapGet _ _ _ _ body _)
  | LoopStepsRank (AuditMapSet _ _ _ _ _ body _)
  | LoopStepsRank (AuditMapRemove _ _ _ _ body _)
  | LoopStepsEdges (AuditMapGet _ _ _ _ body _)
  | LoopStepsEdges (AuditMapSet _ _ _ _ _ body _)
  | LoopStepsEdges (AuditMapRemove _ _ _ _ body _)
      =>
      fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Sum work for this invocation's source events. *)
Definition audit_loop_steps_work {V E B} (weight : B -> nat) (events : list
  (audit_loop_steps_event V E B)) : nat :=
  fold_right (fun event n => audit_loop_steps_event_work weight event + n) 0 events.

(** Sum the actual external bodies of those same events. *)
Definition audit_loop_steps_external {V E B} (weight : B -> nat)
    (events : list (audit_loop_steps_event V E B)) : nat :=
  fold_right (fun event n => audit_loop_steps_event_external weight event + n) 0 events.

(** The shared bound measures all actual input lists, keys, ranks and successor targets. *)
Definition audit_loop_steps_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (numbers : Map.t V positive) (vertices : list V) (h : V) : nat :=
  let rank_rows := Map.elements numbers in
  let edge_rows := Map.elements (out_index p) in
  let edges := flat_map snd edge_rows in
  let keys := h :: vertices ++ map fst rank_rows ++ map fst edge_rows ++ map (Graph.target g)
    edges in
  let width := Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) keys))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) rank_rows)) in
  4096 * Nat.pow (S (length keys + length edges + length rank_rows + width)) 6.

(** Each helper's work is bounded by inputs and its actual external callback bodies. *)
Definition audit_loop_steps_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) numbers vertices h
    (enc : V -> positive * list B) (target : E -> V * list B) (weight : B -> nat),
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    let budget := audit_loop_steps_budget EV g p numbers vertices h in
    let choose_events := snd (audit_loop_steps_choose (E := E) enc numbers vertices) in
    let without_events := snd (audit_loop_steps_without (E := E) enc h vertices) in
    let cyclic_events := snd (audit_loop_steps_cyclic p enc target vertices) in
    audit_loop_steps_work weight choose_events <= budget + audit_loop_steps_external weight
      choose_events /\
    audit_loop_steps_work weight without_events <= budget + audit_loop_steps_external weight
      without_events /\
    audit_loop_steps_work weight cyclic_events <= budget + audit_loop_steps_external weight
      cyclic_events.

(** Events preserve actual operands, results and the supplied encoding bodies. *)
Inductive audit_loop_pack_event (V B : Type) : Type :=
  | LoopPackCase : nat -> audit_loop_pack_event V B
  | LoopPackSet : audit_set_event V B -> audit_loop_pack_event V B
  | LoopPackNodes : audit_map_event V (FinSet.t V) B -> audit_loop_pack_event V B
  | LoopPackParent : audit_map_event V V B -> audit_loop_pack_event V B
  | LoopPackTransform : audit_map_transform_event V unit V unit -> audit_loop_pack_event V B
  | LoopPackUnion : audit_map_union_event V V unit -> audit_loop_pack_event V B.
Arguments LoopPackCase {V B} _.
Arguments LoopPackSet {V B} _.
Arguments LoopPackNodes {V B} _.
Arguments LoopPackParent {V B} _.
Arguments LoopPackTransform {V B} _.
Arguments LoopPackUnion {V B} _.

(** Node sets are built for each entry before inserting its header binding. *)
Fixpoint audit_loop_pack_nodes {V B} (enc : V -> positive * list B) (entries : list (loop_entry V))
    : Map.t V (FinSet.t V) * list (audit_loop_pack_event V B) :=
  match entries with
  | [] => (Map.empty, [LoopPackCase 0])
  | entry :: rest =>
      let '(index, later) := audit_loop_pack_nodes enc rest in
      let '(members, set_events) := audit_finset_of_list enc (loop_members entry) in
      let '(result, writes) := audit_map_set enc (loop_head entry) members index in
      (result, LoopPackCase 1 :: later ++ map LoopPackSet set_events ++ map LoopPackNodes writes)
  end.

(** Missing enclosing headers create no parent binding. *)
Fixpoint audit_loop_pack_parents {V B} (enc : V -> positive * list B) (entries : list (loop_entry
  V))
    : Map.t V V * list (audit_loop_pack_event V B) :=
  match entries with
  | [] => (Map.empty, [LoopPackCase 2])
  | entry :: rest =>
      let '(index, later) := audit_loop_pack_parents enc rest in
      match loop_enclosing entry with
      | None => (index, LoopPackCase 3 :: later)
      | Some parent =>
          let '(result, writes) := audit_map_set enc (loop_head entry) parent index in
          (result, LoopPackCase 4 :: later ++ map LoopPackParent writes)
      end
  end.

(** The actual transformation and union callbacks are fixed internal functions. *)
Fixpoint audit_loop_pack_owners {V B} (enc : V -> positive * list B) (entries : list (loop_entry V))
    : Map.t V V * list (audit_loop_pack_event V B) :=
  match entries with
  | [] => (Map.empty, [LoopPackCase 5])
  | entry :: rest =>
      let '(members, set_events) := audit_finset_of_list enc (loop_members entry) in
      let '(mapped, map_events) := audit_map_transform (fun _ : unit => (loop_head entry, []))
        members in
      let '(deeper, later) := audit_loop_pack_owners enc rest in
      let '(result, union_events) := audit_map_union (fun (_ x : V) => (x, [])) mapped deeper in
      (result, LoopPackCase 6 :: map LoopPackSet set_events ++ map LoopPackTransform map_events ++
        later ++ map LoopPackUnion union_events)
  end.

(** Pack the actual observations in source order. *)
Definition audit_loop_pack_source_counted {V B} (enc : V -> positive * list B)
    (entries : list (loop_entry V)) : loop_forest V * list (audit_loop_pack_event V B) :=
  let headers := map loop_head entries in
  let '(nodes, node_events) := audit_loop_pack_nodes enc entries in
  let '(parents, parent_events) := audit_loop_pack_parents enc entries in
  let '(owners, owner_events) := audit_loop_pack_owners enc entries in
  (LoopForest headers nodes parents owners,
    LoopPackCase 7 :: node_events ++ parent_events ++ owner_events).

(** Work charges each collection primitive and the actual supplied encoder bodies. *)
Definition audit_loop_pack_event_work {V B} (weight : B -> nat) (event : audit_loop_pack_event V
  B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 +
  match event with
  | LoopPackCase _ => 0
  | LoopPackSet call => audit_finset_source_work body [call]
  | LoopPackNodes call => audit_map_source_work body [call]
  | LoopPackParent call => audit_map_source_work body [call]
  | LoopPackTransform call => audit_map_transform_source_work (fun _ => 0) [call]
  | LoopPackUnion call => audit_map_union_source_work (fun _ => 0) [call]
  end.

(** Only actual encoder calls have external bodies in packing. *)
Definition audit_loop_pack_event_external {V B} (weight : B -> nat)
    (event : audit_loop_pack_event V B) : nat :=
  match event with
  | LoopPackSet (AuditSetAdd _ _ _ _ body _)
  | LoopPackSet (AuditSetMem _ _ _ _ body _)
  | LoopPackSet (AuditSetRemove _ _ _ _ body _)
  | LoopPackNodes (AuditMapGet _ _ _ _ body _)
  | LoopPackNodes (AuditMapSet _ _ _ _ _ body _)
  | LoopPackNodes (AuditMapRemove _ _ _ _ body _)
  | LoopPackParent (AuditMapGet _ _ _ _ body _)
  | LoopPackParent (AuditMapSet _ _ _ _ _ body _)
  | LoopPackParent (AuditMapRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Packing work sums this execution's events. *)
Definition audit_loop_pack_source_work {V B} (weight : B -> nat) (events : list
  (audit_loop_pack_event V B)) : nat :=
  fold_right (fun event n => audit_loop_pack_event_work weight event + n) 0 events.

(** External cost sums the bodies recorded by this execution. *)
Definition audit_loop_pack_source_external {V B} (weight : B -> nat)
    (events : list (audit_loop_pack_event V B)) : nat :=
  fold_right (fun event n => audit_loop_pack_event_external weight event + n) 0 events.

(** Input size measures headers, all members and their actual encoding widths. *)
Definition audit_loop_pack_input_scale {V} (EV : encoding V) (entries : list (loop_entry V)) : nat
  :=
  let vertices := map loop_head entries ++ flat_map loop_members entries ++
    flat_map (fun entry =>
      match loop_enclosing entry with
      | Some v => [v]
      | None => []
      end) entries
      in
  S (length entries + length vertices + fold_right Nat.max 0
    (map (fun v => Pos.size_nat (encode EV v)) vertices)).

(** This bound depends only on the entries and supplied encoding. *)
Definition audit_loop_pack_source_budget {V} (EV : encoding V) (entries : list (loop_entry V)) :
  nat :=
  4096 * Nat.pow (audit_loop_pack_input_scale EV entries) 8.

(** The packed forest and source-work bound hold for arbitrary input entries. *)
Definition audit_loop_pack_source_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) entries,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_loop_pack_source_counted enc entries in
    result = loop_pack EV entries /\ audit_loop_pack_source_work weight events <=
      audit_loop_pack_source_budget EV entries + audit_loop_pack_source_external weight events.

(** Each event embeds a concrete source operation or a fixed local branch. *)
Inductive audit_loop_full_event (V E B : Type) : Type :=
  | LoopFullCase : nat -> audit_loop_full_event V E B
  | LoopFullOutput : nat -> audit_loop_full_event V E B
  | LoopFullDepth : nat -> N -> audit_loop_full_event V E B
  | LoopFullDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
      audit_loop_full_event V E B
  | LoopFullScc : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B) ->
      audit_loop_full_event V E B
  | LoopFullStep : audit_loop_steps_event V E B -> audit_loop_full_event V E B
  | LoopFullPack : audit_loop_pack_event V B -> audit_loop_full_event V E B.
Arguments LoopFullCase {V E B} _.
Arguments LoopFullOutput {V E B} _.
Arguments LoopFullDepth {V E B} _ _.
Arguments LoopFullDfs {V E B} _.
Arguments LoopFullScc {V E B} _.
Arguments LoopFullStep {V E B} _.
Arguments LoopFullPack {V E B} _.

(** A block records the actual cyclic test, choice, removal and descendant invocation. *)
Definition audit_loop_full_block {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_full_event V E B))
    (parent : option V) (region component : list V) : list (loop_entry V) * list
      (audit_loop_full_event V E B) :=
  let enc := audit_dfs_encode_model cb in
  let '(cyclic, cycle_events) := audit_loop_steps_cyclic p enc (audit_dfs_target_model cb)
    component in
  if cyclic then
    let '(chosen, choice_events) := audit_loop_steps_choose (E := E) enc numbers component in
    match chosen with
    | None => ([], map LoopFullStep cycle_events ++ [LoopFullCase 0] ++ map LoopFullStep
      choice_events)
    | Some h =>
        let '(smaller, remove_events) := audit_loop_steps_without (E := E) enc h component in
        let '(children, child_events) := descend (Some h) smaller in
        (LoopEntry h component parent region :: children,
          map LoopFullStep cycle_events ++ [LoopFullCase 1] ++ map LoopFullStep choice_events ++
          map LoopFullStep remove_events ++ child_events ++ [LoopFullOutput 1])
    end
  else ([], map LoopFullStep cycle_events ++ [LoopFullCase 2]).

(** The component fold preserves occurrence order and concatenation costs. *)
Fixpoint audit_loop_full_blocks {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_full_event V E B))
    (parent : option V) (region : list V) (components : list (list V))
    : list (loop_entry V) * list (audit_loop_full_event V E B) :=
  match components with
  | [] => ([], [LoopFullCase 3])
  | component :: rest =>
      let '(first, here) := audit_loop_full_block p cb numbers descend parent region component in
      let '(later, events) := audit_loop_full_blocks p cb numbers descend parent region rest in
      (first ++ later, LoopFullCase 4 :: here ++ events ++ [LoopFullOutput (length first)])
  end.

(** Each layer invokes the SCC source model on its actual region. *)
Definition audit_loop_full_layer {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_full_event V E B))
    (parent : option V) (region : list V) : list (loop_entry V) * list (audit_loop_full_event V E
      B) :=
  let '(sccs, calls) := audit_scc_source_counted p cb region in
  let '(result, events) := audit_loop_full_blocks p cb numbers descend parent region (components
    sccs) in
  (result, map LoopFullScc calls ++ events).

(** Binary iteration creates the same layer closures and uses the actual DFS output. *)
Definition audit_loop_full_entries {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : list (loop_entry V) * list (audit_loop_full_event V E B) :=
  let '(search, calls) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let depth := N.of_nat (length (preorder search)) in
  let base := fun (_ : option V) (_ : list V) => (@nil (loop_entry V), @nil (audit_loop_full_event
    V E B)) in
  let step := fun recur => (audit_loop_full_layer p cb (post_num search) recur, @nil
    (audit_loop_full_event V E B)) in
  let '(run, iter_events) := audit_n_iter depth step base in
  let '(result, events) := run None (preorder search) in
  (result, map LoopFullDfs calls ++ [LoopFullDepth (length (preorder search)) depth] ++
    map (fun event =>
      match event with
      | AuditCombCase site => LoopFullCase (10 + site)
      | AuditCombBody body => body
      end) iter_events ++ events).

(** The complete producer passes its actual entry list directly to packing. *)
Definition audit_loop_full_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : loop_forest V * list (audit_loop_full_event V E B) :=
  let '(entries, calls) := audit_loop_full_entries p cb in
  let '(result, packing) := audit_loop_pack_source_counted (audit_dfs_encode_model cb) entries in
  (result, calls ++ [LoopFullOutput (length entries)] ++ map LoopFullPack packing).

(** The complete counted producer returns the exact source forest. *)
Definition audit_loop_full_source_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B),
    audit_dfs_callbacks_erase EV g cb -> fst (audit_loop_full_source_counted p cb) =
      loop_forest_of p.

(** Work includes each nested body and source list concatenation. *)
Definition audit_loop_full_event_work {V E B} (weight : B -> nat) (event : audit_loop_full_event V
  E B) : nat :=
  64 +
  match event with
  | LoopFullCase _ => 0
  | LoopFullOutput n => S n
  | LoopFullDepth n _ => 16 * S n * S n
  | LoopFullDfs call => audit_dfs_source_event_work weight call
  | LoopFullScc call => audit_scc_source_event_work weight call
  | LoopFullStep call => audit_loop_steps_event_work weight call
  | LoopFullPack call => audit_loop_pack_event_work weight call
  end.

(** External charges use only captured bodies from this invocation. *)
Definition audit_loop_full_event_external {V E B} (weight : B -> nat)
    (event : audit_loop_full_event V E B) : nat :=
  match event with
  | LoopFullDfs call => audit_dfs_source_body_work weight [call]
  | LoopFullScc call => audit_scc_source_body_work weight [call]
  | LoopFullStep call => audit_loop_steps_event_external weight call
  | LoopFullPack call => audit_loop_pack_event_external weight call
  | _ => 0
  end.

(** The quadratic list allowance covers source trace composition and emitted prefixes. *)
Definition audit_loop_full_source_work {V E B} (weight : B -> nat)
    (events : list (audit_loop_full_event V E B)) : nat :=
  256 * S (length events) * S (length events) +
  fold_right (fun event n => audit_loop_full_event_work weight event + n) 0 events.

(** The same event list supplies the client body cost. *)
Definition audit_loop_full_source_external {V E B} (weight : B -> nat)
    (events : list (audit_loop_full_event V E B)) : nat :=
  fold_right (fun event n => audit_loop_full_event_external weight event + n) 0 events.

(** The original graph and prepared index determine the source-work bound. *)
Definition audit_loop_full_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let width := audit_dfs_full_input_width EV g p (Graph.entries g) in
  let count := audit_wto_input_event_bound p in
  let scale := S (count + width + Pos.to_nat (fuel p) + length (Graph.entries g) +
    audit_wto_input_max_out p) in
  (1024 * 1024)%nat * Nat.pow scale 8.

(** The whole producer returns the source forest with input-bounded source work. *)
Definition audit_loop_full_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_loop_full_source_counted p cb in
    result = loop_forest_of p /\ audit_loop_full_source_work weight events <=
      audit_loop_full_source_budget EV g p + audit_loop_full_source_external weight events.

(** Captured DFS and SCC calls retain their genuine client inputs. *)
Definition audit_loop_full_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (calls : list (audit_graph_callback_capture V E B)) : nat :=
  fold_right (fun call n => audit_scc_capture_budget encode_budget target_budget call + n) 0 calls.

(** Component and packing events expose only genuine external callback inputs. *)
Definition audit_loop_full_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_loop_full_event V E B) : nat :=
  match event with
  | LoopFullDfs (_, calls)
  | LoopFullScc (_, calls) =>
      audit_loop_full_capture_budget encode_budget target_budget calls
  | LoopFullStep (LoopStepsTarget e _ _) => target_budget e
  | LoopFullStep (LoopStepsEncode v _ _) => encode_budget v
  | LoopFullStep (LoopStepsRank (AuditMapGet v _ _ _ _ _))
  | LoopFullStep (LoopStepsRank (AuditMapSet v _ _ _ _ _ _))
  | LoopFullStep (LoopStepsRank (AuditMapRemove v _ _ _ _ _))
  | LoopFullStep (LoopStepsEdges (AuditMapGet v _ _ _ _ _))
  | LoopFullStep (LoopStepsEdges (AuditMapSet v _ _ _ _ _ _))
  | LoopFullStep (LoopStepsEdges (AuditMapRemove v _ _ _ _ _))
  | LoopFullPack (LoopPackSet (AuditSetAdd v _ _ _ _ _))
  | LoopFullPack (LoopPackSet (AuditSetMem v _ _ _ _ _))
  | LoopFullPack (LoopPackSet (AuditSetRemove v _ _ _ _ _))
  | LoopFullPack (LoopPackNodes (AuditMapGet v _ _ _ _ _))
  | LoopFullPack (LoopPackNodes (AuditMapSet v _ _ _ _ _ _))
  | LoopFullPack (LoopPackNodes (AuditMapRemove v _ _ _ _ _))
  | LoopFullPack (LoopPackParent (AuditMapGet v _ _ _ _ _))
  | LoopFullPack (LoopPackParent (AuditMapSet v _ _ _ _ _ _))
  | LoopFullPack (LoopPackParent (AuditMapRemove v _ _ _ _ _)) => encode_budget v
  | _ => 0
  end.

(** The full traversal has an input-derived bound and budgets for its actual client calls. *)
Definition audit_loop_full_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    let '(result, events) := audit_loop_full_source_counted p cb in
    result = loop_forest_of p /\ audit_loop_full_source_work weight events <=
      audit_loop_full_source_budget EV g p +
      fold_right (fun event n => audit_loop_full_event_budget encode_budget target_budget event +
        n) 0 events.

(** The full source contract joins erasure, recorded-body, adapted and SCC source obligations. *)
Definition audit_loop_full_source_contract_statement : Prop :=
  audit_loop_full_source_erasure_statement /\ audit_loop_full_source_statement /\
  audit_loop_full_source_adapted_statement /\ audit_scc_source_contract_statement /\
  audit_loop_steps_erasure_statement /\ audit_loop_steps_bound_statement /\
  audit_loop_pack_source_statement.
