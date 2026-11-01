(** * SSA query component source contracts

    Record value preparation, online queries, R/T rows and T closure source work.
    For example, a retained T edge keeps every actual target and membership call.
    Builds on: SSA query indexes and graph and collection source models. *)
From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTrie
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements
  CollectionsAuditPrimitive CollectionsAuditCompare CollectionsAuditUnion.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators GraphAuditBase
  GraphAuditDfs
  GraphAuditVirtual GraphAuditSemiDominators GraphAuditLengauerTarjan GraphAuditDominators
  GraphAuditFrontier.
From Galois.Views Require Import ViewsGraph ViewsSsaPoints.
From Galois.Analyses Require Import AnalysesSsaLiveQuery.
Import List.ListNotations.

(** * SSA query component source contracts *)

(** Events retain actual source operations and encoder callback bodies. *)
Inductive audit_sq_query_source_event (N E V B : Type) : Type :=
  | SqQueryCase : nat -> audit_sq_query_source_event N E V B
  | SqQueryDef : audit_map_event V N B -> audit_sq_query_source_event N E V B
  | SqQueryUses : audit_map_event V (FinSet.t N) B -> audit_sq_query_source_event N E V B
  | SqQueryRows : audit_map_event N (FinSet.t N) B -> audit_sq_query_source_event N E V B
  | SqQueryElements : audit_set_elements_event N -> audit_sq_query_source_event N E V B
  | SqQueryEncode : N -> positive -> list B -> audit_sq_query_source_event N E V B
  | SqQueryEqual : positive -> positive -> bool -> list audit_positive_eqb_event ->
    audit_sq_query_source_event N E V B
  | SqQueryDom : audit_frontier_source_event N E B -> audit_sq_query_source_event N E V B
  | SqQueryMem : audit_set_event N B -> audit_sq_query_source_event N E V B.

Arguments SqQueryCase {N E V B} _.

Arguments SqQueryDef {N E V B} _.

Arguments SqQueryUses {N E V B} _.

Arguments SqQueryRows {N E V B} _.

Arguments SqQueryElements {N E V B} _.

Arguments SqQueryEncode {N E V B} _ _ _.

Arguments SqQueryEqual {N E V B} _ _ _ _.

Arguments SqQueryDom {N E V B} _.

Arguments SqQueryMem {N E V B} _.

(** Each membership scan visits its full occurrence list. *)
Fixpoint audit_sq_query_source_members {N E V B} (enc : N -> positive * list B)
    (set : FinSet.t N) (uses : list N) : bool * list (audit_sq_query_source_event N E V B) :=
  match uses with
  | [] => (false, [SqQueryCase 0])
  | u :: rest =>
    let '(found, reads) := audit_finset_mem enc u set in
    let '(later, events) := audit_sq_query_source_members enc set rest in
    (found || later, SqQueryCase 1 :: map SqQueryMem reads ++ events)
  end.

(** Each closure row evaluates equality, dominance and the complete use scan. *)
Fixpoint audit_sq_query_source_rows {N E V B} (enc : N -> positive * list B)
    (idx : ssa_query_graph N E) (d : N) (uses rows : list N) :
    bool * list (audit_sq_query_source_event N E V B) :=
  match rows with
  | [] => (false, [SqQueryCase 2])
  | n :: rest =>
    let '(a, ea) := enc d in let '(b, eb) := enc n in
    let '(same, comparisons) := audit_positive_eqb a b in
    let '(dom, dom_calls) := audit_frontier_source_dom enc (query_dom idx) d n in
    let '(found, reads) := audit_map_get enc n (query_reduced idx) in
    let reduced := match found with
    Some s => s
    | None => FinSet.empty
    end in
    let '(member, members) := audit_sq_query_source_members enc reduced uses in
    let '(later, events) := audit_sq_query_source_rows enc idx d uses rest in
    (negb same && dom && member || later,
      SqQueryCase 3 :: SqQueryEncode d a ea :: SqQueryEncode n b eb ::
      SqQueryEqual a b same comparisons :: map SqQueryDom dom_calls ++ map SqQueryRows reads ++
      members ++ events)
  end.

(** A definition miss takes the source's early return; a hit runs the full indexed query. *)
Definition audit_sq_query_source_counted {N E V B} (encn : N -> positive * list B)
    (encv : V -> positive * list B) (idx : ssa_query_graph N E) (values : ssa_query_values N V)
    (n : N) (x : V) : bool * list (audit_sq_query_source_event N E V B) :=
  let '(definition, definition_reads) := audit_map_get encv x (query_def values) in
  match definition with
  | None => (false, map SqQueryDef definition_reads ++ [SqQueryCase 4])
  | Some d =>
    let '(uses, use_reads) := audit_map_get encv x (query_uses values) in
    let use_set := match uses with
    Some s => s
    | None => FinSet.empty
    end in
    let '(use_list, use_events) := audit_finset_elements use_set in
    let '(rows, row_reads) := audit_map_get encn n (query_back_closure idx) in
    let row_set := match rows with
    Some s => s
    | None => FinSet.empty
    end in
    let '(row_list, row_events) := audit_finset_elements row_set in
    let '(result, events) := audit_sq_query_source_rows encn idx d use_list row_list in
    (result, map SqQueryDef definition_reads ++ [SqQueryCase 5] ++ map SqQueryUses use_reads ++
      map SqQueryElements use_events ++ map SqQueryRows row_reads ++
      map SqQueryElements row_events ++ events)
  end.

(** Source work includes actual trie, enumeration, arithmetic and callback bodies. *)
Definition audit_sq_query_source_event_work {N E V B} (weight : B -> nat)
    (event : audit_sq_query_source_event N E V B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SqQueryCase _ => 0
  | SqQueryDef call => audit_map_source_work body [call]
  | SqQueryUses call => audit_map_source_work body [call]
  | SqQueryRows call => audit_map_source_work body [call]
  | SqQueryElements call => audit_set_elements_work [call]
  | SqQueryEncode _ _ xs => body xs
  | SqQueryEqual _ _ _ calls => audit_positive_eqb_source_work calls
  | SqQueryDom call => audit_frontier_source_event_work weight call
  | SqQueryMem call => audit_finset_source_work body [call]
  end.

(** External work contains only actual node and value encoder bodies. *)
Definition audit_sq_query_source_event_external {N E V B} (weight : B -> nat)
    (event : audit_sq_query_source_event N E V B) : nat :=
  match event with
  | SqQueryEncode _ _ body | SqQueryDef (AuditMapGet _ _ _ _ body _) |
    SqQueryDef (AuditMapSet _ _ _ _ _ body _) | SqQueryDef (AuditMapRemove _ _ _ _ body _) |
    SqQueryUses (AuditMapGet _ _ _ _ body _) | SqQueryUses (AuditMapSet _ _ _ _ _ body _) |
    SqQueryUses (AuditMapRemove _ _ _ _ body _) | SqQueryRows (AuditMapGet _ _ _ _ body _) |
    SqQueryRows (AuditMapSet _ _ _ _ _ body _) | SqQueryRows (AuditMapRemove _ _ _ _ body _) |
    SqQueryMem (AuditSetMem _ _ _ _ body _) | SqQueryMem (AuditSetAdd _ _ _ _ body _) |
    SqQueryMem (AuditSetRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | SqQueryDom call => audit_frontier_source_body_event_work weight call
  | _ => 0
  end.

(** Source work charges recorded frames and trace-list composition. *)
Definition audit_sq_query_source_work {N E V B} (weight : B -> nat)
    (events : list (audit_sq_query_source_event N E V B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_sq_query_source_event_work weight event + n) 0 events.

(** Callback cost is taken from the same recorded events. *)
Definition audit_sq_query_source_external {N E V B} (weight : B -> nat)
    (events : list (audit_sq_query_source_event N E V B)) : nat :=
  fold_right (fun event n => audit_sq_query_source_event_external weight event + n) 0 events.

(** The input scale covers all supplied indexes, stored sets, encoded keys and rank widths. *)
Definition audit_sq_query_source_input_scale {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (n : N) (x : V) : nat :=
  let defs := Map.elements (query_def values) in let uses := Map.elements (query_uses values) in
  let reduced := Map.elements (query_reduced idx) in
  let closure := Map.elements (query_back_closure idx) in
  let starts := Map.elements (tin (query_dom idx)) in let ends := Map.elements (tout (query_dom
    idx)) in
  let sets := map snd uses ++ map snd reduced ++ map snd closure in
  let nodes := n :: map snd defs ++ map fst reduced ++ map fst closure ++ map fst starts ++
    map fst ends ++ flat_map FinSet.elements sets in
  let vars := x :: map fst defs ++ map fst uses in
  let node_width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EN v)) nodes) in
  let var_width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vars) in
  let rank_width := fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (starts ++ ends))
    in
  let set_nodes := fold_right (fun s total => audit_trie_nodes s + audit_trie_output_bits s + total)
    0 sets in
  S (length nodes + length vars + node_width + var_width + rank_width + set_nodes +
    audit_trie_nodes (query_def values) + audit_trie_nodes (query_uses values) +
    audit_trie_nodes (query_reduced idx) + audit_trie_nodes (query_back_closure idx) +
    audit_trie_nodes (tin (query_dom idx)) + audit_trie_nodes (tout (query_dom idx))).

(** The query budget depends only on supplied indexes, encodings and query arguments. *)
Definition audit_sq_query_source_input_budget {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (n : N) (x : V) : nat :=
  (N.to_nat 1048576%N) * Nat.pow (audit_sq_query_source_input_scale EN EV idx values n x) 8.

(** The online query erases to the original result and has a complete source-work bound. *)
Definition audit_sq_query_source_statement : Prop :=
  forall N E V B (EN : encoding N) (EV : encoding V) (idx : ssa_query_graph N E)
    (values : ssa_query_values N V) n x (encn : N -> positive * list B)
    (encv : V -> positive * list B)
    (weight : B -> nat),
    (forall v, fst (encn v) = encode EN v) -> (forall v, fst (encv v) = encode EV v) ->
    let '(result, events) := audit_sq_query_source_counted encn encv idx values n x in
    result = ssa_live_query EN EV idx values n x /\ audit_sq_query_source_work weight events <=
      audit_sq_query_source_input_budget EN EV idx values n x +
      audit_sq_query_source_external weight events.

(** Every query event prices its actual node or value input. *)
Definition audit_sq_query_source_event_budget {N E V B} (node_budget : N -> nat)
    (value_budget : V -> nat)
    (event : audit_sq_query_source_event N E V B) : nat :=
  match event with
  | SqQueryEncode n _ _ => node_budget n
  | SqQueryDef (AuditMapGet x _ _ _ _ _) | SqQueryDef (AuditMapSet x _ _ _ _ _ _) |
    SqQueryDef (AuditMapRemove x _ _ _ _ _) | SqQueryUses (AuditMapGet x _ _ _ _ _) |
    SqQueryUses (AuditMapSet x _ _ _ _ _ _) | SqQueryUses (AuditMapRemove x _ _ _ _ _) =>
    value_budget x
  | SqQueryRows (AuditMapGet n _ _ _ _ _) | SqQueryRows (AuditMapSet n _ _ _ _ _ _) |
    SqQueryRows (AuditMapRemove n _ _ _ _ _) | SqQueryMem (AuditSetMem n _ _ _ _ _) |
    SqQueryMem (AuditSetAdd n _ _ _ _ _) | SqQueryMem (AuditSetRemove n _ _ _ _ _) => node_budget n
  | SqQueryDom (FrontierSourceRank (AuditMapGet n _ _ _ _ _)) |
    SqQueryDom (FrontierSourceRank (AuditMapSet n _ _ _ _ _ _)) |
    SqQueryDom (FrontierSourceRank (AuditMapRemove n _ _ _ _ _)) => node_budget n
  | _ => 0
  end.

(** Under encoder laws, the query returns the source answer within the per-call work bound. *)
Definition audit_sq_query_source_adapted_statement : Prop :=
  forall N E V B (EN : encoding N) (EV : encoding V) (idx : ssa_query_graph N E)
    (values : ssa_query_values N V) n x (encn : N -> positive * list B)
    (encv : V -> positive * list B)
    (weight : B -> nat) node_source value_source node_budget value_budget,
    (forall v, fst (encn v) = encode EN v) -> (forall v, fst (encv v) = encode EV v) ->
    audit_graph_external_callback_adapter encn weight node_source node_budget ->
    audit_graph_external_callback_adapter encv weight value_source value_budget ->
    let '(result, events) := audit_sq_query_source_counted encn encv idx values n x in
    result = ssa_live_query EN EV idx values n x /\ audit_sq_query_source_work weight events <=
      audit_sq_query_source_input_budget EN EV idx values n x +
      fold_right (fun event total => audit_sq_query_source_event_budget node_budget value_budget
        event + total) 0 events.

(** The complete online-query contract includes primitive and adapted source obligations. *)
Definition audit_sq_query_source_contract_statement : Prop :=
  audit_sq_query_source_statement /\ audit_sq_query_source_adapted_statement /\
  audit_map_get_source_work_bound_statement /\ audit_finset_mem_erases_statement /\
  audit_finset_elements_erases_statement /\ audit_finset_elements_work_bound_statement /\
  audit_positive_eqb_erases_statement /\ audit_positive_eqb_source_bound_statement /\
  audit_positive_compare_cont_statement /\ audit_positive_order_statement.

(** Supplied callbacks retain their actual input, result and source body. *)
Record audit_sq_values_callbacks (N E V B : Type) : Type := SqValuesCallbacks {
  sq_values_node_encode : N -> positive * list B;
  sq_values_value_encode : V -> positive * list B;
  sq_values_out : N -> list E * list B;
  sq_values_target : E -> N * list B;
  sq_values_exit : N -> list V * list B;
  sq_values_edge : E -> list V * list B;
  sq_values_home : V -> option N * list B
}.

Arguments sq_values_node_encode {N E V B} _ _.

Arguments sq_values_value_encode {N E V B} _ _.

Arguments sq_values_out {N E V B} _ _.

Arguments sq_values_target {N E V B} _ _.

Arguments sq_values_exit {N E V B} _ _.

Arguments sq_values_edge {N E V B} _ _.

Arguments sq_values_home {N E V B} _ _.

(** Events retain actual graph, operand and collection calls. *)
Inductive audit_sq_values_source_event (N E V B : Type) : Type :=
  | SqValuesCase : nat -> audit_sq_values_source_event N E V B
  | SqValuesPrepare : audit_prepare_source_event N E B -> audit_sq_values_source_event N E V B
  | SqValuesDfs : audit_dfs_nested_event N E (audit_graph_callback_capture N E B) ->
    audit_sq_values_source_event N E V B
  | SqValuesOut : N -> list E -> list B -> audit_sq_values_source_event N E V B
  | SqValuesExit : N -> list V -> list B -> audit_sq_values_source_event N E V B
  | SqValuesEdge : E -> list V -> list B -> audit_sq_values_source_event N E V B
  | SqValuesHome : V -> option N -> list B -> audit_sq_values_source_event N E V B
  | SqValuesUseMap : audit_map_event V (FinSet.t N) B -> audit_sq_values_source_event N E V B
  | SqValuesDefMap : audit_map_event V N B -> audit_sq_values_source_event N E V B
  | SqValuesSet : audit_set_event N B -> audit_sq_values_source_event N E V B
  | SqValuesElements : audit_elements_event (V * FinSet.t N) -> audit_sq_values_source_event N E V B
  | SqValuesOutput : nat -> audit_sq_values_source_event N E V B.

Arguments SqValuesCase {N E V B} _.

Arguments SqValuesPrepare {N E V B} _.

Arguments SqValuesDfs {N E V B} _.

Arguments SqValuesOut {N E V B} _ _ _.

Arguments SqValuesExit {N E V B} _ _ _.

Arguments SqValuesEdge {N E V B} _ _ _.

Arguments SqValuesHome {N E V B} _ _ _.

Arguments SqValuesUseMap {N E V B} _.

Arguments SqValuesDefMap {N E V B} _.

Arguments SqValuesSet {N E V B} _.

Arguments SqValuesElements {N E V B} _.

Arguments SqValuesOutput {N E V B} _.

(** Edge operands preserve every edge occurrence and source list concatenation. *)
Fixpoint audit_sq_values_source_edges {N E V B} (cb : audit_sq_values_callbacks N E V B)
    (edges : list E)
    : list V * list (audit_sq_values_source_event N E V B) :=
  match edges with
  | [] => ([], [SqValuesCase 0])
  | e :: rest => let '(uses, body) := sq_values_edge cb e in
    let '(later, events) := audit_sq_values_source_edges cb rest in
    (uses ++ later, SqValuesCase 1 :: SqValuesEdge e uses body :: events ++
      [SqValuesOutput (length uses)])
  end.

(** The point's exit and outgoing callbacks are each evaluated at this node. *)
Definition audit_sq_values_source_point {N E V B} (cb : audit_sq_values_callbacks N E V B) (n : N)
    : list V * list (audit_sq_values_source_event N E V B) :=
  let '(exits, exit_body) := sq_values_exit cb n in
  let '(edges, out_body) := sq_values_out cb n in
  let '(uses, events) := audit_sq_values_source_edges cb edges in
  (exits ++ uses, [SqValuesExit n exits exit_body; SqValuesOut n edges out_body] ++ events ++
    [SqValuesOutput (length exits)]).

(** Tail-first insertion preserves the source fold and every duplicate occurrence. *)
Fixpoint audit_sq_values_source_add {N E V B} (cb : audit_sq_values_callbacks N E V B) (n : N)
    (values : list V) (index : Map.t V (FinSet.t N)) :
    Map.t V (FinSet.t N) * list (audit_sq_values_source_event N E V B) :=
  match values with
  | [] => (index, [SqValuesCase 2])
  | v :: rest =>
    let '(middle, later) := audit_sq_values_source_add cb n rest index in
    let '(found, reads) := audit_map_get (sq_values_value_encode cb) v middle in
    let old := match found with
    Some s => s
    | None => FinSet.empty
    end in
    let '(row, set_calls) := audit_finset_add (sq_values_node_encode cb) n old in
    let '(result, writes) := audit_map_set (sq_values_value_encode cb) v row middle in
    (result, SqValuesCase 3 :: later ++ map SqValuesUseMap reads ++ map SqValuesSet set_calls ++
      map SqValuesUseMap writes)
  end.

(** The supplied node occurrences are folded tail-first, including duplicates. *)
Fixpoint audit_sq_values_source_uses {N E V B} (cb : audit_sq_values_callbacks N E V B)
    (nodes : list N)
    : Map.t V (FinSet.t N) * list (audit_sq_values_source_event N E V B) :=
  match nodes with
  | [] => (Map.empty, [SqValuesCase 4])
  | n :: rest =>
    let '(middle, later) := audit_sq_values_source_uses cb rest in
    let '(vars, point_calls) := audit_sq_values_source_point cb n in
    let '(result, calls) := audit_sq_values_source_add cb n vars middle in
    (result, SqValuesCase 5 :: later ++ point_calls ++ calls)
  end.

(** Definition callbacks are evaluated for every key in the actual use index. *)
Fixpoint audit_sq_values_source_defs {N E V B A} (cb : audit_sq_values_callbacks N E V B)
    (rows : list (V * A)) : Map.t V N * list (audit_sq_values_source_event N E V B) :=
  match rows with
  | [] => (Map.empty, [SqValuesCase 6])
  | (v, _) :: rest =>
    let '(middle, later) := audit_sq_values_source_defs cb rest in
    let '(home, body) := sq_values_home cb v in
    match home with
    | None => (middle, SqValuesCase 7 :: later ++ [SqValuesHome v home body])
    | Some n => let '(result, writes) := audit_map_set (sq_values_value_encode cb) v n middle in
      (result, SqValuesCase 8 :: later ++ SqValuesHome v home body :: map SqValuesDefMap writes)
    end
  end.

(** The complete preparation shares its graph index and DFS result across the use folds. *)
Definition audit_sq_values_source_counted {N E V B} (EN : encoding N) (g : Graph.t N E)
    (cb : audit_sq_values_callbacks N E V B) :
    ssa_query_values N V * list (audit_sq_values_source_event N E V B) :=
  let prepare_cb := AuditPrepareCallbackModel N E B (sq_values_out cb) (sq_values_target cb)
    (sq_values_node_encode cb) in
  let dfs_cb := AuditDfsCallbackModel N E B (sq_values_target cb) (sq_values_node_encode cb) in
  let '(p, prepare_events) := audit_prepare_source_counted EN g prepare_cb in
  let '(search, dfs_events) := audit_dfs_source_counted p dfs_cb FinSet.empty (Graph.entries g) in
  let '(uses, use_events) := audit_sq_values_source_uses cb (preorder search) in
  let '(rows, elements) := audit_map_elements uses in
  let '(defs, def_events) := audit_sq_values_source_defs cb rows in
  (SsaQueryValues defs uses, map SqValuesPrepare prepare_events ++ map SqValuesDfs dfs_events ++
    use_events ++ map SqValuesElements elements ++ def_events).

(** Callback erasure fixes every supplied value to the actual SSA point source. *)
Definition audit_sq_values_callbacks_erase {B0 BE N E V B} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B0 BE N E V) (cb : audit_sq_values_callbacks N E V B) : Prop :=
  let model := point_model s in let g := live_graph model in
  (forall n, fst (sq_values_node_encode cb n) = encode EN n) /\
  (forall v, fst (sq_values_value_encode cb v) = encode EV v) /\
  (forall n, fst (sq_values_out cb n) = Graph.out g n) /\
  (forall e, fst (sq_values_target cb e) = Graph.target g e) /\
  (forall n, fst (sq_values_exit cb n) = exit_use model n) /\
  (forall e, fst (sq_values_edge cb e) = edge_use model e) /\
  (forall v, fst (sq_values_home cb v) = point_definition s v).

(** Source work charges actual graph, collection and callback bodies. *)
Definition audit_sq_values_source_event_work {N E V B} (weight : B -> nat)
    (event : audit_sq_values_source_event N E V B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SqValuesCase _ => 0
  | SqValuesPrepare call => audit_prepare_source_event_work weight call
  | SqValuesDfs call => audit_dfs_source_event_work weight call
  | SqValuesOut _ _ xs | SqValuesExit _ _ xs | SqValuesEdge _ _ xs | SqValuesHome _ _ xs => body xs
  | SqValuesUseMap call => audit_map_source_work body [call]
  | SqValuesDefMap call => audit_map_source_work body [call]
  | SqValuesSet call => audit_finset_source_work body [call]
  | SqValuesElements call => audit_elements_frame_work call
  | SqValuesOutput n => S n
  end.

(** External cost uses only the actual client callbacks captured in the same run. *)
Definition audit_sq_values_source_event_external {N E V B} (weight : B -> nat)
    (event : audit_sq_values_source_event N E V B) : nat :=
  match event with
  | SqValuesPrepare call => audit_prepare_source_body_work weight [call]
  | SqValuesDfs call => audit_dfs_source_body_work weight [call]
  | SqValuesOut _ _ body | SqValuesExit _ _ body | SqValuesEdge _ _ body | SqValuesHome _ _ body |
    SqValuesUseMap (AuditMapGet _ _ _ _ body _) | SqValuesUseMap (AuditMapSet _ _ _ _ _ body _) |
    SqValuesUseMap (AuditMapRemove _ _ _ _ body _) | SqValuesDefMap (AuditMapGet _ _ _ _ body _) |
    SqValuesDefMap (AuditMapSet _ _ _ _ _ body _) | SqValuesDefMap (AuditMapRemove _ _ _ _ body _) |
    SqValuesSet (AuditSetMem _ _ _ _ body _) | SqValuesSet (AuditSetAdd _ _ _ _ body _) |
    SqValuesSet (AuditSetRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Source work includes trace and operand-list concatenation. *)
Definition audit_sq_values_source_work {N E V B} (weight : B -> nat)
    (events : list (audit_sq_values_source_event N E V B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event n => audit_sq_values_source_event_work weight event + n) 0 events.

(** The external measure sums bodies from that same execution. *)
Definition audit_sq_values_source_external {N E V B} (weight : B -> nat)
    (events : list (audit_sq_values_source_event N E V B)) : nat :=
  fold_right (fun event n => audit_sq_values_source_event_external weight event + n) 0 events.

(** Input support contains all nodes reachable through the prepared adjacency index. *)
Definition audit_sq_values_input_nodes {B0 BE N E V} (s : ssa_points B0 BE N E V) : list N :=
  let g := live_graph (point_model s) in
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  Graph.nodes g ++ Graph.entries g ++ map (Graph.target g) edges.

(** This input scale counts all source point occurrences and actual encoded widths. *)
Definition audit_sq_values_source_input_scale {B0 BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B0 BE N E V) : nat :=
  let model := point_model s in let g := live_graph model in
  let nodes := audit_sq_values_input_nodes s in
  let edges := flat_map (Graph.out g) nodes in
  let vars := flat_map (fun n => exit_use model n) nodes ++ flat_map (edge_use model) edges in
  let nw := fold_right Nat.max 0 (map (fun n => Pos.size_nat (encode EN n)) nodes) in
  let vw := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vars) in
  S (length nodes + length edges + length vars + nw + vw + audit_prepare_source_budget EN g +
    audit_dfs_source_budget EN g (prepare EN g) (Graph.entries g)).

(** The whole preparation bound uses only the original graph and point-use input. *)
Definition audit_sq_values_source_input_budget {B0 BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B0 BE N E V) : nat :=
  (N.to_nat 1048576%N) * Nat.pow (audit_sq_values_source_input_scale EN EV s) 48.

(** The value producer returns the source index and has a complete input-derived work bound. *)
Definition audit_sq_values_source_statement : Prop :=
  forall B0 BE N E V B (EN : encoding N) (EV : encoding V) (s : ssa_points B0 BE N E V)
    (cb : audit_sq_values_callbacks N E V B) (weight : B -> nat),
    audit_sq_values_callbacks_erase EN EV s cb ->
    let '(result, events) := audit_sq_values_source_counted EN (live_graph (point_model s)) cb in
    result = prepare_ssa_query_values EN EV s /\ audit_sq_values_source_work weight events <=
      audit_sq_values_source_input_budget EN EV s + audit_sq_values_source_external weight events.

(** Captured DFS calls price the genuine target or node encoder input. *)
Definition audit_sq_values_capture_budget {N E B} (node_budget : N -> nat)
    (target_budget : E -> nat)
    (call : audit_graph_callback_capture N E B) : nat :=
  match call with
  | AuditGraphEncodeCapture _ _ _ n _ _ => node_budget n
  | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e
  end.

(** Each source event uses the budget for its actual supplied callback input. *)
Definition audit_sq_values_source_event_budget {N E V B}
    (node_budget out_budget exit_budget : N -> nat)
    (value_budget home_budget : V -> nat) (target_budget edge_budget : E -> nat)
    (event : audit_sq_values_source_event N E V B) : nat :=
  match event with
  | SqValuesPrepare call => audit_prepare_source_event_budget node_budget out_budget target_budget
    call
  | SqValuesDfs (_, calls) => fold_right (fun call total =>
    audit_sq_values_capture_budget node_budget target_budget call + total) 0 calls
  | SqValuesOut n _ _ => out_budget n
  | SqValuesExit n _ _ => exit_budget n
  | SqValuesEdge e _ _ => edge_budget e
  | SqValuesHome v _ _ => home_budget v
  | SqValuesUseMap (AuditMapGet v _ _ _ _ _) | SqValuesUseMap (AuditMapSet v _ _ _ _ _ _) |
    SqValuesUseMap (AuditMapRemove v _ _ _ _ _) | SqValuesDefMap (AuditMapGet v _ _ _ _ _) |
    SqValuesDefMap (AuditMapSet v _ _ _ _ _ _) | SqValuesDefMap (AuditMapRemove v _ _ _ _ _) =>
    value_budget v
  | SqValuesSet (AuditSetMem n _ _ _ _ _) | SqValuesSet (AuditSetAdd n _ _ _ _ _) |
    SqValuesSet (AuditSetRemove n _ _ _ _ _) => node_budget n
  | _ => 0
  end.

(** Under callback laws, value preparation returns the source index within the per-call bound. *)
Definition audit_sq_values_source_adapted_statement : Prop :=
  forall B0 BE N E V B (EN : encoding N) (EV : encoding V) (s : ssa_points B0 BE N E V)
    (cb : audit_sq_values_callbacks N E V B) (weight : B -> nat)
    node_source value_source out_source target_source exit_source edge_source home_source
    node_budget value_budget out_budget target_budget exit_budget edge_budget home_budget,
    audit_sq_values_callbacks_erase EN EV s cb ->
    audit_graph_external_callback_adapter (sq_values_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (sq_values_value_encode cb) weight value_source
      value_budget ->
    audit_graph_external_callback_adapter (sq_values_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (sq_values_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter (sq_values_exit cb) weight exit_source exit_budget ->
    audit_graph_external_callback_adapter (sq_values_edge cb) weight edge_source edge_budget ->
    audit_graph_external_callback_adapter (sq_values_home cb) weight home_source home_budget ->
    let '(result, events) := audit_sq_values_source_counted EN (live_graph (point_model s)) cb in
    result = prepare_ssa_query_values EN EV s /\ audit_sq_values_source_work weight events <=
      audit_sq_values_source_input_budget EN EV s +
      fold_right (fun event total => audit_sq_values_source_event_budget node_budget out_budget
        exit_budget value_budget home_budget target_budget edge_budget event + total) 0 events.

(** The complete value-preparation contract includes same-run and primitive source obligations. *)
Definition audit_sq_values_source_contract_statement : Prop :=
  audit_sq_values_source_statement /\ audit_sq_values_source_adapted_statement /\
  audit_map_get_source_work_bound_statement /\ audit_map_set_source_work_bound_statement /\
  audit_finset_add_erases_statement /\ audit_map_elements_erases_statement /\
  audit_map_elements_work_bound_statement.

(** Events retain each actual client callback and collection source call. *)
Inductive audit_sq_reduced_source_event (N E B : Type) : Type :=
  | SqReducedCase : nat -> audit_sq_reduced_source_event N E B
  | SqReducedTarget : E -> N -> list B -> audit_sq_reduced_source_event N E B
  | SqReducedSource : E -> N -> list B -> audit_sq_reduced_source_event N E B
  | SqReducedDom : audit_frontier_source_event N E B -> audit_sq_reduced_source_event N E B
  | SqReducedEdges : audit_map_event N (list E) B -> audit_sq_reduced_source_event N E B
  | SqReducedRows : audit_map_event N (FinSet.t N) B -> audit_sq_reduced_source_event N E B
  | SqReducedSet : audit_set_event N B -> audit_sq_reduced_source_event N E B
  | SqReducedUnion : audit_union_event N -> audit_sq_reduced_source_event N E B.

Arguments SqReducedCase {N E B} _.

Arguments SqReducedTarget {N E B} _ _ _.

Arguments SqReducedSource {N E B} _ _ _.

Arguments SqReducedDom {N E B} _.

Arguments SqReducedEdges {N E B} _.

Arguments SqReducedRows {N E B} _.

Arguments SqReducedSet {N E B} _.

Arguments SqReducedUnion {N E B} _.

(** Back-edge testing uses the actual target, source and selective DFS-interval lookups. *)
Definition audit_sq_reduced_source_back {N E B} (enc : N -> positive * list B)
    (target source : E -> N * list B) (r : dfs_result N E) (e : E)
    : bool * list (audit_sq_reduced_source_event N E B) :=
  let '(dst, db) := target e in let '(src, sb) := source e in
  let tree := DomTree (@Map.empty N N) (pre_num r) (post_num r) in
  let '(result, calls) := audit_frontier_source_dom enc tree dst src in
  (result, [SqReducedTarget e dst db; SqReducedSource e src sb] ++ map SqReducedDom calls).

(** Every edge occurrence follows the actual tail-first reduced-row fold. *)
Fixpoint audit_sq_reduced_source_edges {N E B} (enc : N -> positive * list B)
    (target source : E -> N * list B) (r : dfs_result N E) (index : Map.t N (FinSet.t N))
    (edges : list E) (initial : FinSet.t N) :
    FinSet.t N * list (audit_sq_reduced_source_event N E B) :=
  match edges with
  | [] => (initial, [SqReducedCase 0])
  | edge :: rest =>
    let '(middle, later) := audit_sq_reduced_source_edges enc target source r index rest initial
      in
    let '(back, back_calls) := audit_sq_reduced_source_back enc target source r edge in
    if back then (middle, SqReducedCase 1 :: later ++ back_calls) else
      let '(dst, body) := target edge in
      let '(found, reads) := audit_map_get enc dst index in
      let row := match found with
      Some s => s
      | None => FinSet.empty
      end in
      let '(result, calls) := audit_finset_union row middle in
      (result, SqReducedCase 2 :: later ++ back_calls ++ [SqReducedTarget edge dst body] ++
        map SqReducedRows reads ++ map SqReducedUnion calls)
  end.

(** Each row uses the actual prepared adjacency and accumulated reduced index. *)
Fixpoint audit_sq_reduced_source_rows {N E B} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (enc : N -> positive * list B) (target source : E -> N * list B)
    (r : dfs_result N E) (order : list N) :
    Map.t N (FinSet.t N) * list (audit_sq_reduced_source_event N E B) :=
  match order with
  | [] => (Map.empty, [SqReducedCase 3])
  | n :: rest =>
    let '(middle, later) := audit_sq_reduced_source_rows p enc target source r rest in
    let '(initial, add_calls) := audit_finset_add enc n FinSet.empty in
    let '(found, reads) := audit_map_get enc n (out_index p) in
    let edges := match found with
    Some es => es
    | None => []
    end in
    let '(row, calls) := audit_sq_reduced_source_edges enc target source r middle edges initial in
    let '(result, writes) := audit_map_set enc n row middle in
    (result, SqReducedCase 4 :: later ++ map SqReducedSet add_calls ++ map SqReducedEdges reads ++
      calls ++ map SqReducedRows writes)
  end.

(** Source work includes nested map, comparison, set and complete union bodies. *)
Definition audit_sq_reduced_source_event_work {N E B} (weight : B -> nat)
    (event : audit_sq_reduced_source_event N E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SqReducedTarget _ _ xs | SqReducedSource _ _ xs => body xs
  | SqReducedDom call => audit_frontier_source_event_work weight call
  | SqReducedEdges call => audit_map_source_work body [call]
  | SqReducedRows call => audit_map_source_work body [call]
  | SqReducedSet call => audit_finset_source_work body [call]
  | SqReducedUnion call => audit_finset_union_source_work [call]
  | SqReducedCase _ => 0
  end.

(** External work includes only actual encoder, target and source callback bodies. *)
Definition audit_sq_reduced_source_event_external {N E B} (weight : B -> nat)
    (event : audit_sq_reduced_source_event N E B) : nat :=
  match event with
  | SqReducedTarget _ _ body | SqReducedSource _ _ body |
    SqReducedEdges (AuditMapGet _ _ _ _ body _) | SqReducedEdges (AuditMapSet _ _ _ _ _ body _) |
    SqReducedEdges (AuditMapRemove _ _ _ _ body _) | SqReducedRows (AuditMapGet _ _ _ _ body _) |
    SqReducedRows (AuditMapSet _ _ _ _ _ body _) | SqReducedRows (AuditMapRemove _ _ _ _ body _) |
    SqReducedSet (AuditSetMem _ _ _ _ body _) | SqReducedSet (AuditSetAdd _ _ _ _ body _) |
    SqReducedSet (AuditSetRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | SqReducedDom call => audit_frontier_source_body_event_work weight call
  | _ => 0
  end.

(** Whole reduced-index work charges trace and output concatenation. *)
Definition audit_sq_reduced_source_work {N E B} (weight : B -> nat)
    (events : list (audit_sq_reduced_source_event N E B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event n => audit_sq_reduced_source_event_work weight event + n) 0 events.

(** External work sums the captured callback bodies from this same run. *)
Definition audit_sq_reduced_source_external {N E B} (weight : B -> nat)
    (events : list (audit_sq_reduced_source_event N E B)) : nat :=
  fold_right (fun event n => audit_sq_reduced_source_event_external weight event + n) 0 events.

(** The input budget uses actual order, prepared edges, ranks and encoded widths. *)
Definition audit_sq_reduced_source_budget {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (r : dfs_result N E) (order : list N) : nat :=
  let edges := flat_map (succ_edges p) order in
  let pre := Map.elements (pre_num r) in let post := Map.elements (post_num r) in
  let nodes := order ++ map (Graph.target g) edges ++ map (Graph.source g) edges ++ map fst pre ++
    map fst post in
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EN v)) nodes) in
  let rank_width := fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (pre ++ post)) in
  4096 * Nat.pow (S (length nodes + length edges + width + rank_width)) 8.

(** The reduced-index source result and full input-work bound match the source phase. *)
Definition audit_sq_reduced_source_statement : Prop :=
  forall N E B (EN : encoding N) (g : Graph.t N E) (p : prepared EN g) (r : dfs_result N E) order
    (enc : N -> positive * list B) (target source : E -> N * list B) (weight : B -> nat),
    (forall n, fst (enc n) = encode EN n) -> (forall e, fst (target e) = Graph.target g e) ->
    (forall e, fst (source e) = Graph.source g e) ->
    let '(result, events) := audit_sq_reduced_source_rows p enc target source r order in
    result = AnalysesSsaLiveQuery.live_r_build EN (Graph.target g) (succ_edges p)
      (fun e => ancestor_b EN r (Graph.target g e) (Graph.source g e)) order /\
      audit_sq_reduced_source_work weight events <= audit_sq_reduced_source_budget EN g p r order +
        audit_sq_reduced_source_external weight events.

(** The reduced-index event prices each actual client callback input. *)
Definition audit_sq_reduced_source_event_budget {N E B} (encode_budget : N -> nat)
    (target_budget source_budget : E -> nat) (event : audit_sq_reduced_source_event N E B) : nat :=
  match event with
  | SqReducedTarget e _ _ => target_budget e
  | SqReducedSource e _ _ => source_budget e
  | SqReducedEdges (AuditMapGet n _ _ _ _ _) | SqReducedEdges (AuditMapSet n _ _ _ _ _ _) |
    SqReducedEdges (AuditMapRemove n _ _ _ _ _) | SqReducedRows (AuditMapGet n _ _ _ _ _) |
    SqReducedRows (AuditMapSet n _ _ _ _ _ _) | SqReducedRows (AuditMapRemove n _ _ _ _ _) |
    SqReducedSet (AuditSetMem n _ _ _ _ _) | SqReducedSet (AuditSetAdd n _ _ _ _ _) |
    SqReducedSet (AuditSetRemove n _ _ _ _ _) => encode_budget n
  | SqReducedDom (FrontierSourceRank (AuditMapGet n _ _ _ _ _)) |
    SqReducedDom (FrontierSourceRank (AuditMapSet n _ _ _ _ _ _)) |
    SqReducedDom (FrontierSourceRank (AuditMapRemove n _ _ _ _ _)) => encode_budget n
  | _ => 0
  end.

(** With callback laws, reduced rows match the source and obey the per-call work bound. *)
Definition audit_sq_reduced_source_adapted_statement : Prop :=
  forall N E B (EN : encoding N) (g : Graph.t N E) (p : prepared EN g) (r : dfs_result N E) order
    (enc : N -> positive * list B) (target source : E -> N * list B) (weight : B -> nat)
    encode_source target_source source_source encode_budget target_budget source_budget,
    (forall n, fst (enc n) = encode EN n) -> (forall e, fst (target e) = Graph.target g e) ->
    (forall e, fst (source e) = Graph.source g e) ->
    audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
    audit_graph_external_callback_adapter target weight target_source target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    let '(result, events) := audit_sq_reduced_source_rows p enc target source r order in
    result = AnalysesSsaLiveQuery.live_r_build EN (Graph.target g) (succ_edges p)
      (fun e => ancestor_b EN r (Graph.target g e) (Graph.source g e)) order /\
      audit_sq_reduced_source_work weight events <= audit_sq_reduced_source_budget EN g p r order +
        fold_right (fun event n => audit_sq_reduced_source_event_budget encode_budget target_budget
          source_budget event + n) 0 events.

(** The reduced-index contract includes actual union and binary comparison obligations. *)
Definition audit_sq_reduced_source_contract_statement : Prop :=
  audit_sq_reduced_source_statement /\ audit_sq_reduced_source_adapted_statement /\
  audit_map_get_source_work_bound_statement /\ audit_map_set_source_work_bound_statement /\
  audit_finset_add_erases_statement /\ audit_finset_union_erases_statement /\
  audit_finset_union_source_bound_statement /\ audit_positive_compare_cont_statement /\
  audit_positive_order_statement.

(** Events retain actual nested source bodies and supplied callback inputs. *)
Inductive audit_sq_t_source_event (N E B : Type) : Type :=
  | SqTCase : nat -> audit_sq_t_source_event N E B
  | SqTReduced : audit_sq_reduced_source_event N E B -> audit_sq_t_source_event N E B
  | SqTSetMap : audit_map_event N (FinSet.t N) B -> audit_sq_t_source_event N E B
  | SqTOutMap : audit_map_event N (list E) B -> audit_sq_t_source_event N E B
  | SqTRowMap : audit_map_event N (list (N * N)) B -> audit_sq_t_source_event N E B
  | SqTElements : audit_set_elements_event N -> audit_sq_t_source_event N E B
  | SqTTarget : E -> N -> list B -> audit_sq_t_source_event N E B
  | SqTSet : audit_set_event N B -> audit_sq_t_source_event N E B
  | SqTOutput : nat -> audit_sq_t_source_event N E B.

Arguments SqTCase {N E B} _.

Arguments SqTReduced {N E B} _.

Arguments SqTSetMap {N E B} _.

Arguments SqTOutMap {N E B} _.

Arguments SqTRowMap {N E B} _.

Arguments SqTElements {N E B} _.

Arguments SqTTarget {N E B} _ _ _.

Arguments SqTSet {N E B} _.

Arguments SqTOutput {N E B} _.

(** Every edge evaluates both the back-edge test and target membership. *)
Fixpoint audit_sq_t_source_filter {N E B} (enc : N -> positive * list B)
    (target source : E -> N * list B) (r : dfs_result N E) (reduced : FinSet.t N) (edges : list E)
    : list E * list (audit_sq_t_source_event N E B) :=
  match edges with
  | [] => ([], [SqTCase 0])
  | e :: rest =>
    let '(back, calls) := audit_sq_reduced_source_back enc target source r e in
    let '(dst, body) := target e in let '(member, reads) := audit_finset_mem enc dst reduced in
    let '(later, events) := audit_sq_t_source_filter enc target source r reduced rest in
    (if back && negb member then e :: later else later,
      SqTCase 1 :: map SqTReduced calls ++ [SqTTarget e dst body] ++ map SqTSet reads ++ events)
  end.

(** The subsequent map invokes the target callback for each retained edge. *)
Fixpoint audit_sq_t_source_targets {N E B} (target : E -> N * list B) (edges : list E)
    : list N * list (audit_sq_t_source_event N E B) :=
  match edges with
  | [] => ([], [SqTCase 2])
  | e :: rest => let '(dst, body) := target e in
    let '(later, events) := audit_sq_t_source_targets target rest in
    (dst :: later, SqTCase 3 :: SqTTarget e dst body :: events)
  end.

(** Each reduced vertex reads its prepared adjacency and preserves edge order. *)
Fixpoint audit_sq_t_source_vertices {N E B} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (enc : N -> positive * list B) (target source : E -> N * list B)
    (r : dfs_result N E) (reduced : FinSet.t N) (vertices : list N)
    : list N * list (audit_sq_t_source_event N E B) :=
  match vertices with
  | [] => ([], [SqTCase 4])
  | v :: rest =>
    let '(found, reads) := audit_map_get enc v (out_index p) in
    let edges := match found with
    Some xs => xs
    | None => []
    end in
    let '(selected, calls) := audit_sq_t_source_filter enc target source r reduced edges in
    let '(targets, target_calls) := audit_sq_t_source_targets target selected in
    let '(later, events) := audit_sq_t_source_vertices p enc target source r reduced rest in
    (targets ++ later, SqTCase 5 :: map SqTOutMap reads ++ calls ++ target_calls ++ events ++
      [SqTOutput (length targets)])
  end.

(** A row enumerates its reduced set and constructs the exact target set. *)
Definition audit_sq_t_source_edges {N E B} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (enc : N -> positive * list B) (target source : E -> N * list B)
    (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (n : N)
    : FinSet.t N * list (audit_sq_t_source_event N E B) :=
  let '(found, reads) := audit_map_get enc n rm in
  let reduced := match found with
  Some s => s
  | None => FinSet.empty
  end in
  let '(vertices, enumeration) := audit_finset_elements reduced in
  let '(targets, calls) := audit_sq_t_source_vertices p enc target source r reduced vertices in
  let '(result, inserts) := audit_finset_of_list enc targets in
  (result, map SqTSetMap reads ++ map SqTElements enumeration ++ calls ++ map SqTSet inserts).

(** Tail-first tabulation records each actual row and output list. *)
Fixpoint audit_sq_t_source_rows {N E B} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (enc : N -> positive * list B) (target source : E -> N * list B)
    (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (nodes : list N)
    : Map.t N (list (N * N)) * list (audit_sq_t_source_event N E B) :=
  match nodes with
  | [] => (Map.empty, [SqTCase 6])
  | n :: rest =>
    let '(middle, later) := audit_sq_t_source_rows p enc target source r rm rest in
    let '(edges, calls) := audit_sq_t_source_edges p enc target source r rm n in
    let '(vertices, enumeration) := audit_finset_elements edges in
    let row := map (fun v => (n, v)) vertices in
    let '(result, writes) := audit_map_set enc n row middle in
    (result, SqTCase 7 :: later ++ calls ++ map SqTElements enumeration ++
      [SqTOutput (length vertices)] ++
      map SqTRowMap writes)
  end.

(** The returned graph closes over the exact rows produced by this same run. *)
Definition audit_sq_t_source_counted {N E B} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (enc : N -> positive * list B) (target source : E -> N * list B)
    (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (nodes : list N)
    : Graph.t N (N * N) * (Map.t N (list (N * N)) * list (audit_sq_t_source_event N E B)) :=
  let '(rows, events) := audit_sq_t_source_rows p enc target source r rm nodes in
  (Graph.Make [] nodes (fun n => match Map.get EN n rows with
    Some es => es
    | None => []
    end) fst snd,
    (rows, events)).

(** Source work includes actual nested, map, set and enumeration source calls. *)
Definition audit_sq_t_source_event_work {N E B} (weight : B -> nat)
    (event : audit_sq_t_source_event N E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SqTCase _ => 0
  | SqTReduced call => audit_sq_reduced_source_event_work weight call
  | SqTSetMap call => audit_map_source_work body [call]
  | SqTOutMap call => audit_map_source_work body [call]
  | SqTRowMap call => audit_map_source_work body [call]
  | SqTElements call => audit_set_elements_work [call]
  | SqTTarget _ _ xs => body xs
  | SqTSet call => audit_finset_source_work body [call]
  | SqTOutput n => S n
  end.

(** External work sums only bodies of actual supplied callbacks. *)
Definition audit_sq_t_source_event_external {N E B} (weight : B -> nat)
    (event : audit_sq_t_source_event N E B) : nat :=
  match event with
  | SqTReduced call => audit_sq_reduced_source_event_external weight call
  | SqTTarget _ _ body | SqTSetMap (AuditMapGet _ _ _ _ body _) |
    SqTSetMap (AuditMapSet _ _ _ _ _ body _) |
    SqTSetMap (AuditMapRemove _ _ _ _ body _) | SqTOutMap (AuditMapGet _ _ _ _ body _) |
    SqTOutMap (AuditMapSet _ _ _ _ _ body _) | SqTOutMap (AuditMapRemove _ _ _ _ body _) |
    SqTRowMap (AuditMapGet _ _ _ _ body _) | SqTRowMap (AuditMapSet _ _ _ _ _ body _) |
    SqTRowMap (AuditMapRemove _ _ _ _ body _) | SqTSet (AuditSetMem _ _ _ _ body _) |
    SqTSet (AuditSetAdd _ _ _ _ body _) | SqTSet (AuditSetRemove _ _ _ _ body _) =>
    fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Whole work includes source frames and trace and row-list composition. *)
Definition audit_sq_t_source_work {N E B} (weight : B -> nat)
    (events : list (audit_sq_t_source_event N E B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event n => audit_sq_t_source_event_work weight event + n) 0 events.

(** Callback costs are taken from the same actual T-graph run. *)
Definition audit_sq_t_source_external {N E B} (weight : B -> nat)
    (events : list (audit_sq_t_source_event N E B)) : nat :=
  fold_right (fun event n => audit_sq_t_source_event_external weight event + n) 0 events.

(** The input scale includes all reduced sets, adjacency occurrences, rank and key widths. *)
Definition audit_sq_t_source_input_scale {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (nodes : list N) : nat :=
  let rows := Map.elements rm in
  let vertices := nodes ++ map fst rows ++ flat_map (fun row => FinSet.elements (snd row)) rows in
  let edges := flat_map (succ_edges p) vertices in
  let pre := Map.elements (pre_num r) in let post := Map.elements (post_num r) in
  let keys := vertices ++ map (Graph.target g) edges ++ map (Graph.source g) edges ++ map fst pre ++
    map fst post in
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EN v)) keys) in
  let rank_width := fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (pre ++ post)) in
  let set_size := fold_right (fun row n =>
    audit_trie_nodes (snd row) + audit_trie_output_bits (snd row) + n) 0 rows in
  S (length keys + length edges + length rows + width + rank_width + set_size + audit_trie_nodes
    rm).

(** The T-graph source bound depends only on its original inputs. *)
Definition audit_sq_t_source_budget {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (nodes : list N) : nat :=
  (N.to_nat 1048576%N) * Nat.pow (audit_sq_t_source_input_scale EN g p r rm nodes) 12.

(** The T graph agrees with the source graph and has bounded source work. *)
Definition audit_sq_t_source_statement : Prop :=
  forall N E B (EN : encoding N) (g : Graph.t N E) (p : prepared EN g) (r : dfs_result N E)
    rm nodes (enc : N -> positive * list B) (target source : E -> N * list B) (weight : B -> nat),
    (forall n, fst (enc n) = encode EN n) -> (forall e, fst (target e) = Graph.target g e) ->
    (forall e, fst (source e) = Graph.source g e) ->
    let '(graph, (_, events)) := audit_sq_t_source_counted p enc target source r rm nodes in
    graph = AnalysesSsaLiveQuery.live_t_graph EN g (succ_edges p)
      (fun e => ancestor_b EN r (Graph.target g e) (Graph.source g e)) rm nodes /\
      audit_sq_t_source_work weight events <= audit_sq_t_source_budget EN g p r rm nodes +
        audit_sq_t_source_external weight events.

(** Each event applies the appropriate budget to its actual callback input. *)
Definition audit_sq_t_source_event_budget {N E B} (encode_budget : N -> nat)
    (target_budget source_budget : E -> nat) (event : audit_sq_t_source_event N E B) : nat :=
  match event with
  | SqTReduced call => audit_sq_reduced_source_event_budget encode_budget target_budget
    source_budget call
  | SqTTarget e _ _ => target_budget e
  | SqTSetMap (AuditMapGet n _ _ _ _ _) | SqTSetMap (AuditMapSet n _ _ _ _ _ _) |
    SqTSetMap (AuditMapRemove n _ _ _ _ _) | SqTOutMap (AuditMapGet n _ _ _ _ _) |
    SqTOutMap (AuditMapSet n _ _ _ _ _ _) | SqTOutMap (AuditMapRemove n _ _ _ _ _) |
    SqTRowMap (AuditMapGet n _ _ _ _ _) | SqTRowMap (AuditMapSet n _ _ _ _ _ _) |
    SqTRowMap (AuditMapRemove n _ _ _ _ _) | SqTSet (AuditSetMem n _ _ _ _ _) |
    SqTSet (AuditSetAdd n _ _ _ _ _) | SqTSet (AuditSetRemove n _ _ _ _ _) => encode_budget n
  | _ => 0
  end.

(** With callback laws, the T graph matches the source and obeys the per-call work bound. *)
Definition audit_sq_t_source_adapted_statement : Prop :=
  forall N E B (EN : encoding N) (g : Graph.t N E) (p : prepared EN g) (r : dfs_result N E)
    rm nodes (enc : N -> positive * list B) (target source : E -> N * list B) (weight : B -> nat)
    encode_source target_source source_source encode_budget target_budget source_budget,
    (forall n, fst (enc n) = encode EN n) -> (forall e, fst (target e) = Graph.target g e) ->
    (forall e, fst (source e) = Graph.source g e) ->
    audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
    audit_graph_external_callback_adapter target weight target_source target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    let '(graph, (_, events)) := audit_sq_t_source_counted p enc target source r rm nodes in
    graph = AnalysesSsaLiveQuery.live_t_graph EN g (succ_edges p)
      (fun e => ancestor_b EN r (Graph.target g e) (Graph.source g e)) rm nodes /\
      audit_sq_t_source_work weight events <= audit_sq_t_source_budget EN g p r rm nodes +
        fold_right (fun event n => audit_sq_t_source_event_budget encode_budget target_budget
          source_budget event + n) 0 events.

(** The T-graph contract includes source enumeration and reduced-index obligations. *)
Definition audit_sq_t_source_contract_statement : Prop :=
  audit_sq_t_source_statement /\ audit_sq_t_source_adapted_statement /\
  audit_sq_reduced_source_contract_statement /\ audit_finset_elements_erases_statement /\
  audit_finset_elements_work_bound_statement /\ audit_finset_of_list_erases_statement.

(** Internal T callbacks retain actual map and supplied encoder bodies. *)
Inductive audit_sq_t_internal (N B : Type) : Type :=
  | SqTInternalMap : audit_map_event N (list (N * N)) B -> audit_sq_t_internal N B
  | SqTInternalTarget : N * N -> audit_sq_t_internal N B
  | SqTInternalEncode : N -> positive -> list B -> audit_sq_t_internal N B.

Arguments SqTInternalMap {N B} _.

Arguments SqTInternalTarget {N B} _.

Arguments SqTInternalEncode {N B} _ _ _.

(** The generated outgoing callback reads exactly its captured row map. *)
Definition audit_sq_t_internal_out {N B} (enc : N -> positive * list B)
    (rows : Map.t N (list (N * N))) (n : N)
    : list (N * N) * list (audit_sq_t_internal N B) :=
  let '(found, reads) := audit_map_get enc n rows in
  (match found with
  Some edges => edges
  | None => []
  end, map SqTInternalMap reads).

(** The generated target callback is the second pair projection. *)
Definition audit_sq_t_internal_target {N B} (edge : N * N) : N * list (audit_sq_t_internal N B) :=
  (snd edge, [SqTInternalTarget edge]).

(** The generated encoder calls the supplied node encoder at the actual vertex. *)
Definition audit_sq_t_internal_encode {N B} (enc : N -> positive * list B) (n : N)
    : positive * list (audit_sq_t_internal N B) :=
  let '(code, body) := enc n in (code, [SqTInternalEncode n code body]).

(** These callbacks are the actual T graph's preparation callbacks. *)
Definition audit_sq_t_internal_prepare_callbacks {N B} (enc : N -> positive * list B)
    (rows : Map.t N (list (N * N))) :
    audit_prepare_callback_model N (N * N) (audit_sq_t_internal N B) :=
  AuditPrepareCallbackModel _ _ _ (audit_sq_t_internal_out enc rows) audit_sq_t_internal_target
    (audit_sq_t_internal_encode enc).

(** These callbacks are the actual T graph's DFS callbacks. *)
Definition audit_sq_t_internal_dfs_callbacks {N B} (enc : N -> positive * list B)
    : audit_dfs_callback_model N (N * N) (audit_sq_t_internal N B) :=
  AuditDfsCallbackModel _ _ _ audit_sq_t_internal_target (audit_sq_t_internal_encode enc).

(** Closure events retain actual DFS, set construction and row update bodies. *)
Inductive audit_sq_closure_source_event (N B : Type) : Type :=
  | SqClosureCase : nat -> audit_sq_closure_source_event N B
  | SqClosureDfs : audit_dfs_nested_event N (N * N)
      (audit_graph_callback_capture N (N * N) (audit_sq_t_internal N B)) ->
    audit_sq_closure_source_event N B
  | SqClosureSet : audit_set_event N B -> audit_sq_closure_source_event N B
  | SqClosureRow : audit_map_event N (FinSet.t N) B -> audit_sq_closure_source_event N B.

Arguments SqClosureCase {N B} _.

Arguments SqClosureDfs {N B} _.

Arguments SqClosureSet {N B} _.

Arguments SqClosureRow {N B} _.

(** The tail-first closure tabulation performs one DFS per actual node. *)
Fixpoint audit_sq_closure_source_rows {N B} {EN : encoding N} {tg : Graph.t N (N * N)}
    (tp : prepared EN tg) (enc : N -> positive * list B) (nodes : list N)
    : Map.t N (FinSet.t N) * list (audit_sq_closure_source_event N B) :=
  match nodes with
  | [] => (Map.empty, [SqClosureCase 0])
  | n :: rest =>
    let '(middle, later) := audit_sq_closure_source_rows tp enc rest in
    let '(search, dfs_calls) := audit_dfs_source_counted tp
      (audit_sq_t_internal_dfs_callbacks enc) FinSet.empty [n] in
    let '(row, set_calls) := audit_finset_of_list enc (preorder search) in
    let '(result, writes) := audit_map_set enc n row middle in
    (result, SqClosureCase 1 :: later ++ map SqClosureDfs dfs_calls ++ map SqClosureSet
      set_calls ++
      map SqClosureRow writes)
  end.

(** Internal callback work expands map source operations and the captured encoder body. *)
Definition audit_sq_t_internal_work {N B} (weight : B -> nat) (event : audit_sq_t_internal N B) :
    nat :=
  64 + match event with
  | SqTInternalMap call =>
    audit_map_source_work (fun xs => fold_right (fun x n => weight x + n) 0 xs) [call]
  | SqTInternalEncode _ _ body => fold_right (fun x n => weight x + n) 0 body
  | SqTInternalTarget _ => 0
  end.

(** Only the underlying node encoder has an external body. *)
Definition audit_sq_t_internal_external {N B} (weight : B -> nat) (event : audit_sq_t_internal N B)
    : nat :=
  match event with
  | SqTInternalMap (AuditMapGet _ _ _ _ body _) | SqTInternalMap (AuditMapSet _ _ _ _ _ body _) |
    SqTInternalMap (AuditMapRemove _ _ _ _ body _) | SqTInternalEncode _ _ body =>
    fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Work expands each actual nested DFS and collection source operation. *)
Definition audit_sq_closure_source_event_work {N B} (weight : B -> nat)
    (event : audit_sq_closure_source_event N B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SqClosureCase _ => 0
  | SqClosureDfs call => audit_dfs_source_event_work (audit_sq_t_internal_work weight) call
  | SqClosureSet call => audit_finset_source_work body [call]
  | SqClosureRow call => audit_map_source_work body [call]
  end.

(** The external observation sums only recorded original encoder bodies. *)
Definition audit_sq_closure_source_event_external {N B} (weight : B -> nat)
    (event : audit_sq_closure_source_event N B) : nat :=
  match event with
  | SqClosureDfs call => audit_dfs_source_body_work (audit_sq_t_internal_external weight) [call]
  | SqClosureSet (AuditSetMem _ _ _ _ body _) | SqClosureSet (AuditSetAdd _ _ _ _ body _) |
    SqClosureSet (AuditSetRemove _ _ _ _ body _) | SqClosureRow (AuditMapGet _ _ _ _ body _) |
    SqClosureRow (AuditMapSet _ _ _ _ _ body _) | SqClosureRow (AuditMapRemove _ _ _ _ body _) =>
    fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Whole closure work charges the event stream and trace concatenations. *)
Definition audit_sq_closure_source_work {N B} (weight : B -> nat)
    (events : list (audit_sq_closure_source_event N B)) : nat :=
  256 * Nat.pow (S (length events)) 3 + fold_right (fun event n =>
    audit_sq_closure_source_event_work weight event + n) 0 events.

(** External bodies are counted on the same actual execution. *)
Definition audit_sq_closure_source_external {N B} (weight : B -> nat)
    (events : list (audit_sq_closure_source_event N B)) : nat :=
  fold_right (fun event n => audit_sq_closure_source_event_external weight event + n) 0 events.

(** The input bound uses the prepared T index and all requested closure roots. *)
Definition audit_sq_closure_source_budget {N} (EN : encoding N) (tg : Graph.t N (N * N))
    (tp : prepared EN tg) (nodes : list N) : nat :=
  let scale := S (length nodes + Pos.to_nat (fuel tp) + audit_dfs_full_input_width EN tg tp nodes +
    audit_dfs_source_budget EN tg tp nodes) in
  (N.to_nat 1048576%N) * Nat.pow scale 16.

(** The source closure rows match the actual tabulation and have bounded work. *)
Definition audit_sq_closure_source_statement : Prop :=
  forall N B (EN : encoding N) (tg : Graph.t N (N * N)) (tp : prepared EN tg) nodes
    (enc : N -> positive * list B) (weight : B -> nat),
    (forall n, fst (enc n) = encode EN n) -> (forall edge, Graph.target tg edge = snd edge) ->
    let '(result, events) := audit_sq_closure_source_rows tp enc nodes in
    result = AnalysesSsaLiveQuery.live_tabulate EN
      (fun n => FinSet.of_list EN (preorder (dfs tp FinSet.empty [n]))) nodes /\
      audit_sq_closure_source_work weight events <= audit_sq_closure_source_budget EN tg tp nodes +
        audit_sq_closure_source_external weight events.

(** A generated T callback prices the actual original encoder input. *)
Definition audit_sq_t_internal_budget {N B} (encode_budget : N -> nat)
    (event : audit_sq_t_internal N B) : nat :=
  match event with
  | SqTInternalMap (AuditMapGet n _ _ _ _ _) | SqTInternalMap (AuditMapSet n _ _ _ _ _ _) |
    SqTInternalMap (AuditMapRemove n _ _ _ _ _) | SqTInternalEncode n _ _ => encode_budget n
  | SqTInternalTarget _ => 0
  end.

(** Closure events price each actual external node-encoder invocation. *)
Definition audit_sq_closure_source_event_budget {N B} (encode_budget : N -> nat)
    (event : audit_sq_closure_source_event N B) : nat :=
  match event with
  | SqClosureDfs call => audit_dfs_source_body_work (audit_sq_t_internal_budget encode_budget)
    [call]
  | SqClosureSet (AuditSetMem n _ _ _ _ _) | SqClosureSet (AuditSetAdd n _ _ _ _ _) |
    SqClosureSet (AuditSetRemove n _ _ _ _ _) | SqClosureRow (AuditMapGet n _ _ _ _ _) |
    SqClosureRow (AuditMapSet n _ _ _ _ _ _) | SqClosureRow (AuditMapRemove n _ _ _ _ _) =>
    encode_budget n
  | _ => 0
  end.

(** With encoder and target laws, closure rows match the source and obey the adapted bound. *)
Definition audit_sq_closure_source_adapted_statement : Prop :=
  forall N B (EN : encoding N) (tg : Graph.t N (N * N)) (tp : prepared EN tg) nodes
    (enc : N -> positive * list B) (weight : B -> nat) encode_source encode_budget,
    (forall n, fst (enc n) = encode EN n) -> (forall edge, Graph.target tg edge = snd edge) ->
    audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
    let '(result, events) := audit_sq_closure_source_rows tp enc nodes in
    result = AnalysesSsaLiveQuery.live_tabulate EN
      (fun n => FinSet.of_list EN (preorder (dfs tp FinSet.empty [n]))) nodes /\
      audit_sq_closure_source_work weight events <= audit_sq_closure_source_budget EN tg tp nodes +
        fold_right (fun event n => audit_sq_closure_source_event_budget encode_budget event + n) 0
          events.

(** The closure contract combines actual-body, per-call and collection source obligations. *)
Definition audit_sq_closure_source_contract_statement : Prop :=
  audit_sq_closure_source_statement /\ audit_sq_closure_source_adapted_statement /\
  audit_map_get_source_work_bound_statement /\ audit_map_set_source_work_bound_statement /\
  audit_finset_of_list_erases_statement.
