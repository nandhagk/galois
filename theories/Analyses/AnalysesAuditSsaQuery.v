(** * Original SSA query component contracts

    These component models retain the original query and preparation theorem types.
    For example, a missing dominator interval ends the lookup sequence immediately.
    Builds on: graph audit primitives and SSA query definitions. *)
From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators GraphAuditBase
  GraphAuditDfs
  GraphAuditVirtual GraphAuditDominators GraphAuditDominatorSelect GraphAuditFrontier.
From Galois.Views Require Import ViewsSsaPoints.
From Galois.Analyses Require Import AnalysesAuditSsaQueryBase AnalysesSsaLiveQuery.
Import List.ListNotations.

(** * Original SSA query component contracts *)

Inductive audit_sq_values_call (N E V : Type) : Type :=
  | AuditSqValuesCase (site : nat)
  | AuditSqValuesPrepare (event : audit_graph_full_call N E)
  | AuditSqValuesDfs (event : audit_dfs_full_call N E)
  | AuditSqExit (n : N) (result : list V)
  | AuditSqOut (n : N) (result : list E)
  | AuditSqEdgeUse (e : E) (result : list V)
  | AuditSqUseGet (v : V) (m : Map.t V (FinSet.t N)) (result : option (FinSet.t N))
  | AuditSqUseAdd (n : N) (s : FinSet.t N)
  | AuditSqUseSet (v : V) (s : FinSet.t N) (m : Map.t V (FinSet.t N))
  | AuditSqUsesElements (m : Map.t V (FinSet.t N)) (rows : list (V * FinSet.t N))
  | AuditSqDefinitionCall (v : V) (result : option N)
  | AuditSqDefinitionSet (v : V) (n : N) (m : Map.t V N)
  | AuditSqValuesOutput (size : nat).

Arguments AuditSqValuesCase {N E V} _.

Arguments AuditSqValuesPrepare {N E V} _.

Arguments AuditSqValuesDfs {N E V} _.

Arguments AuditSqExit {N E V} _ _.

Arguments AuditSqOut {N E V} _ _.

Arguments AuditSqEdgeUse {N E V} _ _.

Arguments AuditSqUseGet {N E V} _ _ _.

Arguments AuditSqUseAdd {N E V} _ _.

Arguments AuditSqUseSet {N E V} _ _ _.

Arguments AuditSqUsesElements {N E V} _ _.

Arguments AuditSqDefinitionCall {N E V} _ _.

Arguments AuditSqDefinitionSet {N E V} _ _ _.

Arguments AuditSqValuesOutput {N E V} _.

Fixpoint audit_sq_flat_uses {N E V} (p : point_uses N E V) (edges : list E)
    : list V * list (audit_sq_values_call N E V) :=
  match edges with
  | [] => ([], [AuditSqValuesCase 0])
  | edge :: rest => let uses := edge_use p edge in
    let '(later, events) := audit_sq_flat_uses p rest in
    (uses ++ later, AuditSqValuesCase 1 :: AuditSqEdgeUse edge uses :: events ++
      [AuditSqValuesOutput (length uses)])
  end.

Definition audit_sq_point_uses {N E V} (p : point_uses N E V) (n : N)
    : list V * list (audit_sq_values_call N E V) :=
  let exits := exit_use p n in let edges := Graph.out (live_graph p) n in
  let '(edge_values, events) := audit_sq_flat_uses p edges in
  (exits ++ edge_values, [AuditSqExit n exits; AuditSqOut n edges] ++ events ++
    [AuditSqValuesOutput (length exits)]).

Fixpoint audit_sq_add_uses {N E V} (EN : encoding N) (EV : encoding V) (n : N)
    (values : list V) (initial : Map.t V (FinSet.t N))
    : Map.t V (FinSet.t N) * list (audit_sq_values_call N E V) :=
  match values with
  | [] => (initial, [AuditSqValuesCase 2])
  | v :: rest => let '(middle, events) := audit_sq_add_uses EN EV n rest initial in
    let found := Map.get EV v middle in let old := match found with
    Some s => s
    | None => FinSet.empty
    end in
    let row := FinSet.add EN n old in let next := Map.set EV v row middle in
    (next, AuditSqValuesCase 3 :: events ++
      [AuditSqUseGet v middle found; AuditSqUseAdd n old; AuditSqUseSet v row middle])
  end.

Fixpoint audit_sq_uses_counted {N E V} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) (nodes : list N) :
    Map.t V (FinSet.t N) * list (audit_sq_values_call N E V) :=
  match nodes with
  | [] => (Map.empty, [AuditSqValuesCase 4])
  | n :: rest => let '(middle, later) := audit_sq_uses_counted EN EV p rest in
    let '(values, value_events) := audit_sq_point_uses p n in
    let '(result, events) := audit_sq_add_uses EN EV n values middle in
    (result, AuditSqValuesCase 5 :: later ++ value_events ++ events)
  end.

Fixpoint audit_sq_defs_counted {N E V A} (EV : encoding V) (home : V -> option N)
    (bindings : list (V * A)) : Map.t V N * list (audit_sq_values_call N E V) :=
  match bindings with
  | [] => (Map.empty, [AuditSqValuesCase 6])
  | (v, _) :: rest => let '(middle, events) := audit_sq_defs_counted EV home rest in
    let found := home v in
    match found with
    | None => (middle, AuditSqValuesCase 7 :: events ++ [AuditSqDefinitionCall v found;
      AuditSqValuesCase 8])
    | Some n => (Map.set EV v n middle, AuditSqValuesCase 7 :: events ++
      [AuditSqDefinitionCall v found; AuditSqValuesCase 9; AuditSqDefinitionSet v n middle])
    end
  end.

Definition audit_sq_values_counted {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) : ssa_query_values N V * list (audit_sq_values_call N E V) :=
  let model := point_model s in let graph := live_graph model in
  let '(index, prep_events) := audit_graph_prepare_full_counted EN graph in
  let '(search, dfs_events) := audit_dfs_full_counted index FinSet.empty (Graph.entries graph) in
  let '(uses, use_events) := audit_sq_uses_counted EN EV model (preorder search) in
  let rows := Map.elements uses in
  let '(defs, def_events) := audit_sq_defs_counted EV (point_definition s) rows in
  (SsaQueryValues defs uses, map AuditSqValuesPrepare prep_events ++ map AuditSqValuesDfs
    dfs_events ++
    use_events ++ [AuditSqUsesElements uses rows] ++ def_events).

Definition audit_sq_values_event_work {N E V} (EN : encoding N) (EV : encoding V)
    (event : audit_sq_values_call N E V) : nat :=
  64 + match event with
  | AuditSqValuesPrepare item => audit_graph_full_event_work item
  | AuditSqValuesDfs item => audit_dfs_full_model_event EN item
  | AuditSqUseGet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_get_weight (encode EV v)
  | AuditSqUseSet v _ _ | AuditSqDefinitionSet v _ _ =>
    audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditSqUseAdd n _ => audit_encoding_weight (audit_key_bits_weight (encode EN n)) +
    audit_set_weight (encode EN n)
  | AuditSqUsesElements m _ => 64 * Nat.pow (S (audit_erase_nodes m)) 3
  | AuditSqValuesOutput size => S size
  | _ => 0
  end.

Definition audit_sq_values_model_work {N E V} (EN : encoding N) (EV : encoding V)
    (events : list (audit_sq_values_call N E V)) : nat :=
  512 * S (length events) * S (length events) +
    fold_right (fun event n => audit_sq_values_event_work EN EV event + n) 0 events.

Definition audit_sq_values_input_rows {B BE N E V} (EN : encoding N) (s : ssa_points B BE N E V) :
    list N :=
  let graph := live_graph (point_model s) in
  preorder (dfs (prepare EN graph) FinSet.empty (Graph.entries graph)).

Definition audit_sq_values_input_list {B BE N E V} (s : ssa_points B BE N E V) (nodes : list N) :
    list V :=
  let model := point_model s in
  flat_map (fun n => exit_use model n ++ flat_map (edge_use model) (Graph.out (live_graph model) n))
    nodes.

Definition audit_sq_values_input_event_bound {B BE N E V} (EN : encoding N)
    (s : ssa_points B BE N E V) : nat :=
  let graph := live_graph (point_model s) in let p := prepare EN graph in
  let nodes := audit_sq_values_input_rows EN s in
  let edges := fold_right (fun n total => length (Graph.out graph n) + total) 0 nodes in
  let uses := length (audit_sq_values_input_list s nodes) in
  64 * S (length nodes + edges + uses) + audit_graph_prepare_full_event_bound graph +
    audit_dfs_full_input_event_bound p (Graph.entries graph).

Definition audit_sq_values_input_width {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) : nat :=
  let graph := live_graph (point_model s) in let p := prepare EN graph in
  let nodes := audit_sq_values_input_rows EN s in
  Nat.max (audit_dfs_full_input_width EN graph p (Graph.entries graph))
    (Nat.max (audit_graph_prepare_input_width EN graph)
      (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v))
        (audit_sq_values_input_list s nodes)))).

Definition audit_sq_values_input_budget {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) : nat :=
  let count := audit_sq_values_input_event_bound EN s in
  let width := audit_sq_values_input_width EN EV s in
  4096 * Nat.pow (S count) 4 * Nat.pow (S width) 3.

(** Value preparation returns the original index within the stated event and model-work bounds. *)
Definition audit_sq_values_counted_statement : Prop :=
  forall B BE N E V (EN : encoding N) (EV : encoding V) (s : ssa_points B BE N E V),
    let '(result, events) := audit_sq_values_counted EN EV s in
    result = prepare_ssa_query_values EN EV s /\
      length events <= audit_sq_values_input_event_bound EN s /\
      audit_sq_values_model_work EN EV events <= audit_sq_values_input_budget EN EV s.

Inductive audit_sq_reduced_call (N E : Type) : Type :=
  | AuditSqReducedCase (site : nat)
  | AuditSqReducedTarget (e : E) (n : N)
  | AuditSqReducedSource (e : E) (n : N)
  | AuditSqReducedDom (event : audit_frontier_dom_call N)
  | AuditSqReducedOut (n : N) (m : Map.t N (list E)) (result : option (list E))
  | AuditSqReducedGet (n : N) (m : Map.t N (FinSet.t N)) (result : option (FinSet.t N))
  | AuditSqReducedAdd (n : N) (s : FinSet.t N)
  | AuditSqReducedUnion (lhs rhs result : FinSet.t N)
  | AuditSqReducedSet (n : N) (row : FinSet.t N) (m : Map.t N (FinSet.t N)).

Arguments AuditSqReducedCase {N E} _.

Arguments AuditSqReducedTarget {N E} _ _.

Arguments AuditSqReducedSource {N E} _ _.

Arguments AuditSqReducedDom {N E} _.

Arguments AuditSqReducedOut {N E} _ _ _.

Arguments AuditSqReducedGet {N E} _ _ _.

Arguments AuditSqReducedAdd {N E} _ _.

Arguments AuditSqReducedUnion {N E} _ _ _.

Arguments AuditSqReducedSet {N E} _ _ _.

Definition audit_sq_back_counted {N E} (EN : encoding N) (g : Graph.t N E)
    (r : dfs_result N E) (e : E) : bool * list (audit_sq_reduced_call N E) :=
  let target := Graph.target g e in let source := Graph.source g e in
  let tree := DomTree Map.empty (pre_num r) (post_num r) in
  let '(result, events) := audit_frontier_dom_counted EN tree target source in
  (result, [AuditSqReducedTarget e target; AuditSqReducedSource e source] ++
    map AuditSqReducedDom events).

Fixpoint audit_sq_r_edges_counted {N E} (EN : encoding N) (g : Graph.t N E)
    (r : dfs_result N E) (index : Map.t N (FinSet.t N)) (edges : list E) (initial : FinSet.t N)
    : FinSet.t N * list (audit_sq_reduced_call N E) :=
  match edges with
  | [] => (initial, [AuditSqReducedCase 0])
  | edge :: rest => let '(middle, later) := audit_sq_r_edges_counted EN g r index rest initial in
    let '(back, here) := audit_sq_back_counted EN g r edge in
    if back then (middle, AuditSqReducedCase 1 :: later ++ here ++ [AuditSqReducedCase 2])
    else let target := Graph.target g edge in let found := Map.get EN target index in
      let reachable := match found with
      Some s => s
      | None => FinSet.empty
      end in
      let result := FinSet.union EN reachable middle in
      (result, AuditSqReducedCase 1 :: later ++ here ++ [AuditSqReducedCase 3;
        AuditSqReducedTarget edge target; AuditSqReducedGet target index found;
        AuditSqReducedUnion reachable middle result])
  end.

Fixpoint audit_sq_r_rows_counted {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (r : dfs_result N E) (order : list N)
    : Map.t N (FinSet.t N) * list (audit_sq_reduced_call N E) :=
  match order with
  | [] => (Map.empty, [AuditSqReducedCase 4])
  | n :: rest => let '(middle, later) := audit_sq_r_rows_counted p r rest in
    let initial := FinSet.add EN n FinSet.empty in
    let found := Map.get EN n (out_index p) in let edges := match found with
    Some es => es
    | None => []
    end in
    let '(row, here) := audit_sq_r_edges_counted EN g r middle edges initial in
    (Map.set EN n row middle, AuditSqReducedCase 5 :: later ++
      [AuditSqReducedAdd n FinSet.empty; AuditSqReducedOut n (out_index p) found] ++ here ++
      [AuditSqReducedSet n row middle])
  end.

Definition audit_sq_reduced_event_work {N E} (EN : encoding N) (event : audit_sq_reduced_call N E) :
    nat :=
  64 + match event with
  | AuditSqReducedDom item => audit_frontier_dom_event_work EN item
  | AuditSqReducedOut n _ _ | AuditSqReducedGet n _ _ =>
    audit_encoding_weight (audit_key_bits_weight (encode EN n)) + audit_get_weight (encode EN n)
  | AuditSqReducedAdd n _ | AuditSqReducedSet n _ _ =>
    audit_encoding_weight (audit_key_bits_weight (encode EN n)) + audit_set_weight (encode EN n)
  | AuditSqReducedUnion lhs rhs _ => let size := audit_erase_nodes lhs + audit_erase_nodes rhs in
    64 * S size * S size
  | _ => 0
  end.

Definition audit_sq_reduced_work {N E} (EN : encoding N) (events : list (audit_sq_reduced_call N E))
    : nat :=
  512 * S (length events) * S (length events) +
    fold_right (fun event total => audit_sq_reduced_event_work EN event + total) 0 events.

Definition audit_sq_reduced_input_edges {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (order : list N) : list E := flat_map (succ_edges p) order.

Definition audit_sq_reduced_width {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (r : dfs_result N E) (order : list N) : nat :=
  let edges := audit_sq_reduced_input_edges p order in
  let vertices := order ++ map (Graph.target g) edges ++ map (Graph.source g) edges ++
    map fst (Map.elements (pre_num r)) ++ map fst (Map.elements (post_num r)) in
  let numbers := map snd (Map.elements (pre_num r)) ++ map snd (Map.elements (post_num r)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EN v)) vertices))
    (fold_right Nat.max 0 (map audit_key_bits_weight numbers)).

Definition audit_sq_reduced_event_bound {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (order : list N) : nat :=
  32 * S (length order + length (audit_sq_reduced_input_edges p order)).

Definition audit_sq_reduced_budget {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (r : dfs_result N E) (order : list N) : nat :=
  let count := audit_sq_reduced_event_bound p order in
  let width := audit_sq_reduced_width EN g p r order in
  4096 * Nat.pow (S count) 4 * Nat.pow (S width) 2.

(** Reduced-row construction returns the source rows within its event and work budgets. *)
Definition audit_sq_reduced_statement : Prop :=
  forall N E (EN : encoding N) (g : Graph.t N E) (p : prepared EN g) (r : dfs_result N E) order,
    let '(result, events) := audit_sq_r_rows_counted p r order in
    result = AnalysesSsaLiveQuery.live_r_build EN (Graph.target g) (succ_edges p)
      (fun e => ancestor_b EN r (Graph.target g e) (Graph.source g e)) order /\
      length events <= audit_sq_reduced_event_bound p order /\
      audit_sq_reduced_work EN events <= audit_sq_reduced_budget EN g p r order.

Inductive audit_sq_t_call (N E : Type) : Type :=
  | AuditSqTCase (site : nat)
  | AuditSqTReduced (event : audit_sq_reduced_call N E)
  | AuditSqTGet (v : N) (m : Map.t N (FinSet.t N)) (result : option (FinSet.t N))
  | AuditSqTOut (v : N) (m : Map.t N (list E)) (result : option (list E))
  | AuditSqTElements (set : FinSet.t N) (result : list N)
  | AuditSqTTarget (e : E) (v : N)
  | AuditSqTMember (v : N) (set : FinSet.t N) (result : bool)
  | AuditSqTAdd (v : N) (set : FinSet.t N)
  | AuditSqTSet (v : N) (row : list (N * N)) (m : Map.t N (list (N * N)))
  | AuditSqTOutput (size : nat).

Arguments AuditSqTCase {N E} _.

Arguments AuditSqTReduced {N E} _.

Arguments AuditSqTGet {N E} _ _ _.

Arguments AuditSqTOut {N E} _ _ _.

Arguments AuditSqTElements {N E} _ _.

Arguments AuditSqTTarget {N E} _ _.

Arguments AuditSqTMember {N E} _ _ _.

Arguments AuditSqTAdd {N E} _ _.

Arguments AuditSqTSet {N E} _ _ _.

Arguments AuditSqTOutput {N E} _.

Fixpoint audit_sq_t_filter {N E} (EN : encoding N) (g : Graph.t N E) (r : dfs_result N E)
    (reduced : FinSet.t N) (edges : list E) : list E * list (audit_sq_t_call N E) :=
  match edges with
  | [] => ([], [AuditSqTCase 0])
  | e :: rest => let '(back, back_events) := audit_sq_back_counted EN g r e in
    let target := Graph.target g e in let member := FinSet.mem EN target reduced in
    let keep := back && negb member in
    let '(later, events) := audit_sq_t_filter EN g r reduced rest in
    (if keep then e :: later else later, AuditSqTCase 1 :: map AuditSqTReduced back_events ++
      [AuditSqTTarget e target; AuditSqTMember target reduced member;
       AuditSqTCase (if keep then 2 else 3)] ++ events)
  end.

Fixpoint audit_sq_t_targets {N E} (g : Graph.t N E) (edges : list E) :
    list N * list (audit_sq_t_call N E) :=
  match edges with
  | [] => ([], [AuditSqTCase 4])
  | e :: rest => let target := Graph.target g e in
    let '(later, events) := audit_sq_t_targets g rest in
    (target :: later, AuditSqTCase 5 :: AuditSqTTarget e target :: events)
  end.

Fixpoint audit_sq_t_vertices {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (r : dfs_result N E) (reduced : FinSet.t N) (vertices : list N)
    : list N * list (audit_sq_t_call N E) :=
  match vertices with
  | [] => ([], [AuditSqTCase 6])
  | v :: rest => let found := Map.get EN v (out_index p) in
    let edges := match found with
    Some xs => xs
    | None => []
    end in
    let '(filtered, filter_events) := audit_sq_t_filter EN g r reduced edges in
    let '(targets, target_events) := audit_sq_t_targets g filtered in
    let '(later, events) := audit_sq_t_vertices p r reduced rest in
    (targets ++ later, AuditSqTCase 7 :: AuditSqTOut v (out_index p) found ::
      filter_events ++ target_events ++ events ++ [AuditSqTOutput (length targets)])
  end.

Fixpoint audit_sq_t_set_counted {N E} (EN : encoding N) (vertices : list N) (set : FinSet.t N)
    : FinSet.t N * list (audit_sq_t_call N E) :=
  match vertices with
  | [] => (set, [AuditSqTCase 8])
  | v :: rest => let next := FinSet.add EN v set in
    let '(result, events) := audit_sq_t_set_counted EN rest next in
    (result, AuditSqTCase 9 :: AuditSqTAdd v set :: events)
  end.

Definition audit_sq_t_edges_counted {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (n : N)
    : FinSet.t N * list (audit_sq_t_call N E) :=
  let found := Map.get EN n rm in let reduced := match found with
  Some s => s
  | None => FinSet.empty
  end in
  let vertices := FinSet.elements reduced in
  let '(targets, target_events) := audit_sq_t_vertices p r reduced vertices in
  let '(result, set_events) := audit_sq_t_set_counted EN targets FinSet.empty in
  (result, [AuditSqTGet n rm found; AuditSqTElements reduced vertices] ++ target_events ++
    set_events).

Fixpoint audit_sq_t_rows_counted {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (nodes : list N)
    : Map.t N (list (N * N)) * list (audit_sq_t_call N E) :=
  match nodes with
  | [] => (Map.empty, [AuditSqTCase 10])
  | n :: rest => let '(middle, later) := audit_sq_t_rows_counted p r rm rest in
    let '(edges, edge_events) := audit_sq_t_edges_counted p r rm n in
    let vertices := FinSet.elements edges in let row := map (fun v => (n, v)) vertices in
    (Map.set EN n row middle, AuditSqTCase 11 :: later ++ edge_events ++
      [AuditSqTElements edges vertices; AuditSqTOutput (length vertices);
       AuditSqTSet n row middle])
  end.

Definition audit_sq_t_graph_with_rows {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (nodes : list N)
    : Graph.t N (N * N) * (Map.t N (list (N * N)) * list (audit_sq_t_call N E)) :=
  let '(rows, events) := audit_sq_t_rows_counted p r rm nodes in
  (Graph.Make [] nodes (fun n => match Map.get EN n rows with
    Some es => es
    | None => []
    end) fst snd, (rows, events)).

Definition audit_sq_t_graph_counted {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (nodes : list N)
    : Graph.t N (N * N) * list (audit_sq_t_call N E) :=
  let '(graph, (_, events)) := audit_sq_t_graph_with_rows p r rm nodes in (graph, events).

Definition audit_sq_t_event_work {N E} (EN : encoding N) (event : audit_sq_t_call N E) : nat :=
  64 + match event with
  | AuditSqTReduced item => audit_sq_reduced_event_work EN item
  | AuditSqTGet v _ _ | AuditSqTOut v _ _ | AuditSqTMember v _ _ =>
    audit_encoding_weight (audit_key_bits_weight (encode EN v)) + audit_get_weight (encode EN v)
  | AuditSqTAdd v _ | AuditSqTSet v _ _ =>
    audit_encoding_weight (audit_key_bits_weight (encode EN v)) + audit_set_weight (encode EN v)
  | AuditSqTElements set _ => 64 * Nat.pow (S (audit_erase_nodes set)) 3
  | AuditSqTOutput size => S size
  | _ => 0
  end.

Definition audit_sq_t_work {N E} (EN : encoding N) (events : list (audit_sq_t_call N E)) : nat :=
  512 * S (length events) * S (length events) +
    fold_right (fun event n => audit_sq_t_event_work EN event + n) 0 events.

Definition audit_sq_t_input_vertices {N} (rm : Map.t N (FinSet.t N)) (nodes : list N) : list N :=
  nodes ++ flat_map (fun row => FinSet.elements (snd row)) (Map.elements rm).

Definition audit_sq_t_input_scale {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (rm : Map.t N (FinSet.t N)) (nodes : list N) : nat :=
  let vertices := audit_sq_t_input_vertices rm nodes in
  1 + length vertices + audit_erase_nodes rm +
    fold_right (fun row n => audit_erase_nodes (snd row) + n) 0 (Map.elements rm) +
    length (audit_sq_reduced_input_edges p vertices).

Definition audit_sq_t_event_bound {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (rm : Map.t N (FinSet.t N)) (nodes : list N) : nat :=
  1024 * Nat.pow (S (audit_sq_t_input_scale p rm nodes)) 5.

Definition audit_sq_t_budget {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (r : dfs_result N E) (rm : Map.t N (FinSet.t N)) (nodes : list N) : nat :=
  let count := audit_sq_t_event_bound p rm nodes in
  let width := audit_sq_reduced_width EN g p r (audit_sq_t_input_vertices rm nodes) in
  4096 * Nat.pow (S count) 4 * Nat.pow (S width) 2.

(** T-graph construction returns the source graph within its event and work budgets. *)
Definition audit_sq_t_graph_statement : Prop :=
  forall N E (EN : encoding N) (g : Graph.t N E) (p : prepared EN g) (r : dfs_result N E) rm nodes,
    let '(result, events) := audit_sq_t_graph_counted p r rm nodes in
    result = AnalysesSsaLiveQuery.live_t_graph EN g (succ_edges p)
      (fun e => ancestor_b EN r (Graph.target g e) (Graph.source g e)) rm nodes /\
      length events <= audit_sq_t_event_bound p rm nodes /\ audit_sq_t_work EN events <=
        audit_sq_t_budget EN g p r rm nodes.

Inductive audit_sq_tbody (N : Type) : Type :=
  | AuditSqTBodyOut (n : N) (rows : Map.t N (list (N * N))) (result : option (list (N * N)))
  | AuditSqTBodyTarget (edge : N * N)
  | AuditSqTBodyEncode (n : N) (code : positive).

Arguments AuditSqTBodyOut {N} _ _ _.

Arguments AuditSqTBodyTarget {N} _.

Arguments AuditSqTBodyEncode {N} _ _.

Definition audit_sq_tbody_out {N} (EN : encoding N) (rows : Map.t N (list (N * N))) (n : N)
    : list (N * N) * list (audit_sq_tbody N) :=
  let found := Map.get EN n rows in
  (match found with
  Some es => es
  | None => []
  end, [AuditSqTBodyOut n rows found]).

Definition audit_sq_tbody_target {N} (edge : N * N) : N * list (audit_sq_tbody N) :=
  (snd edge, [AuditSqTBodyTarget edge]).

Definition audit_sq_tbody_encode {N} (EN : encoding N) (n : N) :
    positive * list (audit_sq_tbody N) :=
  let code := encode EN n in (code, [AuditSqTBodyEncode n code]).

Definition audit_sq_t_prepare_callbacks {N} (EN : encoding N) (rows : Map.t N (list (N * N)))
    : audit_prepare_callback_model N (N * N) (audit_sq_tbody N) :=
  AuditPrepareCallbackModel _ _ _ (audit_sq_tbody_out EN rows) audit_sq_tbody_target
    (audit_sq_tbody_encode EN).

Definition audit_sq_t_dfs_callbacks {N} (EN : encoding N) : audit_dfs_callback_model N (N * N)
    (audit_sq_tbody N) :=
  AuditDfsCallbackModel _ _ _ audit_sq_tbody_target (audit_sq_tbody_encode EN).

Inductive audit_sq_tclosure_call (N : Type) : Type :=
  | AuditSqTCClosureCase (site : nat)
  | AuditSqTCClosureDfs (event : audit_dfs_nested_event N (N * N) (audit_sq_tbody N))
  | AuditSqTCClosureAdd (n : N) (s : FinSet.t N)
  | AuditSqTCClosureSet (n : N) (s : FinSet.t N) (m : Map.t N (FinSet.t N)).

Arguments AuditSqTCClosureCase {N} _.

Arguments AuditSqTCClosureDfs {N} _.

Arguments AuditSqTCClosureAdd {N} _ _.

Arguments AuditSqTCClosureSet {N} _ _ _.

Fixpoint audit_sq_tclosure_set {N} (EN : encoding N) (nodes : list N) (s : FinSet.t N)
    : FinSet.t N * list (audit_sq_tclosure_call N) :=
  match nodes with
  | [] => (s, [AuditSqTCClosureCase 0])
  | n :: rest => let next := FinSet.add EN n s in
    let '(result, events) := audit_sq_tclosure_set EN rest next in
    (result, AuditSqTCClosureCase 1 :: AuditSqTCClosureAdd n s :: events)
  end.

Fixpoint audit_sq_tclosure_rows {N} {EN : encoding N} {tg : Graph.t N (N * N)}
    (tp : prepared EN tg) (nodes : list N) :
    Map.t N (FinSet.t N) * list (audit_sq_tclosure_call N) :=
  match nodes with
  | [] => (Map.empty, [AuditSqTCClosureCase 2])
  | n :: rest => let '(middle, later) := audit_sq_tclosure_rows tp rest in
    let '(search, dfs_events) := audit_dfs_nested_counted tp (audit_sq_t_dfs_callbacks EN)
      FinSet.empty [n] in
    let '(row, set_events) := audit_sq_tclosure_set EN (preorder search) FinSet.empty in
    (Map.set EN n row middle, AuditSqTCClosureCase 3 :: later ++ map AuditSqTCClosureDfs
      dfs_events ++
      set_events ++ [AuditSqTCClosureSet n row middle])
  end.

Definition audit_sq_tbody_work {N} (EN : encoding N) (event : audit_sq_tbody N) : nat :=
  64 + match event with
  | AuditSqTBodyOut n _ _ => audit_encoding_weight (audit_key_bits_weight (encode EN n)) +
    audit_get_weight (encode EN n)
  | AuditSqTBodyEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditSqTBodyTarget _ => 0
  end.

Definition audit_sq_tclosure_event_work {N} (EN : encoding N) (event : audit_sq_tclosure_call N) :
    nat :=
  64 + match event with
  | AuditSqTCClosureDfs (outer, body) => audit_dfs_full_model_event EN outer +
    fold_right (fun item n => audit_sq_tbody_work EN item + n) 0 body
  | AuditSqTCClosureAdd n _ | AuditSqTCClosureSet n _ _ =>
    audit_encoding_weight (audit_key_bits_weight (encode EN n)) + audit_set_weight (encode EN n)
  | AuditSqTCClosureCase _ => 0
  end.

Definition audit_sq_tclosure_work {N} (EN : encoding N) (events : list (audit_sq_tclosure_call N)) :
    nat :=
  512 * S (length events) * S (length events) +
    fold_right (fun event n => audit_sq_tclosure_event_work EN event + n) 0 events.

Definition audit_sq_tclosure_event_bound {N} {EN : encoding N} {tg : Graph.t N (N * N)}
    (tp : prepared EN tg) (nodes : list N) : nat :=
  64 * S (length nodes) * S (Pos.to_nat (fuel tp)).

Definition audit_sq_tclosure_budget {N} (EN : encoding N) (tg : Graph.t N (N * N))
    (tp : prepared EN tg) (nodes : list N) : nat :=
  let count := audit_sq_tclosure_event_bound tp nodes in
  let width := Nat.max (audit_dfs_full_input_width EN tg tp nodes)
    (audit_key_bits_weight (Pos.of_succ_nat (S count))) in
  2048 * S count * S count + count * (512 + 24 * width).

(** For pair-projection targets, closure rows match DFS tabulation within the stated bounds. *)
Definition audit_sq_tclosure_statement : Prop :=
  forall N (EN : encoding N) (tg : Graph.t N (N * N)) (tp : prepared EN tg) nodes,
    (forall edge, Graph.target tg edge = snd edge) ->
    let '(result, events) := audit_sq_tclosure_rows tp nodes in
    result = AnalysesSsaLiveQuery.live_tabulate EN
      (fun n => FinSet.of_list EN (preorder (dfs tp FinSet.empty [n]))) nodes /\
    length events <= audit_sq_tclosure_event_bound tp nodes /\
    audit_sq_tclosure_work EN events <= audit_sq_tclosure_budget EN tg tp nodes.

(** The trace retains each graph preparation phase and the selected dominance execution. *)
Record audit_sq_graph_trace (N E : Type) : Type := AuditSqGraphTrace {
  audit_sq_graph_prepare_events : list (audit_graph_full_call N E);
  audit_sq_graph_initial_dfs_events : list (audit_dfs_full_call N E);
  audit_sq_graph_reduced_events : list (audit_sq_reduced_call N E);
  audit_sq_graph_t_events : list (audit_sq_t_call N E);
  audit_sq_graph_t_prepare_events : list (audit_prepare_nested_event N (N * N) (audit_sq_tbody N));
  audit_sq_graph_dom_events : audit_dom_backend_trace N E;
  audit_sq_graph_closure_events : list (audit_sq_tclosure_call N)
}.

Arguments AuditSqGraphTrace {N E} _ _ _ _ _ _ _.

(** A graph run couples preparation, dominance, reduced rows and closure in one trace. *)
Definition audit_sq_graph_run {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (result : ssa_query_graph N E) (trace : audit_sq_graph_trace N E) : Prop :=
  let '(p, prepare_events) := audit_graph_prepare_full_counted EN g in
  let '(search, dfs_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let '(rm, reduced_events) := audit_sq_r_rows_counted p search (rpo search) in
  let '(tg, (rows, t_events)) := audit_sq_t_graph_with_rows p search rm (preorder search) in
  let '(tp, t_prepare_events) := audit_graph_prepare_nested_counted EN tg
    (audit_sq_t_prepare_callbacks EN rows) in
  exists tree dom_events,
    audit_dom_tree_with_run p SimpleLT tree dom_events /\
    let '(closure, closure_events) := audit_sq_tclosure_rows tp (preorder search) in
    result = SsaQueryGraph g search tree rm closure /\
      trace = AuditSqGraphTrace prepare_events dfs_events reduced_events t_events t_prepare_events
        dom_events closure_events.

(** Some recorded graph run returns the original prepared SSA query graph. *)
Definition audit_sq_graph_erasure_statement : Prop :=
  forall N E (EN : encoding N) (EE : encoding E) (g : Graph.t N E),
    exists result trace, audit_sq_graph_run EN EE g result trace /\
      result = prepare_ssa_query_graph EN EE g.

Inductive audit_sq_dom_call (N : Type) : Type :=
  | AuditSqDomGet (n : N) (m : Map.t N positive) (r : option positive)
  | AuditSqDomLe (a b : positive) (r : bool).

Arguments AuditSqDomGet {N} _ _ _.

Arguments AuditSqDomLe {N} _ _ _.

Definition audit_sq_dom_counted {N} (EN : encoding N) (tree : dom_tree N) (d t : N)
    : bool * list (audit_sq_dom_call N) :=
  let a := Map.get EN d (tin tree) in
  match a with
  | None => (false, [AuditSqDomGet d (tin tree) a])
  | Some av => let b := Map.get EN t (tin tree) in
    match b with
    | None => (false, [AuditSqDomGet d (tin tree) a; AuditSqDomGet t (tin tree) b])
    | Some bv => let c := Map.get EN d (tout tree) in
      match c with
      | None => (false, [AuditSqDomGet d (tin tree) a; AuditSqDomGet t (tin tree) b;
        AuditSqDomGet d (tout tree) c])
      | Some cv => let e := Map.get EN t (tout tree) in
        match e with
        | None => (false, [AuditSqDomGet d (tin tree) a; AuditSqDomGet t (tin tree) b;
          AuditSqDomGet d (tout tree) c; AuditSqDomGet t (tout tree) e])
        | Some ev => let first := Pos.leb av bv in let second := Pos.leb ev cv in
          (first && second, [AuditSqDomGet d (tin tree) a; AuditSqDomGet t (tin tree) b;
            AuditSqDomGet d (tout tree) c; AuditSqDomGet t (tout tree) e;
            AuditSqDomLe av bv first; AuditSqDomLe ev cv second])
        end
      end
    end
  end.

Inductive audit_sq_query_call (N V : Type) : Type :=
  | AuditSqDefinition (x : V) (m : Map.t V N) (r : option N)
  | AuditSqUses (x : V) (m : Map.t V (FinSet.t N)) (r : FinSet.t N)
  | AuditSqClosure (n : N) (m : Map.t N (FinSet.t N)) (r : FinSet.t N)
  | AuditSqCompare (d t : N) (same : bool)
  | AuditSqDominates (d t : N) (tree : dom_tree N) (result : bool) (calls : list (audit_sq_dom_call
    N))
  | AuditSqReduced (t : N) (m : Map.t N (FinSet.t N)) (r : FinSet.t N)
  | AuditSqMember (u : N) (set : FinSet.t N) (result : bool).

Arguments AuditSqDefinition {N V} _ _ _.

Arguments AuditSqUses {N V} _ _ _.

Arguments AuditSqClosure {N V} _ _ _.

Arguments AuditSqCompare {N V} _ _ _.

Arguments AuditSqDominates {N V} _ _ _ _ _.

Arguments AuditSqReduced {N V} _ _ _.

Arguments AuditSqMember {N V} _ _ _.

Fixpoint audit_sq_members_counted {N V} (EN : encoding N) (set : FinSet.t N)
    (uses : list N) : bool * list (audit_sq_query_call N V) :=
  match uses with
  | [] => (false, [])
  | u :: rest =>
    let found := FinSet.mem EN u set in
    let '(later, events) := audit_sq_members_counted EN set rest in
    (found || later, AuditSqMember u set found :: events)
  end.

Fixpoint audit_sq_rows_counted {N E V} (EN : encoding N) (idx : ssa_query_graph N E)
    (d : N) (uses rows : list N) : bool * list (audit_sq_query_call N V) :=
  match rows with
  | [] => (false, [])
  | t :: rest =>
    let same := Pos.eqb (encode EN d) (encode EN t) in
    let '(dom, dom_events) := audit_sq_dom_counted EN (query_dom idx) d t in
    let reduced := live_index_get EN t (query_reduced idx) in
    let '(member, members) := audit_sq_members_counted EN reduced uses in
    let here := negb same && dom && member in
    let '(later, events) := audit_sq_rows_counted EN idx d uses rest in
    (here || later, AuditSqCompare d t same :: AuditSqDominates d t (query_dom idx) dom
      dom_events ::
      AuditSqReduced t (query_reduced idx) reduced :: members ++ events)
  end.

Definition audit_sq_query_counted {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (n : N) (x : V)
    : bool * list (audit_sq_query_call N V) :=
  let definition := Map.get EV x (query_def values) in
  match definition with
  | None => (false, [AuditSqDefinition x (query_def values) definition])
  | Some d =>
    let us := live_index_get EV x (query_uses values) in
    let uses := FinSet.elements us in
    let rows := live_index_get EN n (query_back_closure idx) in
    let '(result, events) := audit_sq_rows_counted EN idx d uses (FinSet.elements rows) in
    (result, AuditSqDefinition x (query_def values) definition ::
      AuditSqUses x (query_uses values) us :: AuditSqClosure n (query_back_closure idx) rows ::
      events)
  end.

Definition audit_sq_dom_event_work {N} (EN : encoding N) (event : audit_sq_dom_call N) : nat :=
  64 + match event with
  | AuditSqDomGet n _ _ => audit_get_weight (encode EN n) +
    audit_encoding_weight (audit_key_bits_weight (encode EN n))
  | AuditSqDomLe a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  end.

Definition audit_sq_query_event_work {N V} (EN : encoding N) (EV : encoding V)
    (event : audit_sq_query_call N V) : nat :=
  let node_read n := audit_get_weight (encode EN n) +
    audit_encoding_weight (audit_key_bits_weight (encode EN n)) in
  let value_read x := audit_get_weight (encode EV x) +
    audit_encoding_weight (audit_key_bits_weight (encode EV x)) in
  64 + match event with
  | AuditSqDefinition x _ _ | AuditSqUses x _ _ => value_read x
  | AuditSqClosure n _ _ | AuditSqReduced n _ _ | AuditSqMember n _ _ => node_read n
  | AuditSqCompare d t _ => audit_encoding_weight (audit_key_bits_weight (encode EN d)) +
    audit_encoding_weight (audit_key_bits_weight (encode EN t)) +
    audit_binary_weight (Z.pos (encode EN d)) (Z.pos (encode EN t))
  | AuditSqDominates _ _ _ _ calls =>
    fold_right (fun e total => audit_sq_dom_event_work EN e + total) 0 calls
  end.

Definition audit_sq_query_model_work {N V} (EN : encoding N) (EV : encoding V)
    (events : list (audit_sq_query_call N V)) : nat :=
  64 * S (length events) * S (length events) +
    fold_right (fun e total => audit_sq_query_event_work EN EV e + total) 0 events.

Definition audit_sq_query_event_bound {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (n : N) (x : V) : nat :=
  let uses := FinSet.elements (live_index_get EV x (query_uses values)) in
  let rows := FinSet.elements (live_index_get EN n (query_back_closure idx)) in
  3 + length rows * (3 + length uses).

Definition audit_sq_query_input_width {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (n : N) (x : V) : nat :=
  let nodes := n :: FinSet.elements (live_index_get EV x (query_uses values)) ++
    FinSet.elements (live_index_get EN n (query_back_closure idx)) ++
    match Map.get EV x (query_def values) with
    Some d => [d]
    | None => []
    end in
  Nat.max (audit_key_bits_weight (encode EV x))
    (Nat.max (fold_right Nat.max 0 (map (fun node => audit_key_bits_weight (encode EN node)) nodes))
      (fold_right Nat.max 0 (map (fun binding => audit_key_bits_weight (snd binding))
        (Map.elements (tin (query_dom idx)) ++ Map.elements (tout (query_dom idx)))))).

Definition audit_sq_query_input_budget {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (n : N) (x : V) : nat :=
  let events := audit_sq_query_event_bound EN EV idx values n x in
  let width := audit_sq_query_input_width EN EV idx values n x in
  64 * S events * S events + events * (8 * (70 + 6 * width)).

(** A dominance query returns the original Boolean and records at most six calls. *)
Definition audit_sq_dom_counted_statement : Prop :=
  forall N (EN : encoding N) tree d t,
    let '(result, events) := audit_sq_dom_counted EN tree d t in
    result = dominates_b EN tree d t /\ length events <= 6.

(** A recorded query returns the original answer within the event and model-work bounds. *)
Definition audit_sq_query_counted_statement : Prop :=
  forall N E V (EN : encoding N) (EV : encoding V) (idx : ssa_query_graph N E)
      (values : ssa_query_values N V) n x,
    let '(result, events) := audit_sq_query_counted EN EV idx values n x in
    result = ssa_live_query EN EV idx values n x /\
      length events <= audit_sq_query_event_bound EN EV idx values n x /\
      audit_sq_query_model_work EN EV events <= audit_sq_query_input_budget EN EV idx values n x.
