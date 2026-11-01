(** * General liveness tabulation source

    Tabulation decodes the actual rules database at each listed graph node.
    For example, each node recomputes its two variable-universe arguments.
    Builds on: collection source models and liveness fact extraction. *)
From Stdlib Require Import List Bool PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditEncoding.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Views Require Import ViewsGraph.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve.
From Galois.Analyses Require Import AnalysesLiveness AnalysesRules AnalysesSsaLiveQuery
  AnalysesAuditSsaSparse.
Import List.ListNotations.

(** * General liveness tabulation source *)

Inductive audit_live_tab_event (N E V B : Type) : Type :=
  | LiveTabCase : nat -> audit_live_tab_event N E V B
  | LiveTabList : nat -> audit_live_tab_event N E V B
  | LiveTabSparse : audit_live_sparse_event N E V B -> audit_live_tab_event N E V B
  | LiveTabSet : audit_set_event V B -> audit_live_tab_event N E V B
  | LiveTabElements : audit_set_elements_event V -> audit_live_tab_event N E V B
  | LiveTabRows : audit_map_event N (FinSet.t V) B -> audit_live_tab_event N E V B
  | LiveTabDb : audit_map_event pred (FinSet.t tuple) unit -> audit_live_tab_event N E V B
  | LiveTabTuple : audit_set_event tuple
      (audit_list_event positive (audit_basic_encoding_event positive)) -> audit_live_tab_event N E
        V B
  | LiveTabNode : N -> positive -> list B -> audit_live_tab_event N E V B
  | LiveTabValue : V -> positive -> list B -> audit_live_tab_event N E V B.

Arguments LiveTabCase {N E V B} _.

Arguments LiveTabList {N E V B} _.

Arguments LiveTabSparse {N E V B} _.

Arguments LiveTabSet {N E V B} _.

Arguments LiveTabElements {N E V B} _.

Arguments LiveTabRows {N E V B} _.

Arguments LiveTabDb {N E V B} _.

Arguments LiveTabTuple {N E V B} _.

Arguments LiveTabNode {N E V B} _ _ _.

Arguments LiveTabValue {N E V B} _ _ _.

Fixpoint audit_live_tab_edge_values {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (edges : list E) : list V * list (audit_live_tab_event N E V B) :=
  match edges with
  | [] => ([], [LiveTabCase 0])
  | e :: rest => let '(uses, ub) := sl_use cb e in let '(defs, db) := sl_def cb e in
    let '(later, events) := audit_live_tab_edge_values cb rest in
    (uses ++ defs ++ later,
      LiveTabSparse (SlUse e uses ub) :: LiveTabSparse (SlDef e defs db) ::
      LiveTabList (length uses) :: events ++ [LiveTabList (length uses + length defs)])
  end.

Fixpoint audit_live_tab_exits {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (nodes : list N) : list V * list (audit_live_tab_event N E V B) :=
  match nodes with
  | [] => ([], [LiveTabCase 1])
  | n :: rest => let '(values, body) := sl_exit cb n in
    let '(later, events) := audit_live_tab_exits cb rest in
    (values ++ later, LiveTabSparse (SlExit n values body) :: events ++
      [LiveTabList (length values)])
  end.

(** Universe enumeration is repeated where the source uses it twice. *)
Definition audit_live_tab_universe {N E V B} (g : Graph.t N E)
    (cb : audit_live_sparse_callbacks N E V B)
    : list V * list (audit_live_tab_event N E V B) :=
  let '(edges, edge_events) := audit_live_sparse_edges cb (Graph.nodes g) in
  let '(edge_values, edge_calls) := audit_live_tab_edge_values cb edges in
  let '(exit_values, exit_calls) := audit_live_tab_exits cb (Graph.nodes g) in
  let '(set, set_calls) := audit_finset_of_list (sl_value_encode cb) (edge_values ++ exit_values) in
  let '(values, element_calls) := audit_finset_elements set in
  (values, map LiveTabSparse edge_events ++ edge_calls ++ exit_calls ++
    [LiveTabList (length edge_values)] ++
    map LiveTabSet set_calls ++ map LiveTabElements element_calls).

(** Database membership uses the actual tuple encoder, predicate lookup and set lookup. *)
Definition audit_live_tab_db_holds {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (db : database pred) (n : N) (x : V) : bool * list (audit_live_tab_event N E V B) :=
  let '(nc, nb) := sl_node_encode cb n in let '(xc, xb) := sl_value_encode cb x in
  let '(found, db_calls) := audit_map_get (fun p : pred => (encode pred_encoding p, [])) PLive db in
  let tuples := match found with
  Some s => s
  | None => FinSet.empty
  end in
  let '(answer, tuple_calls) := audit_finset_mem (audit_list_encode audit_positive_encode) [nc; xc]
    tuples in
  (answer, LiveTabNode n nc nb :: LiveTabValue x xc xb :: map LiveTabDb db_calls ++
    map LiveTabTuple tuple_calls).

Fixpoint audit_live_tab_filter_db {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (db : database pred) (n : N) (values : list V) : list V * list (audit_live_tab_event N E V B) :=
  match values with
  | [] => ([], [LiveTabCase 2])
  | x :: rest => let '(keep, calls) := audit_live_tab_db_holds cb db n x in
    let '(later, events) := audit_live_tab_filter_db cb db n rest in
    (if keep then x :: later else later, calls ++ events)
  end.

Fixpoint audit_live_tab_filter_set {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (set : FinSet.t V) (values : list V) : list V * list (audit_live_tab_event N E V B) :=
  match values with
  | [] => ([], [LiveTabCase 3])
  | x :: rest => let '(keep, calls) := audit_finset_mem (sl_value_encode cb) x set in
    let '(later, events) := audit_live_tab_filter_set cb set rest in
    (if keep then x :: later else later, map LiveTabSet calls ++ events)
  end.

(** The clamp uses the first universe and the database filter uses the second. *)
Definition audit_live_tab_node {N E V B} (g : Graph.t N E)
    (cb : audit_live_sparse_callbacks N E V B)
    (db : database pred) (n : N) : FinSet.t V * list (audit_live_tab_event N E V B) :=
  let '(universe, first) := audit_live_tab_universe g cb in
  let '(universe2, second) := audit_live_tab_universe g cb in
  let '(selected, selected_calls) := audit_live_tab_filter_db cb db n universe2 in
  let '(selected_set, set_calls) := audit_finset_of_list (sl_value_encode cb) selected in
  let '(clamped, clamp_calls) := audit_live_tab_filter_set cb selected_set universe in
  let '(result, result_calls) := audit_finset_of_list (sl_value_encode cb) clamped in
  (result, first ++ second ++ selected_calls ++ map LiveTabSet set_calls ++ clamp_calls ++
    map LiveTabSet result_calls).

Fixpoint audit_live_tab_nodes {N E V B} (g : Graph.t N E) (cb : audit_live_sparse_callbacks N E V B)
    (db : database pred) (nodes : list N) :
    Map.t N (FinSet.t V) * list (audit_live_tab_event N E V B) :=
  match nodes with
  | [] => (Map.empty, [LiveTabCase 4])
  | n :: rest => let '(later, calls) := audit_live_tab_nodes g cb db rest in
    let '(set, node_calls) := audit_live_tab_node g cb db n in
    let '(result, writes) := audit_map_set (sl_node_encode cb) n set later in
    (result, calls ++ node_calls ++ map LiveTabRows writes)
  end.

Definition audit_live_tab_probe {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (rows : Map.t N (FinSet.t V)) (n : N) (x : V) : bool * list (audit_live_tab_event N E V B) :=
  let '(found, reads) := audit_map_get (sl_node_encode cb) n rows in
  let set := match found with
  Some s => s
  | None => FinSet.empty
  end in
  let '(answer, tests) := audit_finset_mem (sl_value_encode cb) x set in
  (answer, map LiveTabRows reads ++ map LiveTabSet tests).

(** Event work expands tuple encoding and collection operations at their actual operands. *)
Definition audit_live_tab_event_work {N E V B} (weight : B -> nat)
    (event : audit_live_tab_event N E V B) : nat :=
  let body := fun xs => fold_right (fun item total => weight item + total) 0 xs in
  64 + match event with
  | LiveTabCase _ => 0
  | LiveTabList size => size
  | LiveTabSparse inner => audit_live_sparse_event_work weight inner
  | LiveTabSet call => audit_finset_source_work body [call]
  | LiveTabElements call => audit_set_elements_work [call]
  | LiveTabRows call => audit_map_source_work body [call]
  | LiveTabDb call => audit_map_source_work (fun _ => 0) [call]
  | LiveTabTuple call => audit_finset_source_work (audit_list_events_work audit_basic_encoding_work)
    [call]
  | LiveTabNode _ _ xs | LiveTabValue _ _ xs => body xs
  end.

Definition audit_live_tab_work {N E V B} (weight : B -> nat)
    (events : list (audit_live_tab_event N E V B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event total => audit_live_tab_event_work weight event + total) 0 events.

(** Callback allowances follow each original input retained in the same trace. *)
Definition audit_live_tab_event_budget {N E V B} (node_budget out_budget exit_budget : N -> nat)
    (edge_budget source_budget def_budget use_budget : E -> nat) (value_budget : V -> nat)
    (event : audit_live_tab_event N E V B) : nat :=
  match event with
  | LiveTabSparse call => audit_live_sparse_event_budget node_budget out_budget exit_budget
    edge_budget source_budget def_budget use_budget value_budget call
  | LiveTabSet (AuditSetMem x _ _ _ _ _) | LiveTabSet (AuditSetAdd x _ _ _ _ _) |
    LiveTabSet (AuditSetRemove x _ _ _ _ _) => value_budget x
  | LiveTabRows (AuditMapGet n _ _ _ _ _) | LiveTabRows (AuditMapSet n _ _ _ _ _ _) |
    LiveTabRows (AuditMapRemove n _ _ _ _ _) | LiveTabNode n _ _ => node_budget n
  | LiveTabValue x _ _ => value_budget x
  | _ => 0
  end.

(** Database dimensions use the actual stored relation tries, not a returned-work total. *)
Definition audit_live_tab_input_scale {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) (db : database pred) (n : N) (x : V) : nat :=
  let relations := map snd (Map.elements db) in
  let dimensions := fold_right (fun rel total =>
    audit_trie_nodes rel + audit_trie_output_bits rel + total) 0 relations in
  Nat.succ (audit_live_sparse_input_scale EN EE EV (var_point_uses vv) + Pos.size_nat (encode EN
    n) +
    Pos.size_nat (encode EV x) + audit_trie_nodes db + audit_trie_output_bits db + dimensions).

Definition audit_live_tab_input_budget {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) (db : database pred) (n : N) (x : V) : nat :=
  (N.to_nat 1048576%N) * Nat.pow (audit_live_tab_input_scale EN EE EV vv db n x) 64.

(** Under callback laws, tabulation and lookup agree with the database and obey the work bound. *)
Definition audit_live_tab_adapted_statement : Prop :=
  forall S O N E V C B (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (vv : var_view S O N E V C) (cb : audit_live_sparse_callbacks N E V B) (db : database pred)
    n x (weight : B -> nat) node_source value_source out_source use_source def_source exit_source
    node_budget value_budget out_budget use_budget def_budget exit_budget,
    audit_live_sparse_callbacks_erase EN EE EV (var_point_uses vv) cb ->
    audit_graph_external_callback_adapter (sl_node_encode cb) weight node_source node_budget ->
    audit_graph_external_callback_adapter (sl_value_encode cb) weight value_source value_budget ->
    audit_graph_external_callback_adapter (sl_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (sl_use cb) weight use_source use_budget ->
    audit_graph_external_callback_adapter (sl_def cb) weight def_source def_budget ->
    audit_graph_external_callback_adapter (sl_exit cb) weight exit_source exit_budget ->
    let g := cfg (gview vv) in
    let '(rows, build_events) := audit_live_tab_nodes g cb db (Graph.nodes g) in
    let '(answer, query_events) := audit_live_tab_probe cb rows n x in
    let expected := fold_right (fun v m => Map.set EN v (proj1_sig (live_of_db EN EV vv db v)) m)
      Map.empty (Graph.nodes g) in
    rows = expected /\ answer = FinSet.mem EV x (live_index_get EN n expected) /\
      audit_live_tab_work weight build_events + audit_live_tab_work weight query_events <=
        audit_live_tab_input_budget EN EE EV vv db n x +
        fold_right (fun event total => audit_live_tab_event_budget node_budget out_budget
          exit_budget
          (fun _ => 0) (fun _ => 0) def_budget use_budget value_budget event + total)
          0 (build_events ++ query_events).
