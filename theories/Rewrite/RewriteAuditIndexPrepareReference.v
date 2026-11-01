(** * RewriteAuditIndexPrepareReference

    Models fresh-identifier selection and its graph-enumeration receipts.
    For example, empty root and node maps yield fresh identifier 2.
    Builds on: RewriteAuditIndexBuild and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBuild RewriteAuditIndexReference
  RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_ri_fresh_call (K Sort V : Type) : Type :=
  | RIFreshRoots : Map.t rw_id rw_id -> list (rw_id * rw_id) ->
      list (audit_elements_event (rw_id * rw_id)) -> rw_ri_fresh_call K Sort V
  | RIFreshNodes : Map.t rw_id (rw_id * rw_node K Sort V) ->
      list (rw_id * (rw_id * rw_node K Sort V)) ->
      list (audit_elements_event (rw_id * (rw_id * rw_node K Sort V))) -> rw_ri_fresh_call K Sort V
  | RIFreshMax : positive -> positive -> positive -> rw_ri_fresh_call K Sort V
  | RIFreshSucc : positive -> positive -> list audit_nat_encoding_event ->
      rw_ri_fresh_call K Sort V.
Arguments RIFreshRoots {K Sort V}.
Arguments RIFreshNodes {K Sort V}.
Arguments RIFreshMax {K Sort V}.
Arguments RIFreshSucc {K Sort V}.

Definition rw_ri_fresh_event_cost {K Sort V} (event : audit_event (rw_ri_fresh_call K Sort V)) : nat
    :=
  match event with
  | AuditCall (RIFreshRoots _ _ trace) => 1 + audit_elements_work trace
  | AuditCall (RIFreshNodes _ _ trace) => 1 + audit_elements_work trace
  | AuditCall (RIFreshMax key current _) => 4 + Pos.size_nat key + Pos.size_nat current
  | AuditCall (RIFreshSucc _ _ trace) => 1 + audit_nat_events_work trace
  | _ => 1
  end.

Definition rw_ri_fresh_trace_cost {K Sort V} (trace : audit_trace (rw_ri_fresh_call K Sort V)) : nat
    :=
  fold_right (fun event total => rw_ri_fresh_event_cost event + total) 0 trace.

Fixpoint rw_ri_max_entries_atomic {A K Sort V} (entries : list (positive * A)) (current : positive)
    : positive * audit_trace (rw_ri_fresh_call K Sort V) :=
  match entries with
  | nil => (current, [AuditCase 810 []])
  | (key, _) :: rest =>
    let next := Pos.max key current in
    let '(out, trace) := rw_ri_max_entries_atomic rest next in
    (out, [AuditCase 811 []; AuditCall (RIFreshMax key current next)] ++ trace)
  end.

Definition rw_ri_fresh_atomic {K Sort V} (g : rw_graph K Sort V) : positive * audit_trace
    (rw_ri_fresh_call K Sort V) :=
  let roots_map := rw_class_roots g in
  let '(roots, root_trace) := audit_map_elements roots_map in
  let nodes_map := rw_nodes g in
  let '(nodes, node_trace) := audit_map_elements nodes_map in
  let '(root_max, root_max_trace) := rw_ri_max_entries_atomic roots 1%positive in
  let '(all_max, node_max_trace) := rw_ri_max_entries_atomic nodes root_max in
  let '(fresh, succ_trace) := audit_positive_succ all_max in
  (fresh, [AuditCase 812 []; AuditCall (RIFreshRoots roots_map roots root_trace);
    AuditCase 813 []; AuditCall (RIFreshNodes nodes_map nodes node_trace)] ++
    root_max_trace ++ node_max_trace ++ [AuditCall (RIFreshSucc all_max fresh succ_trace)]).

Definition rw_ri_fresh_value {K Sort V} (g : rw_graph K Sort V) : positive :=
  let roots := Map.elements (rw_class_roots g) in
  let nodes := Map.elements (rw_nodes g) in
  let root_max := fold_left (fun acc entry => Pos.max (fst entry) acc) roots 1%positive in
  let all_max := fold_left (fun acc entry => Pos.max (fst entry) acc) nodes root_max in
  Pos.succ all_max.

Definition rw_index_build {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) : rw_index_state K Sort V :=
  let empty := RwRiBuildAcc Map.empty Map.empty Map.empty in
  let buckets := rw_ri_build_nodes_value EK EV g (rw_nodes_in g) empty in
  let dirty := FinSet.of_list positive_encoding (rw_nodes_in g) in
  let fresh := rw_ri_fresh_value g in
  RWIndexState g UnionFind.make (rw_ri_build_parents buckets) Map.empty Map.empty
    (rw_nodes_in g) dirty rw_pending_empty (rw_ri_build_ops buckets) (rw_ri_build_vars buckets)
    fresh.
