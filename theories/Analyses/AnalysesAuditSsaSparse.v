(** * Sparse liveness materialization source

    The source follows seed insertion and binary-fuel backward propagation.
    For example, an already present node/value pair is not scheduled again.
    Builds on: collection source models, graph preparation and point-use views. *)
From Stdlib Require Import List Bool PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditEncoding CollectionsAuditNAdd.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Views Require Import ViewsGraph ViewsSsaPoints.
From Galois.Analyses Require Import AnalysesLiveness AnalysesSsaLiveQuery AnalysesSsaLiveSets.
Import List.ListNotations.

(** * Sparse liveness materialization source *)

(** The sparse producer records each graph, use and encoding callback with its source body. *)
Record audit_live_sparse_callbacks (N E V B : Type) : Type := AuditLiveSparseCallbacks {
  sl_node_encode : N -> positive * list B;
  sl_edge_encode : E -> positive * list B;
  sl_value_encode : V -> positive * list B;
  sl_out : N -> list E * list B;
  sl_target : E -> N * list B;
  sl_source : E -> N * list B;
  sl_def : E -> list V * list B;
  sl_exit : N -> list V * list B;
  sl_use : E -> list V * list B
}.

Arguments sl_node_encode {N E V B} _ _.

Arguments sl_edge_encode {N E V B} _ _.

Arguments sl_value_encode {N E V B} _ _.

Arguments sl_out {N E V B} _ _.

Arguments sl_target {N E V B} _ _.

Arguments sl_source {N E V B} _ _.

Arguments sl_def {N E V B} _ _.

Arguments sl_exit {N E V B} _ _.

Arguments sl_use {N E V B} _ _.

Inductive audit_live_sparse_event (N E V B : Type) : Type :=
  | SlCase : nat -> audit_live_sparse_event N E V B
  | SlList : nat -> audit_live_sparse_event N E V B
  | SlOut : N -> list E -> list B -> audit_live_sparse_event N E V B
  | SlSource : E -> N -> list B -> audit_live_sparse_event N E V B
  | SlDef : E -> list V -> list B -> audit_live_sparse_event N E V B
  | SlExit : N -> list V -> list B -> audit_live_sparse_event N E V B
  | SlUse : E -> list V -> list B -> audit_live_sparse_event N E V B
  | SlPred : audit_map_event N (list E) B -> audit_live_sparse_event N E V B
  | SlRows : audit_map_event N (FinSet.t V) B -> audit_live_sparse_event N E V B
  | SlDefs : audit_map_event E (FinSet.t V) B -> audit_live_sparse_event N E V B
  | SlSet : audit_set_event V B -> audit_live_sparse_event N E V B
  | SlEncodeNat : audit_nat_encoding_event -> audit_live_sparse_event N E V B
  | SlMultiply : positive -> positive -> audit_live_sparse_event N E V B
  | SlAdd : audit_idf_nadd_event -> audit_live_sparse_event N E V B.

Arguments SlCase {N E V B} _.

Arguments SlList {N E V B} _.

Arguments SlOut {N E V B} _ _ _.

Arguments SlSource {N E V B} _ _ _.

Arguments SlDef {N E V B} _ _ _.

Arguments SlExit {N E V B} _ _ _.

Arguments SlUse {N E V B} _ _ _.

Arguments SlPred {N E V B} _.

Arguments SlRows {N E V B} _.

Arguments SlDefs {N E V B} _.

Arguments SlSet {N E V B} _.

Arguments SlEncodeNat {N E V B} _.

Arguments SlMultiply {N E V B} _ _.

Arguments SlAdd {N E V B} _.

(** Binary multiplication records each recursive bit and the actual addition body. *)
Fixpoint audit_live_sparse_mul {N E V B} (a b : positive)
    : positive * list (audit_live_sparse_event N E V B) :=
  match a with
  | xH => (b, [SlMultiply a b])
  | xO rest => let '(result, calls) := audit_live_sparse_mul rest b in
    (xO result, SlMultiply a b :: calls)
  | xI rest => let '(result, calls) := audit_live_sparse_mul rest b in
    let '(sum, adds) := audit_idf_positive_add false b (xO result) in
    (sum, SlMultiply a b :: calls ++ map SlAdd adds)
  end.

(** The binary fuel product preserves its value and has an operand-width frame bound. *)
Definition audit_live_sparse_mul_statement : Prop :=
  forall N E V B a b,
    let '(result, events) := audit_live_sparse_mul (N := N) (E := E) (V := V) (B := B) a b in
    result = Pos.mul a b /\
    length events <= 16 * Nat.pow (S (Pos.size_nat a + Pos.size_nat b)) 3.

Fixpoint audit_live_sparse_edges {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (nodes : list N) : list E * list (audit_live_sparse_event N E V B) :=
  match nodes with
  | [] => ([], [SlCase 0])
  | n :: rest => let '(edges, body) := sl_out cb n in
    let '(later, calls) := audit_live_sparse_edges cb rest in
    (edges ++ later, SlOut n edges body :: calls ++ [SlList (length edges)])
  end.

Fixpoint audit_live_sparse_uses {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (edges : list E) : list V * list (audit_live_sparse_event N E V B) :=
  match edges with
  | [] => ([], [SlCase 1])
  | e :: rest => let '(values, body) := sl_use cb e in
    let '(later, calls) := audit_live_sparse_uses cb rest in
    (values ++ later, SlUse e values body :: calls ++ [SlList (length values)])
  end.

Fixpoint audit_live_sparse_seeds {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (nodes : list N) : list (N * V) * list (audit_live_sparse_event N E V B) :=
  match nodes with
  | [] => ([], [SlCase 2])
  | n :: rest =>
    let '(exit_values, exit_body) := sl_exit cb n in
    let '(edges, out_body) := sl_out cb n in
    let '(edge_values, use_calls) := audit_live_sparse_uses cb edges in
    let values := exit_values ++ edge_values in
    let '(later, calls) := audit_live_sparse_seeds cb rest in
    (map (fun v => (n, v)) values ++ later,
      SlExit n exit_values exit_body :: SlOut n edges out_body :: use_calls ++
      [SlList (length exit_values); SlList (length values)] ++ calls ++ [SlList (length values)])
  end.

Fixpoint audit_live_sparse_defs {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (edges : list E) : Map.t E (FinSet.t V) * list (audit_live_sparse_event N E V B) :=
  match edges with
  | [] => (Map.empty, [SlCase 3])
  | e :: rest => let '(later, calls) := audit_live_sparse_defs cb rest in
    let '(values, body) := sl_def cb e in
    let '(set, set_calls) := audit_finset_of_list (sl_value_encode cb) values in
    let '(result, writes) := audit_map_set (sl_edge_encode cb) e set later in
    (result, calls ++ SlDef e values body :: map SlSet set_calls ++ map SlDefs writes)
  end.

(** The worklist state pairs materialized node rows with pending node-value pairs. *)
Definition audit_live_sparse_state N V := (Map.t N (FinSet.t V) * list (N * V))%type.

(** A miss repeats the source lookup before inserting and scheduling the pair. *)
Definition audit_live_sparse_add {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (state : audit_live_sparse_state N V) (q : N * V)
    : audit_live_sparse_state N V * list (audit_live_sparse_event N E V B) :=
  let '(n, x) := q in
  let '(found, reads) := audit_map_get (sl_node_encode cb) n (fst state) in
  let set := match found with
  Some s => s
  | None => FinSet.empty
  end in
  let '(present, tests) := audit_finset_mem (sl_value_encode cb) x set in
  if present then (state, map SlRows reads ++ map SlSet tests ++ [SlCase 4])
  else let '(found2, reads2) := audit_map_get (sl_node_encode cb) n (fst state) in
    let set2 := match found2 with
    Some s => s
    | None => FinSet.empty
    end in
    let '(updated, adds) := audit_finset_add (sl_value_encode cb) x set2 in
    let '(rows, writes) := audit_map_set (sl_node_encode cb) n updated (fst state) in
    ((rows, q :: snd state), map SlRows reads ++ map SlSet tests ++ map SlRows reads2 ++
      map SlSet adds ++ map SlRows writes).

Fixpoint audit_live_sparse_adds {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (qs : list (N * V)) (state : audit_live_sparse_state N V)
    : audit_live_sparse_state N V * list (audit_live_sparse_event N E V B) :=
  match qs with
  | [] => (state, [SlCase 5])
  | q :: rest => let '(next, here) := audit_live_sparse_add cb state q in
    let '(result, calls) := audit_live_sparse_adds cb rest next in (result, here ++ calls)
  end.

(** The filter tests every predecessor before the source-map phase starts. *)
Fixpoint audit_live_sparse_filter_edges {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (defs : Map.t E (FinSet.t V)) (x : V) (edges : list E)
    : list E * list (audit_live_sparse_event N E V B) :=
  match edges with
  | [] => ([], [SlCase 6])
  | e :: rest => let '(found, reads) := audit_map_get (sl_edge_encode cb) e defs in
    let set := match found with
    Some s => s
    | None => FinSet.empty
    end in
    let '(killed, tests) := audit_finset_mem (sl_value_encode cb) x set in
    let '(later, calls) := audit_live_sparse_filter_edges cb defs x rest in
    if killed then (later, map SlDefs reads ++ map SlSet tests ++ calls)
    else (e :: later, map SlDefs reads ++ map SlSet tests ++ calls)
  end.

(** The source-map phase visits the filtered edges in their original order. *)
Fixpoint audit_live_sparse_back_sources {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (x : V) (edges : list E) : list (N * V) * list (audit_live_sparse_event N E V B) :=
  match edges with
  | [] => ([], [SlCase 11])
  | e :: rest =>
    let '(src, body) := sl_source cb e in
    let '(later, calls) := audit_live_sparse_back_sources cb x rest in
    ((src, x) :: later, SlSource e src body :: calls)
  end.

Definition audit_live_sparse_step {N E V B} {EN : encoding N} {g : Graph.t N E}
    (cb : audit_live_sparse_callbacks N E V B) (p : prepared EN g) (defs : Map.t E (FinSet.t V))
    (state : audit_live_sparse_state N V) :
    audit_live_sparse_state N V * list (audit_live_sparse_event N E V B) :=
  match snd state with
  | [] => (state, [SlCase 7])
  | (n, x) :: rest =>
    let '(found, reads) := audit_map_get (sl_node_encode cb) n (in_index p) in
    let edges := match found with
    Some es => es
    | None => []
    end in
    let '(kept, filter_calls) := audit_live_sparse_filter_edges cb defs x edges in
    let '(next, back_calls) := audit_live_sparse_back_sources cb x kept in
    let '(result, calls) := audit_live_sparse_adds cb next (fst state, rest) in
    (result, map SlPred reads ++ filter_calls ++ back_calls ++ calls)
  end.

Fixpoint audit_live_sparse_run {N E V B} {EN : encoding N} {g : Graph.t N E}
    (cb : audit_live_sparse_callbacks N E V B) (p : prepared EN g) (defs : Map.t E (FinSet.t V))
    (fuel : positive) (state : audit_live_sparse_state N V)
    : audit_live_sparse_state N V * list (audit_live_sparse_event N E V B) :=
  match snd state with
  | [] => (state, [SlCase 8])
  | _ :: _ => match fuel with
    | xH => audit_live_sparse_step cb p defs state
    | xO k => let '(middle, first) := audit_live_sparse_run cb p defs k state in
      let '(result, second) := audit_live_sparse_run cb p defs k middle in
      (result, SlCase 9 :: first ++ second)
    | xI k => let '(middle, first) := audit_live_sparse_run cb p defs k state in
      let '(before, second) := audit_live_sparse_run cb p defs k middle in
      let '(result, last) := audit_live_sparse_step cb p defs before in
      (result, SlCase 10 :: first ++ second ++ last)
    end
  end.

(** Materialization binds one preparation, two input traversals and one worklist run. *)
Definition audit_live_sparse_counted {N E V B} (EN : encoding N) (p : point_uses N E V)
    (cb : audit_live_sparse_callbacks N E V B) :=
  let g := live_graph p in
  let prep_cb := AuditPrepareCallbackModel N E B (sl_out cb) (sl_target cb) (sl_node_encode cb) in
  let '(prepared, prep_events) := audit_prepare_source_counted EN g prep_cb in
  let '(edges, edge_calls) := audit_live_sparse_edges cb (Graph.nodes g) in
  let '(defs, def_calls) := audit_live_sparse_defs cb edges in
  let '(seeds, seed_calls) := audit_live_sparse_seeds cb (Graph.nodes g) in
  let '(initial, initial_calls) := audit_live_sparse_adds cb seeds (Map.empty, []) in
  let '(a, ac) := audit_nat_encode (length (Graph.nodes g)) in
  let '(b, bc) := audit_nat_encode (length seeds) in
  let '(fuel, mul_calls) := audit_live_sparse_mul a b in
  let '(result, run_calls) := audit_live_sparse_run cb prepared defs fuel initial in
  (fst result, (prep_events, edge_calls ++ def_calls ++ seed_calls ++ initial_calls ++
    map SlEncodeNat ac ++ map SlEncodeNat bc ++ mul_calls ++ run_calls)).

(** Event work includes trie paths, arithmetic frames and actual callback bodies. *)
Definition audit_live_sparse_event_work {N E V B} (weight : B -> nat)
    (event : audit_live_sparse_event N E V B) : nat :=
  let body := fun xs => fold_right (fun item total => weight item + total) 0 xs in
  64 + match event with
  | SlOut _ _ xs | SlSource _ _ xs | SlDef _ _ xs | SlExit _ _ xs | SlUse _ _ xs => body xs
  | SlPred call => audit_map_source_work body [call]
  | SlRows call => audit_map_source_work body [call]
  | SlDefs call => audit_map_source_work body [call]
  | SlSet call => audit_finset_source_work body [call]
  | SlList length => length
  | _ => 0
  end.

Definition audit_live_sparse_work {N E V B} (weight : B -> nat)
    (events : list (audit_live_sparse_event N E V B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event total => audit_live_sparse_event_work weight event + total) 0 events.

(** Actual operands select the corresponding supplied callback allowance. *)
Definition audit_live_sparse_event_budget {N E V B} (node_budget out_budget exit_budget : N -> nat)
    (edge_budget source_budget def_budget use_budget : E -> nat) (value_budget : V -> nat)
    (event : audit_live_sparse_event N E V B) : nat :=
  match event with
  | SlOut n _ _ => out_budget n
  | SlExit n _ _ => exit_budget n
  | SlSource e _ _ => source_budget e
  | SlDef e _ _ => def_budget e
  | SlUse e _ _ => use_budget e
  | SlPred (AuditMapGet n _ _ _ _ _) | SlPred (AuditMapSet n _ _ _ _ _ _) |
    SlPred (AuditMapRemove n _ _ _ _ _) | SlRows (AuditMapGet n _ _ _ _ _) |
    SlRows (AuditMapSet n _ _ _ _ _ _) | SlRows (AuditMapRemove n _ _ _ _ _) => node_budget n
  | SlDefs (AuditMapGet e _ _ _ _ _) | SlDefs (AuditMapSet e _ _ _ _ _ _) |
    SlDefs (AuditMapRemove e _ _ _ _ _) => edge_budget e
  | SlSet (AuditSetMem x _ _ _ _ _) | SlSet (AuditSetAdd x _ _ _ _ _) |
    SlSet (AuditSetRemove x _ _ _ _ _) => value_budget x
  | _ => 0
  end.

(** Original nodes, edge occurrences and values bound all reachable worklist operands. *)
Definition audit_live_sparse_input_scale {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) : nat :=
  let g := live_graph p in
  let edges := edges_of g in
  let nodes := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++
    map (Graph.target g) edges in
  let values := flat_map (exit_use p) (Graph.nodes g) ++ flat_map (edge_use p) edges ++
    flat_map (edge_def p) edges in
  let nw := fold_right (fun x total => Pos.size_nat (encode EN x) + total) 0 nodes in
  let ew := fold_right (fun x total => Pos.size_nat (encode EE x) + total) 0 edges in
  let vw := fold_right (fun x total => Pos.size_nat (encode EV x) + total) 0 values in
  S (length nodes + length edges + length values + nw + ew + vw + audit_prepare_source_budget EN g).

Definition audit_live_sparse_input_budget {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) : nat :=
  (N.to_nat 1048576%N) * Nat.pow (audit_live_sparse_input_scale EN EE EV p) 64.

(** Every supplied callback erases to its actual graph or point-use operation. *)
Definition audit_live_sparse_callbacks_erase {N E V B} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) (cb : audit_live_sparse_callbacks N E V B) : Prop :=
  (forall n, fst (sl_node_encode cb n) = encode EN n) /\
  (forall e, fst (sl_edge_encode cb e) = encode EE e) /\
  (forall x, fst (sl_value_encode cb x) = encode EV x) /\
  (forall n, fst (sl_out cb n) = Graph.out (live_graph p) n) /\
  (forall e, fst (sl_target cb e) = Graph.target (live_graph p) e) /\
  (forall e, fst (sl_source cb e) = Graph.source (live_graph p) e) /\
  (forall e, fst (sl_def cb e) = edge_def p e) /\
  (forall n, fst (sl_exit cb n) = exit_use p n) /\
  (forall e, fst (sl_use cb e) = edge_use p e).

(** Under callback laws, sparse materialization returns the source rows within both work bounds. *)
Definition audit_live_sparse_source_adapted_statement : Prop :=
  forall N E V B (EN : encoding N) (EE : encoding E) (EV : encoding V) (p : point_uses N E V)
    (cb : audit_live_sparse_callbacks N E V B) (weight : B -> nat)
    node_source edge_source value_source out_source target_source source_source def_source
    exit_source use_source
    node_budget edge_budget value_budget out_budget target_budget source_budget def_budget
    exit_budget use_budget,
    audit_live_sparse_callbacks_erase EN EE EV p cb ->
    audit_graph_external_callback_adapter (sl_node_encode cb) weight node_source node_budget ->
    audit_graph_external_callback_adapter (sl_edge_encode cb) weight edge_source edge_budget ->
    audit_graph_external_callback_adapter (sl_value_encode cb) weight value_source value_budget ->
    audit_graph_external_callback_adapter (sl_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (sl_target cb) weight target_source target_budget ->
    audit_graph_external_callback_adapter (sl_source cb) weight source_source source_budget ->
    audit_graph_external_callback_adapter (sl_def cb) weight def_source def_budget ->
    audit_graph_external_callback_adapter (sl_exit cb) weight exit_source exit_budget ->
    audit_graph_external_callback_adapter (sl_use cb) weight use_source use_budget ->
    let '(result, (prep_events, events)) := audit_live_sparse_counted EN p cb in
    let external := audit_prepare_source_body_work weight prep_events in
    let adapted := fold_right (fun event total => audit_live_sparse_event_budget node_budget
      out_budget exit_budget edge_budget source_budget def_budget use_budget value_budget event +
        total) 0
      events in
    result = sparse_live_materialize EN EE EV p /\
    audit_prepare_source_work weight prep_events + audit_live_sparse_work weight events <=
      audit_live_sparse_input_budget EN EE EV p + external + adapted /\
    audit_prepare_source_work weight prep_events + audit_live_sparse_work weight events <=
      audit_live_sparse_input_budget EN EE EV p +
      fold_right (fun event total => audit_prepare_source_event_budget node_budget out_budget
        target_budget event + total)
        0 prep_events + adapted.

(** An online lookup reads the actual materialized row and tests the requested value. *)
Definition audit_live_sparse_probe {N E V B} (cb : audit_live_sparse_callbacks N E V B)
    (rows : Map.t N (FinSet.t V)) (n : N) (x : V)
    : bool * list (audit_live_sparse_event N E V B) :=
  let '(found, reads) := audit_map_get (sl_node_encode cb) n rows in
  let set := match found with
  Some s => s
  | None => FinSet.empty
  end in
  let '(answer, tests) := audit_finset_mem (sl_value_encode cb) x set in
  (answer, map SlRows reads ++ map SlSet tests).

(** Lookup has an operand-width bound and retains both actual encoder calls. *)
Definition audit_live_sparse_probe_statement : Prop :=
  forall N E V B (EN : encoding N) (EV : encoding V) (cb : audit_live_sparse_callbacks N E V B)
    rows n x (weight : B -> nat) node_source value_source node_budget value_budget,
    (forall v, fst (sl_node_encode cb v) = encode EN v) ->
    (forall v, fst (sl_value_encode cb v) = encode EV v) ->
    audit_graph_external_callback_adapter (sl_node_encode cb) weight node_source node_budget ->
    audit_graph_external_callback_adapter (sl_value_encode cb) weight value_source value_budget ->
    let '(answer, events) := audit_live_sparse_probe cb rows n x in
    answer = sparse_live_at EN EV rows n x /\
    audit_live_sparse_work weight events <=
      4096 * Nat.pow (S (Pos.size_nat (encode EN n) + Pos.size_nat (encode EV x))) 4 +
      fold_right (fun event total => audit_live_sparse_event_budget node_budget (fun _ => 0)
        (fun _ => 0)
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) value_budget event + total) 0 events.
