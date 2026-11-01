(** * One-shot liveness source callbacks

    The surviving graph filters each outgoing edge using the original definition callback.
    For example, a defining edge is omitted while every definition occurrence is scanned.
    Builds on: graph source models and SSA one-shot liveness. *)
From Stdlib Require Import List Bool PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditCompare
  CollectionsAuditPrimitive.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase GraphAuditDfs.
From Galois.Views Require Import ViewsGraph ViewsSsaPoints.
From Galois.Analyses Require Import AnalysesLiveness AnalysesAuditSsaQueryBase.
Import List.ListNotations.

(** * One-shot liveness source callbacks *)

(** Only supplied graph, point-use and encoding operations carry external bodies. *)
Record audit_live_one_callbacks (N E V B : Type) : Type := AuditLiveOneCallbacks {
  live_one_node_encode : N -> positive * list B;
  live_one_value_encode : V -> positive * list B;
  live_one_out : N -> list E * list B;
  live_one_target : E -> N * list B;
  live_one_def : E -> list V * list B;
  live_one_exit : N -> list V * list B;
  live_one_use : E -> list V * list B
}.

Arguments live_one_node_encode {N E V B} _ _.

Arguments live_one_value_encode {N E V B} _ _.

Arguments live_one_out {N E V B} _ _.

Arguments live_one_target {N E V B} _ _.

Arguments live_one_def {N E V B} _ _.

Arguments live_one_exit {N E V B} _ _.

Arguments live_one_use {N E V B} _ _.

(** Events retain exact original callback inputs, outputs and body receipts. *)
Inductive audit_live_one_event (N E V B : Type) : Type :=
  | LiveOneCase : nat -> audit_live_one_event N E V B
  | LiveOneNode : N -> positive -> list B -> audit_live_one_event N E V B
  | LiveOneValue : V -> positive -> list B -> audit_live_one_event N E V B
  | LiveOneOut : N -> list E -> list B -> audit_live_one_event N E V B
  | LiveOneTarget : E -> N -> list B -> audit_live_one_event N E V B
  | LiveOneDef : E -> list V -> list B -> audit_live_one_event N E V B
  | LiveOneExit : N -> list V -> list B -> audit_live_one_event N E V B
  | LiveOneUse : E -> list V -> list B -> audit_live_one_event N E V B
  | LiveOneEqual : list audit_positive_eqb_event -> audit_live_one_event N E V B.

Arguments LiveOneCase {N E V B} _.

Arguments LiveOneNode {N E V B} _ _ _.

Arguments LiveOneValue {N E V B} _ _ _.

Arguments LiveOneOut {N E V B} _ _ _.

Arguments LiveOneTarget {N E V B} _ _ _.

Arguments LiveOneDef {N E V B} _ _ _.

Arguments LiveOneExit {N E V B} _ _ _.

Arguments LiveOneUse {N E V B} _ _ _.

Arguments LiveOneEqual {N E V B} _.

(** The modeled scan retains comparisons for every occurrence, even after a match. *)
Fixpoint audit_live_one_has {N E V B} (cb : audit_live_one_callbacks N E V B)
    (x : V) (xs : list V) : bool * list (audit_live_one_event N E V B) :=
  match xs with
  | [] => (false, [LiveOneCase 0])
  | y :: rest =>
    let '(a, ac) := live_one_value_encode cb x in
    let '(b, bc) := live_one_value_encode cb y in
    let '(same, equal) := audit_positive_eqb a b in
    let '(later, events) := audit_live_one_has cb x rest in
    (same || later, LiveOneValue x a ac :: LiveOneValue y b bc :: LiveOneEqual equal :: events)
  end.

(** Filtering evaluates every defining-edge predicate and preserves edge order. *)
Fixpoint audit_live_one_filter {N E V B} (cb : audit_live_one_callbacks N E V B)
    (x : V) (edges : list E) : list E * list (audit_live_one_event N E V B) :=
  match edges with
  | [] => ([], [LiveOneCase 1])
  | e :: rest =>
    let '(defs, body) := live_one_def cb e in
    let '(defined, calls) := audit_live_one_has cb x defs in
    let '(later, events) := audit_live_one_filter cb x rest in
    (if defined then later else e :: later, LiveOneDef e defs body :: calls ++ events)
  end.

Definition audit_live_one_surviving_out {N E V B} (cb : audit_live_one_callbacks N E V B)
    (x : V) (n : N) : list E * list (audit_live_one_event N E V B) :=
  let '(edges, body) := live_one_out cb n in
  let '(kept, calls) := audit_live_one_filter cb x edges in
  (kept, LiveOneOut n edges body :: calls).

Fixpoint audit_live_one_edge_uses {N E V B} (cb : audit_live_one_callbacks N E V B)
    (x : V) (edges : list E) : bool * list (audit_live_one_event N E V B) :=
  match edges with
  | [] => (false, [LiveOneCase 2])
  | e :: rest =>
    let '(uses, body) := live_one_use cb e in
    let '(here, calls) := audit_live_one_has cb x uses in
    let '(later, events) := audit_live_one_edge_uses cb x rest in
    (here || later, LiveOneUse e uses body :: calls ++ events)
  end.

Definition audit_live_one_use_at {N E V B} (cb : audit_live_one_callbacks N E V B)
    (x : V) (n : N) : bool * list (audit_live_one_event N E V B) :=
  let '(uses, body) := live_one_exit cb n in
  let '(here, calls) := audit_live_one_has cb x uses in
  let '(edges, out_body) := live_one_out cb n in
  let '(later, events) := audit_live_one_edge_uses cb x edges in
  (here || later, LiveOneExit n uses body :: calls ++ LiveOneOut n edges out_body :: events).

Fixpoint audit_live_one_search_uses {N E V B} (cb : audit_live_one_callbacks N E V B)
    (x : V) (nodes : list N) : bool * list (audit_live_one_event N E V B) :=
  match nodes with
  | [] => (false, [LiveOneCase 3])
  | n :: rest => let '(here, calls) := audit_live_one_use_at cb x n in
    let '(later, events) := audit_live_one_search_uses cb x rest in
    (here || later, calls ++ events)
  end.

(** Wrappers preserve the genuine node and edge callback bodies. *)
Definition audit_live_one_node {N E V B} (cb : audit_live_one_callbacks N E V B) (n : N)
    : positive * list (audit_live_one_event N E V B) :=
  let '(code, body) := live_one_node_encode cb n in (code, [LiveOneNode n code body]).

Definition audit_live_one_target {N E V B} (cb : audit_live_one_callbacks N E V B) (e : E)
    : N * list (audit_live_one_event N E V B) :=
  let '(n, body) := live_one_target cb e in (n, [LiveOneTarget e n body]).

(** The source model prepares and searches the same filtered graph once. *)
Definition audit_live_one_counted {N E V B} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) (cb : audit_live_one_callbacks N E V B) (n : N) (x : V) :=
  let g := audit_live_surviving_graph EV p x in
  let prep_cb := AuditPrepareCallbackModel N E (audit_live_one_event N E V B)
    (audit_live_one_surviving_out cb x) (audit_live_one_target cb) (audit_live_one_node cb) in
  let dfs_cb := AuditDfsCallbackModel N E (audit_live_one_event N E V B)
    (audit_live_one_target cb) (audit_live_one_node cb) in
  let '(prepared, prep_events) := audit_prepare_source_counted EN g prep_cb in
  let '(search, dfs_events) := audit_dfs_source_counted prepared dfs_cb FinSet.empty [n] in
  let '(answer, use_events) := audit_live_one_search_uses cb x (preorder search) in
  (answer, (prep_events, dfs_events, use_events)).

(** Every internal equality frame and actual supplied body is charged. *)
Definition audit_live_one_event_work {N E V B} (weight : B -> nat)
    (event : audit_live_one_event N E V B) : nat :=
  let body := fun xs => fold_right (fun item total => weight item + total) 0 xs in
  64 + match event with
  | LiveOneNode _ _ xs | LiveOneValue _ _ xs | LiveOneOut _ _ xs | LiveOneTarget _ _ xs |
    LiveOneDef _ _ xs | LiveOneExit _ _ xs | LiveOneUse _ _ xs => body xs
  | LiveOneEqual calls => audit_positive_eqb_source_work calls
  | LiveOneCase _ => 0
  end.

(** Each external allowance refers to the input of the actual captured invocation. *)
Definition audit_live_one_event_budget {N E V B} (node_budget out_budget exit_budget : N -> nat)
    (value_budget : V -> nat) (target_budget def_budget use_budget : E -> nat)
    (event : audit_live_one_event N E V B) : nat :=
  match event with
  | LiveOneNode n _ _ => node_budget n
  | LiveOneValue v _ _ => value_budget v
  | LiveOneOut n _ _ => out_budget n
  | LiveOneTarget e _ _ => target_budget e
  | LiveOneDef e _ _ => def_budget e
  | LiveOneExit n _ _ => exit_budget n
  | LiveOneUse e _ _ => use_budget e
  | _ => 0
  end.

(** The input support includes listed vertices and the endpoints DFS may visit. *)
Definition audit_live_one_input_scale {N E V} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) (n : N) (x : V) : nat :=
  let g := live_graph p in
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let nodes := n :: Graph.nodes g ++ Graph.entries g ++ map (Graph.target g) edges in
  let use_edges := flat_map (Graph.out g) nodes in
  let values := x :: flat_map (exit_use p) nodes ++ flat_map (edge_def p) edges ++
    flat_map (edge_use p) use_edges in
  let nw := fold_right (fun node total => Pos.size_nat (encode EN node) + total) 0 nodes in
  let vw := fold_right (fun value total => Pos.size_nat (encode EV value) + total) 0 values in
  let filtered := audit_live_surviving_graph EV p x in
  S (length nodes + length edges + length use_edges + length values + nw + vw +
    audit_prepare_source_budget EN filtered +
    audit_dfs_source_budget EN filtered (prepare EN filtered) [n]).

(** The one-shot allowance is determined by the original point-use input. *)
Definition audit_live_one_input_budget {N E V} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) (n : N) (x : V) : nat :=
  (N.to_nat 1048576%N) * Nat.pow (audit_live_one_input_scale EN EV p n x) 64.

(** Erasure fixes each callback to the matching point-use or graph operation. *)
Definition audit_live_one_callbacks_erase {N E V B} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) (cb : audit_live_one_callbacks N E V B) : Prop :=
  (forall n, fst (live_one_node_encode cb n) = encode EN n) /\
  (forall v, fst (live_one_value_encode cb v) = encode EV v) /\
  (forall n, fst (live_one_out cb n) = Graph.out (live_graph p) n) /\
  (forall e, fst (live_one_target cb e) = Graph.target (live_graph p) e) /\
  (forall e, fst (live_one_def cb e) = edge_def p e) /\
  (forall n, fst (live_one_exit cb n) = exit_use p n) /\
  (forall e, fst (live_one_use cb e) = edge_use p e).

(** Under callback laws, one-shot search returns the source answer within its adapted work bound. *)
Definition audit_live_one_source_adapted_statement : Prop :=
  forall N E V B (EN : encoding N) (EV : encoding V) (p : point_uses N E V)
    (cb : audit_live_one_callbacks N E V B) n x (weight : B -> nat)
    node_source value_source out_source target_source def_source exit_source use_source
    node_budget value_budget out_budget target_budget def_budget exit_budget use_budget,
    audit_live_one_callbacks_erase EN EV p cb ->
    audit_graph_external_callback_adapter (live_one_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (live_one_value_encode cb) weight value_source
      value_budget ->
    audit_graph_external_callback_adapter (live_one_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (live_one_target cb) weight target_source target_budget ->
    audit_graph_external_callback_adapter (live_one_def cb) weight def_source def_budget ->
    audit_graph_external_callback_adapter (live_one_exit cb) weight exit_source exit_budget ->
    audit_graph_external_callback_adapter (live_one_use cb) weight use_source use_budget ->
    let '(answer, (prep_events, dfs_events, use_events)) := audit_live_one_counted EN EV p cb n x in
    let event_work := audit_live_one_event_work weight in
    let event_budget := audit_live_one_event_budget node_budget out_budget exit_budget value_budget
      target_budget def_budget use_budget in
    let work := audit_prepare_source_work event_work prep_events +
      audit_dfs_source_work event_work dfs_events + 256 * Nat.pow (S (length use_events)) 3 +
      fold_right (fun event total => event_work event + total) 0 use_events in
    let external := audit_prepare_source_body_work event_budget prep_events +
      audit_dfs_source_body_work event_budget dfs_events +
      fold_right (fun event total => event_budget event + total) 0 use_events in
    answer = audit_live_one_shot EN EV p n x /\ work <= audit_live_one_input_budget EN EV p n x +
      external.
