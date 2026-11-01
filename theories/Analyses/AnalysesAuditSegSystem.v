(** * SEG constraint-system source

    Generated constraints enumerate the captured sparse graph once.
    For example, each enumerated sparse edge produces one flow constraint.
    Builds on: graph preparation and SEG builder callbacks. *)
From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSeg AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder.
Import List.ListNotations.

(** * SEG constraint-system source *)

Inductive audit_seg_system_event (N E B : Type) : Type :=
  | SegSystemCase : nat -> audit_seg_system_event N E B
  | SegSystemGraph : audit_seg_graph_body N E B -> audit_seg_system_event N E B
  | SegSystemAppend : nat -> audit_seg_system_event N E B.

Arguments SegSystemCase {N E B} _.

Arguments SegSystemGraph {N E B} _.

Arguments SegSystemAppend {N E B} _.

Fixpoint audit_seg_system_edges {N E B} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (encn : N -> positive * list B) (work : seg_work N E) (nodes : list N)
    : list E * list (audit_seg_system_event N E B) :=
  match nodes with
  | [] => ([], [SegSystemCase 0])
  | n :: rest => let '(here, calls) := audit_seg_graph_out p encn work n in
    let '(later, later_calls) := audit_seg_system_edges p encn work rest in
    (here ++ later, SegSystemCase 1 :: map SegSystemGraph calls ++ later_calls ++
      [SegSystemAppend (length here)])
  end.

Definition audit_seg_system_constraints {N E B} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (encn : N -> positive * list B) (work : seg_work N E)
    (idx : seg_index N E) (direction : audit_seg_direction)
    : list (dense_constraint N E) * list (audit_seg_system_event N E B) :=
  let seeds := match direction with
  | AuditAvailable => Graph.entries (seg_graph idx)
  | AuditBusy => Graph.nodes (seg_graph idx)
  end in
  let seed_rows := map Seed seeds in
  let '(edges, calls) := audit_seg_system_edges p encn work (Graph.nodes (seg_graph idx)) in
  let flow_rows := map Flow edges in
  (seed_rows ++ flow_rows, [SegSystemAppend (length seeds)] ++ calls ++
    [SegSystemAppend (length edges); SegSystemAppend (length seeds)]).

Definition audit_seg_system_event_work {N E B} (weight : B -> nat)
    (event : audit_seg_system_event N E B) : nat :=
  64 + match event with
  | SegSystemCase _ => 0
  | SegSystemGraph call => audit_seg_graph_body_work weight call
  | SegSystemAppend size => size
  end.

Definition audit_seg_system_work {N E B} (weight : B -> nat)
    (events : list (audit_seg_system_event N E B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event total => audit_seg_system_event_work weight event + total) 0 events.

Definition audit_seg_system_input_budget {N E} (EN : encoding N) (idx : seg_index N E) : nat :=
  let g := seg_graph idx in
  let nodes := Graph.nodes g in
  let width := fold_right (fun n total => Pos.size_nat (encode EN n) + total) 0 nodes in
  let edges := flat_map (Graph.out g) nodes in
  (N.to_nat 65536%N) *
    Nat.pow (S (length nodes + length (Graph.entries g) + length edges + width)) 8.

Definition audit_seg_system_event_budget {N E B} (node_budget : N -> nat)
    (event : audit_seg_system_event N E B) : nat :=
  match event with
  | SegSystemGraph call => audit_seg_graph_body_budget node_budget (fun _ => 0) (fun _ => 0)
    (fun _ => 0) call
  | _ => 0
  end.

(** Exact constraints and source bound follow from the captured graph closure. *)
Definition audit_seg_system_adapted_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (p : prepared EN (cfg (gkview gk))) (work : seg_work N E) (idx : seg_index N E)
    (direction : audit_seg_direction) u (weight : B -> nat) node_source node_budget,
    (forall n, fst (seg_build_node_encode cb n) = encode EN n) ->
    (forall n, fst (audit_seg_graph_out p (seg_build_node_encode cb) work n) =
      Graph.out (seg_graph idx) n) ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      node_budget ->
    let '(constraints, events) := audit_seg_system_constraints p (seg_build_node_encode cb) work
      idx direction in
    let expected := match direction with
    | AuditAvailable => System.constraints (seg_available_system EE EU gk u idx)
    | AuditBusy => System.constraints (seg_busy_system EE EU gk u idx)
    end in
    let external := fold_right (fun event total => audit_seg_system_event_budget node_budget
      event + total) 0 events in
    constraints = expected /\ audit_seg_system_work weight events <=
      audit_seg_system_input_budget EN idx + external.
