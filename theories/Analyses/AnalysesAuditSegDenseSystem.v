(** * Dense SEG system and index callbacks

    Dense constraints use original graph endpoints and a tagged node-or-edge encoding.
    For example, a backward flow targets its source and reads its target.
    Builds on: ViewsGraph and the indexed Fixpoint source models. *)
From Stdlib Require Import List PArith Arith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditInter.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointWorklist
  FixpointAuditIndex FixpointAuditWorklistCallbacks FixpointAuditScheduleWrapper.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder
  AnalysesAuditSegUniverse AnalysesAuditSegDenseUniverse AnalysesAuditSegDenseSets
  AnalysesAuditSegDenseTransfer.
Import List.ListNotations.

(** * Dense SEG system and index callbacks *)

(** The selected system is exactly the existing forward or backward dense system. *)
Definition audit_dense_fx_system {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C)
    (direction : audit_seg_direction) : System.t N (dense_constraint N E) (avail_set EU gk) :=
  match direction with
  | AuditAvailable => available_system EU gk
  | AuditBusy => busy_system EU gk
  end.

(** The selected static dictionary is the source system's actual dictionary. *)
Definition audit_dense_fx_static {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C)
    (direction : audit_seg_direction) : System.static (audit_dense_fx_system EU gk direction) :=
  match direction with
  | AuditAvailable => forward_static _ _ _
  | AuditBusy => backward_static _ _ _
  end.

Inductive audit_dense_fx_event (N E U B : Type) : Type :=
  | DenseFxNodeEncode (node : N) (code : positive) (body : list B)
  | DenseFxEdgeEncode (edge : E) (code : positive) (body : list B)
  | DenseFxOut (node : N) (edges : list E) (body : list B)
  | DenseFxTarget (edge : E) (node : N) (body : list B)
  | DenseFxSource (edge : E) (node : N) (body : list B)
  | DenseFxUniverse (events : list (audit_seg_universe_event N E U B))
  | DenseFxTransfer (events : list (audit_dense_transfer_event N E U B))
  | DenseFxSubset (events : list (audit_dense_subset_event U))
  | DenseFxInter (events : list (audit_inter_event U))
  | DenseFxNodeMap (event : audit_map_event N positive B)
  | DenseFxNodeSet (event : audit_set_event N B)
  | DenseFxCase (site : nat).

Arguments DenseFxNodeEncode {N E U B} _ _ _.

Arguments DenseFxEdgeEncode {N E U B} _ _ _.

Arguments DenseFxOut {N E U B} _ _ _.

Arguments DenseFxTarget {N E U B} _ _ _.

Arguments DenseFxSource {N E U B} _ _ _.

Arguments DenseFxUniverse {N E U B} _.

Arguments DenseFxTransfer {N E U B} _.

Arguments DenseFxSubset {N E U B} _.

Arguments DenseFxInter {N E U B} _.

Arguments DenseFxNodeMap {N E U B} _.

Arguments DenseFxNodeSet {N E U B} _.

Arguments DenseFxCase {N E U B} _.

(** Seed and flow codes invoke their actual node and edge encoders, respectively. *)
Definition audit_dense_constraint_encode {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (c : dense_constraint N E) : positive * list (audit_dense_fx_event N E U B) :=
  match c with
  | Seed n => let '(code, body) := seg_build_node_encode cb n in
    (xO code, [DenseFxNodeEncode n code body])
  | Flow e => let '(code, body) := seg_build_edge_encode cb e in
    (xI code, [DenseFxEdgeEncode e code body])
  end.

(** The source node encoding carries its actual client body. *)
Definition audit_dense_node_encode {N E U B} (cb : audit_seg_build_callbacks N E U B) (n : N) :
    positive * list (audit_dense_fx_event N E U B) :=
  let '(code, body) := seg_build_node_encode cb n in (code, [DenseFxNodeEncode n code body]).

(** Direction selects the actual endpoint invoked by a flow target. *)
Definition audit_dense_target {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (c : dense_constraint N E) :
    N * list (audit_dense_fx_event N E U B) :=
  match c with
  | Seed n => (n, [DenseFxCase 0])
  | Flow e => match direction with
    | AuditAvailable => let '(n, body) := seg_build_target cb e in (n, [DenseFxTarget e n body])
    | AuditBusy => let '(n, body) := seg_build_source cb e in (n, [DenseFxSource e n body])
    end
  end.

(** Flow dependencies invoke the opposite graph endpoint; seed dependencies are empty. *)
Definition audit_dense_deps {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (c : dense_constraint N E) :
    list N * list (audit_dense_fx_event N E U B) :=
  match c with
  | Seed _ => ([], [DenseFxCase 1])
  | Flow e => match direction with
    | AuditAvailable => let '(n, body) := seg_build_source cb e in ([n], [DenseFxSource e n body])
    | AuditBusy => let '(n, body) := seg_build_target cb e in ([n], [DenseFxTarget e n body])
    end
  end.

(** The index source model uses the actual dense target and dependency bodies. *)
Definition audit_dense_index_model {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) :
    fx_index_external_model N (dense_constraint N E) (audit_dense_fx_event N E U B) :=
  FxIndexExternalModel _ _ _ (audit_dense_node_encode cb) (audit_dense_target cb direction)
    (fun _ => ([], [DenseFxCase 2])) (audit_dense_deps cb direction).

(** Each index callback relation identifies its same-call captured concrete body. *)
Definition audit_dense_index_source {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) :
    fx_index_external_source N (dense_constraint N E) (audit_dense_fx_event N E U B) :=
  FxIndexExternalSource _ _ _
    (fun n out body => audit_dense_node_encode cb n = (out, body))
    (fun c out body => audit_dense_target cb direction c = (out, body))
    (fun _ out body => out = [] /\ body = [DenseFxCase 2])
    (fun c out body => audit_dense_deps cb direction c = (out, body)).

(** System constraints enumerate outgoing edges once and retain actual source callbacks. *)
Definition audit_dense_constraints {N E U B} (g : Graph.t N E)
    (cb : audit_seg_build_callbacks N E U B) (direction : audit_seg_direction) :
    list (dense_constraint N E) * list (audit_seg_universe_event N E U B) :=
  let seeds := match direction with
  AuditAvailable => Graph.entries g
  | AuditBusy => Graph.nodes g
  end in
  let seed_rows := map Seed seeds in
  let '(edges, events) := audit_seg_universe_edges cb (Graph.nodes g) in
  let flow_rows := map Flow edges in
  (seed_rows ++ flow_rows,
    SegUniverseAppend (length seeds) :: events ++
      [SegUniverseAppend (length edges); SegUniverseAppend (length seeds)]).

(** The constraint budget includes entries even when they are absent from the node list. *)
Definition audit_dense_constraints_budget {N E} (g : Graph.t N E) : nat :=
  (N.to_nat 65536%N) * Nat.pow (S (length (Graph.nodes g) + length (Graph.entries g) +
    length (edges_of g))) 8.

(** Under the outgoing callback law, constraints match the source list and obey the work bound. *)
Definition audit_dense_constraints_source_statement : Prop :=
  forall (S O N E U C B : Type) (EU : encoding U) (gk : genkill_view S O N E U C)
    (cb : audit_seg_build_callbacks N E U B) (weight : B -> nat) direction out_source out_budget,
    (forall n, fst (seg_build_out cb n) = Graph.out (cfg (gkview gk)) n) ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source out_budget ->
    let g := cfg (gkview gk) in
    let '(out, events) := audit_dense_constraints g cb direction in
    out = System.constraints (audit_dense_fx_system EU gk direction) /\
      audit_seg_universe_work weight events <= audit_dense_constraints_budget g +
        fold_right (fun e n => audit_seg_universe_event_budget out_budget (fun _ => 0)
          (fun _ => 0) e + n) 0 events.

(** Source work includes nested transfer, finite-set, scheduler and actual client bodies. *)
Definition audit_dense_fx_event_work {N E U B} (weight : B -> nat)
    (event : audit_dense_fx_event N E U B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | DenseFxNodeEncode _ _ xs | DenseFxEdgeEncode _ _ xs | DenseFxOut _ _ xs |
    DenseFxTarget _ _ xs | DenseFxSource _ _ xs => body xs
  | DenseFxUniverse events => audit_seg_universe_work weight events
  | DenseFxTransfer events => audit_dense_transfer_work weight events
  | DenseFxSubset events => audit_dense_subset_work events
  | DenseFxInter events => audit_finset_inter_source_work events
  | DenseFxNodeMap e => audit_map_source_work body [e]
  | DenseFxNodeSet e => audit_finset_source_work body [e]
  | DenseFxCase _ => 0
  end.

(** The generated index uses per-node and per-edge bounds on its concrete callbacks. *)
Definition audit_dense_fx_index_budget {N E U B} (EN : encoding N) (EE : encoding E)
    (weight : B -> nat) (node_budget : N -> nat)
    (edge_budget target_budget source_budget : E -> nat) :
    fx_index_external_budget N (dense_constraint N E) (audit_dense_fx_event N E U B) :=
  FxIndexExternalBudget _ _ _ (audit_dense_fx_event_work weight)
    (fun n => 256 + node_budget n + 16 * Pos.size_nat (encode EN n))
    (fun c => match c with
      Seed _ => 256
      | Flow e => 256 + target_budget e + source_budget e
      end)
    (fun _ => 256)
    (fun c => match c with
      Seed _ => 256
      | Flow e => 256 + target_budget e + source_budget e
      end).

(** The generated index dictionary erases and is bounded by actual endpoint client bodies. *)
Definition audit_dense_fx_index_statement : Prop :=
  forall (S O N E U C B : Type) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (weight : B -> nat)
    node_source edge_source target_source source_source node_budget edge_budget target_budget
    source_budget,
    (forall n, fst (seg_build_node_encode cb n) = encode EN n) ->
    (forall e, fst (seg_build_edge_encode cb e) = encode EE e) ->
    (forall e, fst (seg_build_target cb e) = Graph.target (cfg (gkview gk)) e) ->
    (forall e, fst (seg_build_source cb e) = Graph.source (cfg (gkview gk)) e) ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight edge_source
      edge_budget ->
    audit_graph_external_callback_adapter (seg_build_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter (seg_build_source cb) weight source_source
      source_budget ->
    let sys := audit_dense_fx_system EU gk direction in
    let static := audit_dense_fx_static EU gk direction in
    let model := audit_dense_index_model cb direction in
    let budget := audit_dense_fx_index_budget EN EE weight node_budget edge_budget
      target_budget source_budget in
    fx_index_external_erases EN sys static model /\ fx_index_external_bounded model budget /\
      fx_dep_source_laws model (audit_dense_index_source cb direction).
