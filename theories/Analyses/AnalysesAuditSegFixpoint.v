(** * SEG solver generated callback source models

    Instantiate solver index and engine callbacks with the actual sparse graph and Boolean system.
    For example, a flow continuation reads its captured summary map at the actual edge.
    Builds on: SEG builder, Fixpoint source models and graph scheduling source models. *)
From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominators GraphAuditBase
  GraphAuditDfs.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklistCallbacks FixpointAuditScheduleWrapper.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSeg AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder.
Import List.ListNotations.

(** * SEG solver generated callback source models *)

(** The selected actual SEG Boolean constraint system. *)
Definition audit_seg_fx_system {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) (direction : audit_seg_direction)
    : System.t N (dense_constraint N E) bool :=
  match direction with
  | AuditAvailable => seg_available_system EE EU gk u idx
  | AuditBusy => seg_busy_system EE EU gk u idx
  end.

(** The static dependency dictionary is the exact selected graph-system dictionary. *)
Definition audit_seg_fx_static {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) (direction : audit_seg_direction)
    : System.static (audit_seg_fx_system EE EU gk u idx direction) :=
  match direction with
  | AuditAvailable => forward_static _ _ _
  | AuditBusy => backward_static _ _ _
  end.

(** Each solver callback body retains its actual primitive and underlying client events. *)
Inductive audit_seg_fx_event (N E B : Type) : Type :=
  | SegFxCase : nat -> audit_seg_fx_event N E B
  | SegFxGraph : audit_seg_graph_body N E B -> audit_seg_fx_event N E B
  | SegFxNodeEncode : N -> positive -> list B -> audit_seg_fx_event N E B
  | SegFxEdgeEncode : E -> positive -> list B -> audit_seg_fx_event N E B
  | SegFxNodeMap : audit_map_event N positive B -> audit_seg_fx_event N E B
  | SegFxNodeSet : audit_set_event N B -> audit_seg_fx_event N E B
  | SegFxSummary : audit_map_event E (bool * bool) B -> audit_seg_fx_event N E B
  | SegFxBool : nat -> bool -> bool -> bool -> audit_seg_fx_event N E B.

Arguments SegFxCase {N E B} _.

Arguments SegFxGraph {N E B} _.

Arguments SegFxNodeEncode {N E B} _ _ _.

Arguments SegFxEdgeEncode {N E B} _ _ _.

Arguments SegFxNodeMap {N E B} _.

Arguments SegFxNodeSet {N E B} _.

Arguments SegFxSummary {N E B} _.

Arguments SegFxBool {N E B} _ _ _ _.

(** The actual tagged constraint encoder calls the matching client encoder. *)
Definition audit_seg_fx_constraint_encode {N E B} (encn : N -> positive * list B)
    (ence : E -> positive * list B) (c : dense_constraint N E) :
    positive * list (audit_seg_fx_event N E B) :=
  match c with
  | Seed n => let '(code, body) := encn n in (xO code, [SegFxNodeEncode n code body])
  | Flow e => let '(code, body) := ence e in (xI code, [SegFxEdgeEncode e code body])
  end.

(** The node encoder is the actual supplied callback. *)
Definition audit_seg_fx_node_encode {N E B} (encn : N -> positive * list B) (n : N)
    : positive * list (audit_seg_fx_event N E B) :=
  let '(code, body) := encn n in (code, [SegFxNodeEncode n code body]).

(** Flow targets use the generated sparse target or source closure for the selected direction. *)
Definition audit_seg_fx_target {N E B} (direction : audit_seg_direction)
    (ence : E -> positive * list B)
    (target source : E -> N * list B) (work : seg_work N E) (c : dense_constraint N E)
    : N * list (audit_seg_fx_event N E B) :=
  match c with
  | Seed n => (n, [SegFxCase 0])
  | Flow e =>
    let '(result, calls) := match direction with
    | AuditAvailable => audit_seg_graph_target ence target work e
    | AuditBusy => audit_seg_graph_source source e
    end in
    (result, map SegFxGraph calls)
  end.

(** Dependencies use the opposite generated endpoint; seed rows have no dependencies. *)
Definition audit_seg_fx_deps {N E B} (direction : audit_seg_direction)
    (ence : E -> positive * list B)
    (target source : E -> N * list B) (work : seg_work N E) (c : dense_constraint N E)
    : list N * list (audit_seg_fx_event N E B) :=
  match c with
  | Seed _ => ([], [SegFxCase 1])
  | Flow e =>
    let '(result, calls) := match direction with
    | AuditAvailable => audit_seg_graph_source source e
    | AuditBusy => audit_seg_graph_target ence target work e
    end in
    ([result], map SegFxGraph calls)
  end.

(** The concrete index model has no side contributions. *)
Definition audit_seg_fx_index_model {N E B} (direction : audit_seg_direction)
    (encn : N -> positive * list B) (ence : E -> positive * list B)
    (target source : E -> N * list B) (work : seg_work N E)
    : fx_index_external_model N (dense_constraint N E) (audit_seg_fx_event N E B) :=
  FxIndexExternalModel _ _ _ (audit_seg_fx_node_encode (E := E) encn)
    (audit_seg_fx_target direction ence target source work)
    (fun _ => ([], [SegFxCase 2])) (audit_seg_fx_deps direction ence target source work).

(** The source relation fixes each index body to the actual counted operation. *)
Definition audit_seg_fx_index_source {N E B} (direction : audit_seg_direction)
    (encn : N -> positive * list B) (ence : E -> positive * list B)
    (target source : E -> N * list B) (work : seg_work N E)
    : fx_index_external_source N (dense_constraint N E) (audit_seg_fx_event N E B) :=
  FxIndexExternalSource _ _ _
    (fun n result body => audit_seg_fx_node_encode (E := E) encn n = (result, body))
    (fun c result body => audit_seg_fx_target direction ence target source work c = (result, body))
    (fun _ result body => result = [] /\ body = [SegFxCase 2])
    (fun c result body => audit_seg_fx_deps direction ence target source work c = (result, body)).

(** A summary continuation reads the actual selected cached truth table. *)
Definition audit_seg_fx_summary {N E B} (ence : E -> positive * list B)
    (idx : seg_index N E) (direction : audit_seg_direction) (e : E) (bit : bool)
    : bool * list (audit_seg_fx_event N E B) :=
  let summaries := match direction with
  AuditAvailable => seg_forward_summary idx
  | AuditBusy => seg_backward_summary idx
  end in
  let '(found, reads) := audit_map_get ence e summaries in
  (match found with
  Some (f, t) => if bit then t else f
  | None => bit
  end, map SegFxSummary reads).

(** A flow RHS uses the actual sparse endpoint and a cached-summary continuation. *)
Definition audit_seg_fx_rhs {N E B} {EN : encoding N} {g : Graph.t N E} (EE : encoding E)
    (p : prepared EN g) (direction : audit_seg_direction) (encn : N -> positive * list B)
    (ence : E -> positive * list B) (target source : E -> N * list B) (work : seg_work N E)
    (idx : seg_index N E) (c : dense_constraint N E) :
    Query.t N bool * list (audit_seg_fx_event N E B) :=
  match c with
  | Seed n => match direction with
    | AuditAvailable => (Query.Ret false, [SegFxCase 3])
    | AuditBusy => let '(edges, calls) := audit_seg_graph_out p encn work n in
      (Query.Ret (match edges with
      [] => false
      | _ => true
      end), map SegFxGraph calls)
    end
  | Flow e =>
    let '(node, calls) := match direction with
    | AuditAvailable => audit_seg_graph_source source e
    | AuditBusy => audit_seg_graph_target ence target work e
    end in
    let summaries := match direction with
    AuditAvailable => seg_forward_summary idx
    | AuditBusy => seg_backward_summary idx
    end in
    (Query.Ask node (fun bit => Query.Ret (seg_summary_apply EE e bit summaries)),
      map SegFxGraph calls)
  end.

(** Priority reads the actual captured RPO position map. *)
Definition audit_seg_fx_priority {N E B} (encn : N -> positive * list B)
    (positions : Map.t N positive) (n : N) : positive * list (audit_seg_fx_event N E B) :=
  let '(found, reads) := audit_map_get encn n positions in
  (match found with
  Some rank => rank
  | None => 1%positive
  end, map SegFxNodeMap reads).

(** Widening-point lookup reads the actual captured scheduler head set. *)
Definition audit_seg_fx_widening {N E B} (encn : N -> positive * list B)
    (heads : FinSet.t N) (n : N) : bool * list (audit_seg_fx_event N E B) :=
  let '(found, reads) := audit_finset_mem encn n heads in (found, map SegFxNodeSet reads).

(** The declared source dictionary fixes every solver callback to its concrete body. *)
Definition audit_seg_fx_declared_source {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (p : prepared EN (cfg (gkview gk)))
    (direction : audit_seg_direction) (encn : N -> positive * list B)
    (ence : E -> positive * list B)
    (target source : E -> N * list B) (work : seg_work N E) (idx : seg_index N E)
    (schedule : fx_rpo_result N (dense_constraint N E) (audit_seg_fx_event N E B))
    : fx_declared_callback_source N (dense_constraint N E) bool (audit_seg_fx_event N E B) :=
  let sys := audit_seg_fx_system EE EU gk u idx direction in
  let summaries := match direction with
  AuditAvailable => seg_forward_summary idx
  | AuditBusy => seg_backward_summary idx
  end in
  FxDeclaredCallbackSource _ _ _ _
    (fun n result body => audit_seg_fx_node_encode (E := E) encn n = (result, body))
    (fun c result body => audit_seg_fx_constraint_encode encn ence c = (result, body))
    (fun c result body => audit_seg_fx_target direction ence target source work c = (result, body))
    (fun n result body => audit_seg_fx_priority encn (fx_rpo_positions schedule) n = (result, body))
    (fun n result body => audit_seg_fx_widening encn (fx_rpo_heads schedule) n = (result, body))
    (fun c result body => audit_seg_fx_rhs EE p direction encn ence target source work idx c =
      (result, body))
    (fun k bit result body => exists e,
      In (Flow e) (System.constraints sys) /\
      k = (fun b => Query.Ret (seg_summary_apply EE e b summaries)) /\
      let '(value, calls) := audit_seg_fx_summary (N := N) ence idx direction e bit in
      result = Query.Ret value /\ body = calls)
    (fun a b result body => result = implb b a /\ body = [SegFxBool 0 a b result])
    (fun a b result body => result = andb a b /\ body = [SegFxBool 1 a b result])
    (fun a b result body => result = andb a b /\ body = [SegFxBool 2 a b result]).

(** Component body work includes generated graph, trie and genuine client callback bodies. *)
Definition audit_seg_fx_event_work {N E B} (weight : B -> nat) (event : audit_seg_fx_event N E B) :
    nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SegFxGraph call => audit_seg_graph_body_work weight call
  | SegFxNodeEncode _ _ xs | SegFxEdgeEncode _ _ xs => body xs
  | SegFxNodeMap call => audit_map_source_work body [call]
  | SegFxNodeSet call => audit_finset_source_work body [call]
  | SegFxSummary call => audit_map_source_work body [call]
  | SegFxCase _ | SegFxBool _ _ _ _ => 0
  end.

(** Component external work counts only actual client callback bodies. *)
Definition audit_seg_fx_event_external {N E B} (weight : B -> nat)
    (event : audit_seg_fx_event N E B) : nat :=
  match event with
  | SegFxGraph call => audit_seg_graph_body_external weight call
  | SegFxNodeEncode _ _ body | SegFxEdgeEncode _ _ body |
    SegFxNodeMap (AuditMapGet _ _ _ _ body _) | SegFxNodeMap (AuditMapSet _ _ _ _ _ body _) |
    SegFxNodeMap (AuditMapRemove _ _ _ _ body _) | SegFxNodeSet (AuditSetMem _ _ _ _ body _) |
    SegFxNodeSet (AuditSetAdd _ _ _ _ body _) | SegFxNodeSet (AuditSetRemove _ _ _ _ body _) |
    SegFxSummary (AuditMapGet _ _ _ _ body _) | SegFxSummary (AuditMapSet _ _ _ _ _ body _) |
    SegFxSummary (AuditMapRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Per-call budget selection uses only captured client callback inputs. *)
Definition audit_seg_fx_event_external_budget {N E B} (node_budget : N -> nat)
    (edge_budget target_budget source_budget : E -> nat) (event : audit_seg_fx_event N E B) : nat :=
  match event with
  | SegFxGraph call => audit_seg_graph_body_budget node_budget edge_budget target_budget
    source_budget call
  | SegFxNodeEncode n _ _ | SegFxNodeMap (AuditMapGet n _ _ _ _ _) |
    SegFxNodeMap (AuditMapSet n _ _ _ _ _ _) | SegFxNodeMap (AuditMapRemove n _ _ _ _ _) |
    SegFxNodeSet (AuditSetMem n _ _ _ _ _) | SegFxNodeSet (AuditSetAdd n _ _ _ _ _) |
    SegFxNodeSet (AuditSetRemove n _ _ _ _ _) => node_budget n
  | SegFxEdgeEncode e _ _ | SegFxSummary (AuditMapGet e _ _ _ _ _) |
    SegFxSummary (AuditMapSet e _ _ _ _ _ _) | SegFxSummary (AuditMapRemove e _ _ _ _ _) =>
    edge_budget e
  | _ => 0
  end.

(** One node operation has an input-width and actual encoder-budget allowance. *)
Definition audit_seg_fx_node_budget {N} (EN : encoding N) (node_budget : N -> nat) (n : N) : nat :=
  4096 + 64 * Pos.size_nat (encode EN n) + 2 * node_budget n.

(** One edge operation includes actual encoder and endpoint budgets. *)
Definition audit_seg_fx_edge_budget {E} (EE : encoding E)
    (edge_budget target_budget source_budget : E -> nat)
    (e : E) : nat :=
  4096 + 64 * Pos.size_nat (encode EE e) + edge_budget e + target_budget e + source_budget e.

(** Each index callback budget is determined by its own actual input. *)
Definition audit_seg_fx_index_budget {N E B} (EN : encoding N) (EE : encoding E)
    (weight : B -> nat) (node_budget : N -> nat)
    (edge_budget target_budget source_budget : E -> nat)
    : fx_index_external_budget N (dense_constraint N E) (audit_seg_fx_event N E B) :=
  FxIndexExternalBudget _ _ _ (audit_seg_fx_event_work weight)
    (audit_seg_fx_node_budget EN node_budget)
    (fun c => match c with
      Seed n => audit_seg_fx_node_budget EN node_budget n
      | Flow e => audit_seg_fx_edge_budget EE edge_budget target_budget source_budget e
      end)
    (fun _ => 256)
    (fun c => match c with
      Seed _ => 256
      | Flow e => audit_seg_fx_edge_budget EE edge_budget target_budget source_budget e
      end).

(** Finite actual constraints bound the source cost of every reachable continuation. *)
Definition audit_seg_fx_continuation_budget {N E} (EE : encoding E) (edge_budget : E -> nat)
    (constraints : list (dense_constraint N E)) : nat :=
  fold_right (fun c total => match c with
    | Seed _ => total
    | Flow e => Nat.max total (4096 + 64 * Pos.size_nat (encode EE e) + edge_budget e)
    end) 256 constraints.

(** Solver callback budgets are explicit source bounds, with no opaque continuation oracle. *)
Definition audit_seg_fx_declared_budget {N E B} (EN : encoding N) (EE : encoding E)
    (weight : B -> nat) (node_budget : N -> nat)
    (edge_budget target_budget source_budget : E -> nat)
    (constraints : list (dense_constraint N E))
    : fx_declared_callback_budget N (dense_constraint N E) bool (audit_seg_fx_event N E B) :=
  FxDeclaredCallbackBudget _ _ _ _ (audit_seg_fx_event_work weight)
    (audit_seg_fx_node_budget EN node_budget)
    (fun c => match c with
      Seed n => audit_seg_fx_node_budget EN node_budget n
      | Flow e => audit_seg_fx_edge_budget EE edge_budget target_budget source_budget e
      end)
    (fun c => match c with
      Seed n => audit_seg_fx_node_budget EN node_budget n
      | Flow e => audit_seg_fx_edge_budget EE edge_budget target_budget source_budget e
      end)
    (audit_seg_fx_node_budget EN node_budget) (audit_seg_fx_node_budget EN node_budget)
    (fun c => match c with
      Seed n => audit_seg_fx_node_budget EN node_budget n
      | Flow e => audit_seg_fx_edge_budget EE edge_budget target_budget source_budget e
      end)
    (fun _ _ => audit_seg_fx_continuation_budget EE edge_budget constraints)
    (fun _ _ => 256) (fun _ _ => 256) (fun _ _ => 256).

(** Concrete index and solver source laws follow from actual builder and callback inputs. *)
Definition audit_seg_fx_instantiation_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B) u direction
    (weight : B -> nat)
    node_source edge_source target_source source_source node_budget edge_budget target_budget
    source_budget,
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight edge_source
      edge_budget ->
    audit_graph_external_callback_adapter (seg_build_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter (seg_build_source cb) weight source_source
      source_budget ->
    let receipt := audit_seg_full_source_counted EN EE (cfg (gkview gk)) cb u in
    let idx := audit_seg_full_result receipt in
    let p := audit_seg_full_index receipt in let work := audit_seg_full_work_state receipt in
    let system := audit_seg_fx_system EE EU gk u idx direction in
    let static := audit_seg_fx_static EE EU gk u idx direction in
    let index_cb := audit_seg_fx_index_model direction (seg_build_node_encode cb)
      (seg_build_edge_encode cb)
      (seg_build_target cb) (seg_build_source cb) work in
    let index_source := audit_seg_fx_index_source direction (seg_build_node_encode cb)
      (seg_build_edge_encode cb)
      (seg_build_target cb) (seg_build_source cb) work in
    let index_budget := audit_seg_fx_index_budget EN EE weight node_budget edge_budget target_budget
      source_budget in
    let schedule := fx_rpo_scheduler_counted EN system static index_cb in
    let declared_source := audit_seg_fx_declared_source EN EE EU gk u p direction
      (seg_build_node_encode cb)
      (seg_build_edge_encode cb) (seg_build_target cb) (seg_build_source cb) work idx schedule in
    let declared_budget := audit_seg_fx_declared_budget EN EE weight node_budget edge_budget
      target_budget source_budget (System.constraints system) in
    fx_index_external_erases EN system static index_cb /\ fx_index_external_bounded index_cb
      index_budget /\
      fx_dep_source_laws index_cb index_source /\
      fx_declared_source_laws EN (dense_constraint_encoding EN EE) seg_must_lattice
        (rpo_scheduler EN system static) system declared_source /\
      fx_declared_callback_bounded declared_source declared_budget.
