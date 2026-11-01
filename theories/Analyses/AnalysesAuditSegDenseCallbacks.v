(** * Dense SEG solver callbacks

    The generated solver uses actual graph endpoints, finite must operations and transfers.
    For example, a backward seed inspects its actual outgoing list before choosing its value.
    Builds on: AnalysesAuditSegDenseSystem and the captured RPO schedule. *)
From Stdlib Require Import List Bool PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditInter.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Graph Require Import GraphCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklistCallbacks FixpointAuditScheduleWrapper.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder
  AnalysesAuditSegDenseUniverse AnalysesAuditSegDenseSets AnalysesAuditSegDenseTransfer
  AnalysesAuditSegDenseSystem.
Import List.ListNotations.

(** * Dense SEG solver callbacks *)

(** A seed captures the selected empty clamp or full-universe construction. *)
Definition audit_dense_seed {N E U B} (g : Graph.t N E) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (n : N) :
    FinSet.t U * list (audit_dense_fx_event N E U B) :=
  let '(boundary, before) := match direction with
  | AuditAvailable => (true, [])
  | AuditBusy => let '(out, body) := seg_build_out cb n in
    (match out with
    [] => true
    | _ => false
    end, [DenseFxOut n out body])
  end in
  let '(universe, universe_events) := audit_dense_universe g cb in
  if boundary then
    let '(result, clamp_events) := audit_dense_clamp cb universe FinSet.empty in
    (result, before ++ [DenseFxUniverse universe_events; DenseFxTransfer clamp_events])
  else
    let '(result, set_events) := audit_finset_of_list (seg_build_expr_encode cb) universe in
    (result, before ++ [DenseFxUniverse universe_events;
      DenseFxTransfer [DenseTransferSet set_events]]).

(** RHS source is a relational same-invocation derivation, including its actual returned query. *)
Definition audit_dense_rhs_source {S O N E U C B} (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (c : dense_constraint N E)
    (out : Query.t N (avail_set EU gk)) (body : list (audit_dense_fx_event N E U B)) : Prop :=
  let g := cfg (gkview gk) in
  let system := audit_dense_fx_system EU gk direction in
  match c with
  | Seed n => exists value raw events,
    out = Query.Ret value /\ out = System.rhs system c /\
    audit_dense_seed g cb direction n = (raw, events) /\ proj1_sig value = raw /\ body = events
  | Flow e => exists n endpoint,
    (match direction with
    | AuditAvailable => seg_build_source cb e = (n, endpoint) /\ body = [DenseFxSource e n
      endpoint]
    | AuditBusy => seg_build_target cb e = (n, endpoint) /\ body = [DenseFxTarget e n endpoint]
    end) /\
    out = Query.Ask n (fun input => Query.Ret (avail_transfer EU gk e input))
  end.

(** A flow continuation captures its transfer on the actual finite-set input. *)
Definition audit_dense_continuation_source {S O N E U C B} (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (k : avail_set EU gk -> Query.t N (avail_set EU gk))
    (input : avail_set EU gk) (out : Query.t N (avail_set EU gk))
    (body : list (audit_dense_fx_event N E U B)) : Prop :=
  exists edge raw events,
    In (Flow edge) (System.constraints (audit_dense_fx_system EU gk direction)) /\
    k = (fun value => Query.Ret (avail_transfer EU gk edge value)) /\
    audit_dense_transfer (cfg (gkview gk)) cb edge (proj1_sig input) = (raw, events) /\
    raw = proj1_sig (avail_transfer EU gk edge input) /\
    out = Query.Ret (avail_transfer EU gk edge input) /\ body = [DenseFxTransfer events].

(** RPO priority reads the actual captured position map. *)
Definition audit_dense_priority {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (positions : Map.t N positive) (n : N) : positive * list (audit_dense_fx_event N E U B) :=
  let '(found, events) := audit_map_get (seg_build_node_encode cb) n positions in
  (match found with
  Some p => p
  | None => 1%positive
  end, map DenseFxNodeMap events).

(** RPO widening membership reads the actual captured head set. *)
Definition audit_dense_widening {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (heads : FinSet.t N) (n : N) : bool * list (audit_dense_fx_event N E U B) :=
  let '(found, events) := audit_finset_mem (seg_build_node_encode cb) n heads in
  (found, map DenseFxNodeSet events).

(** Every declared callback is tied to a concrete source-shaped invocation. *)
Definition audit_dense_declared_source {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction)
    (schedule : fx_rpo_result N (dense_constraint N E) (audit_dense_fx_event N E U B)) :
    fx_declared_callback_source N (dense_constraint N E) (avail_set EU gk)
      (audit_dense_fx_event N E U B) :=
  let lattice := avail_lattice EU gk in
  FxDeclaredCallbackSource _ _ _ _
    (fun n result body => audit_dense_node_encode cb n = (result, body))
    (fun c result body => audit_dense_constraint_encode cb c = (result, body))
    (fun c result body => audit_dense_target cb direction c = (result, body))
    (fun n result body => audit_dense_priority cb (fx_rpo_positions schedule) n = (result, body))
    (fun n result body => audit_dense_widening cb (fx_rpo_heads schedule) n = (result, body))
    (audit_dense_rhs_source EU gk cb direction)
    (audit_dense_continuation_source EU gk cb direction)
    (fun a b result body => let '(out, events) := audit_dense_subset (proj1_sig b) (proj1_sig a) in
      result = out /\ body = [DenseFxSubset events])
    (fun a b result body => let '(raw, events) := audit_dense_inter (proj1_sig a) (proj1_sig b) in
      result = join lattice a b /\ proj1_sig result = raw /\ body = [DenseFxInter events])
    (fun a b result body => let '(raw, events) := audit_dense_inter (proj1_sig a) (proj1_sig b) in
      result = widen lattice a b /\ proj1_sig result = raw /\ body = [DenseFxInter events]).
