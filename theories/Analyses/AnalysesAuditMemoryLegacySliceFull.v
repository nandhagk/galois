(** * Full counted legacy forward/reverse slice

    This adapter executes the two actual DFS walks used by [legacy_slice], then
    feeds their returned visited sets into every actual graph-node membership and
    footprint-overlap check. Reverse preparation is the library's exact index swap.
    For example, both DFS walks contribute their events to the result.
    Builds on: graph DFS, legacy slices and footprint overlap. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy.
From Galois.Collections Require Import CollectionsAuditFinSet CollectionsAuditPrimitive.
From Galois.Analyses Require Import AnalysesAuditMemoryLegacySlice AnalysesAuditMemoryLegacyOverlap.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.
Import List.ListNotations.

Definition audit_legacy_dfs_callbacks {N E CN} (node_enc : N -> positive * list CN)
    (g : Graph.t N E) : audit_dfs_callback_model N E (list CN) :=
  @AuditDfsCallbackModel N E (list CN)
    (fun edge => (Graph.target g edge, []))
    (fun n => let '(code, trace) := node_enc n in (code, [trace])).

Definition audit_legacy_reached_counted {N E CN} (EN : encoding N)
    (node_enc : N -> positive * list CN) (g : Graph.t N E) (p : prepared EN g) (roots : list N)
    : FinSet.t N * list (audit_dfs_nested_event N E (audit_graph_callback_capture N E (list CN))) :=
  let '(result, events) := audit_dfs_source_counted p (audit_legacy_dfs_callbacks node_enc g)
    FinSet.empty roots in
  (visited result, events).

Record audit_legacy_slice_full_events (N E T CN CT W : Type) : Type :=
  AuditLegacySliceFullEvents {
    audit_legacy_slice_forward_dfs : list (audit_dfs_nested_event N E
      (audit_graph_callback_capture N E (list CN)));
    audit_legacy_slice_reverse_dfs : list (audit_dfs_nested_event N E
      (audit_graph_callback_capture N E (list CN)));
    audit_legacy_slice_node_checks : list (audit_legacy_slice_event N T CN CT W)
  }.
Arguments AuditLegacySliceFullEvents {N E T CN CT W} _ _ _.
Arguments audit_legacy_slice_forward_dfs {N E T CN CT W} _.
Arguments audit_legacy_slice_reverse_dfs {N E T CN CT W} _.
Arguments audit_legacy_slice_node_checks {N E T CN CT W} _.

Definition audit_legacy_slice_full {N E T CN CT W} (EN : encoding N) (ET : encoding T)
    (node_enc : N -> positive * list CN) (site_enc : T -> positive * list CT)
    (g : Graph.t N E) (p : prepared EN g)
    (writes : N -> list (footprint T) * list W) (read : list (footprint T))
    (roots : list N) (load : N)
    : bool * audit_legacy_slice_full_events N E T CN CT W :=
  let '(forward, forward_events) := audit_legacy_reached_counted EN node_enc g p roots in
  let reverse_graph := reverse_graph p [load] in
  let reverse_prep := prepared_reverse p [load] in
  let '(backward, backward_events) := audit_legacy_reached_counted EN node_enc reverse_graph
    reverse_prep [load] in
  let '(answer, node_events) := audit_legacy_slice_nodes node_enc site_enc writes read
    forward backward (Graph.nodes g) in
  (answer, AuditLegacySliceFullEvents forward_events backward_events node_events).

Definition audit_legacy_slice_full_source_work {N E T CN CT W} (EN : encoding N)
    (node_work : list CN -> nat) (site_work : list CT -> nat) (writes_work : list W -> nat)
    (events : audit_legacy_slice_full_events N E T CN CT W) : nat :=
  audit_dfs_source_work node_work (audit_legacy_slice_forward_dfs events) +
  audit_dfs_source_work node_work (audit_legacy_slice_reverse_dfs events) +
  audit_legacy_slice_source_work node_work site_work writes_work (audit_legacy_slice_node_checks
    events).

(** Matching encoders recover the legacy slice built from both reachability walks. *)
Definition audit_legacy_slice_full_erases_statement : Prop :=
  forall N E T CN CT W (EN : encoding N) (ET : encoding T)
    (node_enc : N -> positive * list CN) (site_enc : T -> positive * list CT)
    (g : Graph.t N E) (p : prepared EN g)
    (writes : N -> list (footprint T) * list W) (read : list (footprint T)) roots load,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    fst (audit_legacy_slice_full EN ET node_enc site_enc g p writes read roots load) =
      legacy_slice EN ET g p (fun n => fst (writes n)) read roots load.

(** The full slice work is bounded by the stated DFS and node-scan charges. *)
Definition audit_legacy_slice_full_trace_bound_statement : Prop :=
  forall N E T CN CT W (EN : encoding N) (ET : encoding T)
    (node_enc : N -> positive * list CN) (site_enc : T -> positive * list CT)
    (g : Graph.t N E) (p : prepared EN g)
    (writes : N -> list (footprint T) * list W) read roots load node_work site_work writes_work,
    let events := snd (audit_legacy_slice_full EN ET node_enc site_enc g p writes read roots load)
      in
    audit_legacy_slice_full_source_work EN node_work site_work writes_work events <=
      audit_dfs_source_budget EN g p roots + audit_dfs_source_body_work node_work
        (audit_legacy_slice_forward_dfs events) +
      audit_dfs_source_budget EN (reverse_graph p [load]) (prepared_reverse p [load]) [load] +
      audit_dfs_source_body_work node_work (audit_legacy_slice_reverse_dfs events) +
      audit_legacy_slice_budget node_enc site_enc writes node_work site_work writes_work
        read (visited (dfs p FinSet.empty roots))
        (visited (dfs (prepared_reverse p [load]) FinSet.empty [load])) (Graph.nodes g).
