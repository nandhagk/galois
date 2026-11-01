(** * Counted node-adjacency graph used by the legacy checker

    This observer retains every graph-out and target callback, actual node
    distinctness probe and result-index update used by [legacy_cfg].
    For example, parallel outgoing edges retain separate target calls.
    Builds on: legacy graph preparation and counted map operations. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesMemoryFrontier.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Analyses Require Import AnalysesAuditMemoryDistinct AnalysesAuditMemoryIndex.
Import List.ListNotations.

Inductive audit_legacy_cfg_event (N E CN OE TE : Type) : Type :=
  | AuditLegacyCfgRowCase (remaining : list N)
  | AuditLegacyCfgOutCall (node : N) (edges : list E) (calls : list OE)
  | AuditLegacyCfgTargetCall (edge : E) (target : N) (calls : list TE)
  | AuditLegacyCfgDistinct (events : list (audit_memory_distinct_event N CN))
  | AuditLegacyCfgPairCase (remaining : list N)
  | AuditLegacyCfgPair (node target : N).
Arguments AuditLegacyCfgRowCase {N E CN OE TE} _.
Arguments AuditLegacyCfgOutCall {N E CN OE TE} _ _ _.
Arguments AuditLegacyCfgTargetCall {N E CN OE TE} _ _ _.
Arguments AuditLegacyCfgDistinct {N E CN OE TE} _.
Arguments AuditLegacyCfgPairCase {N E CN OE TE} _.
Arguments AuditLegacyCfgPair {N E CN OE TE} _ _.

Fixpoint audit_legacy_cfg_targets {N E CN OE TE}
    (target : E -> N * list TE) (node : N) (edges : list E)
    : list N * list (audit_legacy_cfg_event N E CN OE TE) :=
  match edges with
  | [] => ([], [])
  | edge :: rest =>
      let '(n, calls) := target edge in
      let '(tail, events) := audit_legacy_cfg_targets target node rest in
      (n :: tail, AuditLegacyCfgTargetCall edge n calls :: events)
  end.

Fixpoint audit_legacy_cfg_pairs {N E CN OE TE} (node : N) (targets : list N)
    : list (N * N) * list (audit_legacy_cfg_event N E CN OE TE) :=
  match targets with
  | [] => ([], [AuditLegacyCfgPairCase targets])
  | target :: rest =>
      let '(tail, events) := audit_legacy_cfg_pairs node rest in
      ((node, target) :: tail, [AuditLegacyCfgPairCase targets; AuditLegacyCfgPair node target] ++
        events)
  end.

Definition audit_legacy_cfg_row {N E CN OE TE} (EN : encoding N)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) (node : N)
    : list (N * N) * list (audit_legacy_cfg_event N E CN OE TE) :=
  let '(edges, out_calls) := out node in
  let '(targets, target_events) := audit_legacy_cfg_targets target node edges in
  let '(distinct, distinct_events) := audit_memory_distinct node_enc targets in
  let '(pairs, pair_events) := audit_legacy_cfg_pairs node distinct in
  (pairs, [AuditLegacyCfgRowCase [node]; AuditLegacyCfgOutCall node edges out_calls] ++
    target_events ++ [AuditLegacyCfgDistinct distinct_events] ++ pair_events).

Definition audit_legacy_cfg_rows {N E CN OE TE} (EN : encoding N)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) (nodes : list N)
    : Map.t N (list (N * N)) *
      list (audit_memory_index_event N (list (N * N)) CN (audit_legacy_cfg_event N E CN OE TE)) :=
  audit_memory_result_index node_enc (audit_legacy_cfg_row EN node_enc out target) nodes.

Definition audit_legacy_cfg_counted {N E CN OE TE} (EN : encoding N)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) (g : Graph.t N E)
    : Graph.t N (N * N) *
      list (audit_memory_index_event N (list (N * N)) CN (audit_legacy_cfg_event N E CN OE TE)) :=
  let '(rows, events) := audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g) in
  ({| Graph.entries := Graph.entries g; Graph.nodes := Graph.nodes g;
      Graph.out := index_edges EN rows; Graph.source := fst; Graph.target := snd |}, events).

Fixpoint audit_legacy_cfg_row_work {N E CN OE TE}
    (node_work : list CN -> nat) (out_work : list OE -> nat) (target_work : list TE -> nat)
    (events : list (audit_legacy_cfg_event N E CN OE TE)) : nat :=
  match events with
  | [] => 0
  | AuditLegacyCfgRowCase _ :: rest => 2 + audit_legacy_cfg_row_work node_work out_work
    target_work rest
  | AuditLegacyCfgOutCall _ edges calls :: rest => 2 + length edges + out_work calls +
      audit_legacy_cfg_row_work node_work out_work target_work rest
  | AuditLegacyCfgTargetCall _ _ calls :: rest => 2 + target_work calls +
      audit_legacy_cfg_row_work node_work out_work target_work rest
  | AuditLegacyCfgDistinct child :: rest => 2 + audit_memory_distinct_work node_work child +
      audit_legacy_cfg_row_work node_work out_work target_work rest
  | AuditLegacyCfgPairCase _ :: rest => 2 + audit_legacy_cfg_row_work node_work out_work
    target_work rest
  | AuditLegacyCfgPair _ _ :: rest => 2 + audit_legacy_cfg_row_work node_work out_work target_work
    rest
  end.

Definition audit_legacy_cfg_source_work {N E CN OE TE}
    (node_work : list CN -> nat) (out_work : list OE -> nat) (target_work : list TE -> nat)
    (events : list (audit_memory_index_event N (list (N * N)) CN (audit_legacy_cfg_event N E CN OE
      TE))) : nat :=
  audit_memory_index_work node_work (audit_legacy_cfg_row_work node_work out_work target_work)
    events.

(** Matching node codes, outgoing and target callbacks recover the ordered legacy adjacency
    graph. *)
Definition audit_legacy_cfg_erases_statement : Prop :=
  forall N E CN OE TE (EN : encoding N) (node_enc : N -> positive * list CN)
    (out : N -> list E * list OE) (target : E -> N * list TE) (g : Graph.t N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    fst (audit_legacy_cfg_counted EN node_enc out target g) = legacy_cfg EN g.

(** The adjacency construction is bounded by result indexing with each actual row charged. *)
Definition audit_legacy_cfg_source_bound_statement : Prop :=
  forall N E CN OE TE (EN : encoding N) (node_enc : N -> positive * list CN)
    (out : N -> list E * list OE) (target : E -> N * list TE) (g : Graph.t N E)
    node_work out_work target_work,
    audit_legacy_cfg_source_work node_work out_work target_work
      (snd (audit_legacy_cfg_counted EN node_enc out target g)) <=
    audit_memory_index_budget node_enc (audit_legacy_cfg_row EN node_enc out target)
      node_work (audit_legacy_cfg_row_work node_work out_work target_work) (Graph.nodes g).
