(** * Counted legacy successor enumeration

    The definition-side roots are every indexed outgoing edge target in stored order.
    This observer retains the actual map lookup and maps each parallel edge separately.
    For example, parallel edges can produce repeated successor nodes.
    Builds on: legacy graph preparation and counted maps. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Analyses Require Import AnalysesMemoryLegacy.
From Galois.Collections Require Import CollectionsAuditMap.
Import List.ListNotations.

Inductive audit_legacy_successor_event (N E CN : Type) : Type :=
  | AuditLegacySuccessorLookup (calls : list (audit_map_event N (list E) CN))
  | AuditLegacySuccessorMapCase (remaining : list E)
  | AuditLegacySuccessorTarget (edge : E) (target : N).
Arguments AuditLegacySuccessorLookup {N E CN} _.
Arguments AuditLegacySuccessorMapCase {N E CN} _.
Arguments AuditLegacySuccessorTarget {N E CN} _ _.

Fixpoint audit_legacy_successor_map {N E CN} (g : Graph.t N E) (edges : list E)
    : list N * list (audit_legacy_successor_event N E CN) :=
  match edges with
  | [] => ([], [])
  | edge :: rest =>
      let target := Graph.target g edge in
      let '(tail, events) := audit_legacy_successor_map g rest in
      (target :: tail, [AuditLegacySuccessorMapCase edges; AuditLegacySuccessorTarget edge target]
        ++ events)
  end.

Definition audit_legacy_successors_counted {N E CN} (EN : encoding N)
    (node_enc : N -> positive * list CN) (g : Graph.t N E) (p : prepared EN g) (node : N)
    : list N * list (audit_legacy_successor_event N E CN) :=
  let '(found, calls) := audit_map_get node_enc node (out_index p) in
  let edges :=
    match found with
    | Some xs => xs
    | None => []
    end in
  let '(result, events) := audit_legacy_successor_map g edges in
  (result, AuditLegacySuccessorLookup calls :: events).

Fixpoint audit_legacy_successor_source_work {N E CN} (node_work : list CN -> nat)
    (events : list (audit_legacy_successor_event N E CN)) : nat :=
  match events with
  | [] => 0
  | AuditLegacySuccessorLookup calls :: rest => 2 + audit_map_source_work node_work calls +
      audit_legacy_successor_source_work node_work rest
  | AuditLegacySuccessorMapCase _ :: rest => 2 + audit_legacy_successor_source_work node_work rest
  | AuditLegacySuccessorTarget _ _ :: rest => 2 + audit_legacy_successor_source_work node_work rest
  end.

(** With matching node encodings, indexed edge targets agree with the legacy successor list in
  order. *)
Definition audit_legacy_successors_erases_statement : Prop :=
  forall N E CN (EN : encoding N) (node_enc : N -> positive * list CN)
    (g : Graph.t N E) (p : prepared EN g) node,
    (forall n, fst (node_enc n) = encode EN n) ->
    fst (audit_legacy_successors_counted EN node_enc g p node) = legacy_successors EN g p node.
