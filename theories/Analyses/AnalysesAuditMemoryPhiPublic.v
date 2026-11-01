(** * Fixed public phi pruning and proof-carrying result packaging

    The public package contains the same plain computed graph and representative map.
    For example, the graph-only result projects that same representative-bearing result.
    Builds on: the fixed plain phi producer and the original history, shape and byte predicates. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryPhiState
  AnalysesAuditMemoryPhiConsumer.

(** Pruning a well-formed memory graph produces a well-formed memory graph. *)
Definition audit_memory_phi_prune_wf_statement : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    memory_graph_wf g effects mg ->
    memory_graph_wf g effects (phi_graph (audit_memory_phi_prune N E T EN EE g effects mg)).

(** Given a proof that pruning preserves well-formedness, pack returns the pruned phi result
    with that proof. *)
Definition audit_memory_phi_prune_pack (correct : audit_memory_phi_prune_wf_statement)
    : memory_prune_with_map_type :=
  fun N E T EN EE g effects mg wf =>
    exist _ (audit_memory_phi_prune N E T EN EE g effects mg)
      (correct N E T EN EE g effects mg wf).

(** Given the same well-formedness proof, graph packing returns the pruned graph with its proof. *)
Definition audit_memory_phi_graph_pack (correct : audit_memory_phi_prune_wf_statement)
    : memory_prune_type := memory_prune_from_map (audit_memory_phi_prune_pack correct).

(** The packed producer satisfies the history, terminal, cycle, shape, resolution and
    conditional legacy contracts. *)
Definition audit_memory_phi_public_semantics_statement : Prop :=
  audit_memory_phi_prune_wf_statement /\
  forall correct,
    let operation := audit_memory_phi_prune_pack correct in
    memory_phi_projection_statement operation /\
    memory_phi_terminal_removed_statement operation /\
    memory_phi_cycles_retained_statement operation /\
    memory_pruned_builders_projection_statement operation /\
    memory_prune_legacy_checked_statement operation /\
    memory_prune_legacy_bytes_statement operation /\
    memory_phi_removed_has_operand_statement operation /\
    memory_phi_resolved_removed_statement operation /\
    memory_phi_output_shape_statement operation /\
    memory_phi_map_domain_statement operation /\
    phi_resolution_statement operation /\
    memory_prune_wf_contract (audit_memory_phi_graph_pack correct) /\
    memory_prune_map_projection_contract (audit_memory_phi_graph_pack correct) operation.

(** The two packed operations return the computed phi result and its graph projection. *)
Definition audit_memory_phi_public_projection_statement : Prop :=
  forall correct N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) (mg : memory_graph N E) wf,
    proj1_sig (audit_memory_phi_prune_pack correct N E T EN EE g effects mg wf) =
      audit_memory_phi_prune N E T EN EE g effects mg /\
    proj1_sig (audit_memory_phi_graph_pack correct N E T EN EE g effects mg wf) =
      phi_graph (audit_memory_phi_prune N E T EN EE g effects mg).
