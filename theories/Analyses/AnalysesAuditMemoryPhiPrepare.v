(** * Memory phi dependency preparation phases

    This candidate preserves the actual intermediate inputs, graph, SCC and flags.
    For example, SCC receives the graph prepared from the same captured input rows.
    Builds on: AnalysesAuditMemoryPhiState and the graph preparation and SCC APIs. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryPhiState.
Import List.ListNotations.

(** * Dependency preparation sequence *)

Inductive audit_phi_prepare_event {N E T} (EN : encoding N) : Type :=
  | AuditPhiInputs (graph : Graph.t N E) (effects : E -> list (memory_effect T))
      (memory : memory_graph N E) (rows : Map.t N (list (option E * memory_version N E)))
  | AuditPhiGraph (rows : Map.t N (list (option E * memory_version N E)))
      (dep : Graph.t N (phi_dependency_edge N E))
  | AuditPhiPrepared (dep : Graph.t N (phi_dependency_edge N E)) (index : prepared EN dep)
  | AuditPhiScc (result : scc_result N)
  | AuditPhiCycles (result : FinSet.t N).

Arguments AuditPhiInputs {N E T EN} _ _ _ _.
Arguments AuditPhiGraph {N E T EN} _ _.
Arguments AuditPhiPrepared {N E T EN} _ _.
Arguments AuditPhiScc {N E T EN} _.
Arguments AuditPhiCycles {N E T EN} _.

(** The five source phases retain the exact common intermediate values and returned index. *)
Definition audit_phi_prepare_dependencies {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    : phi_dependency_index (E := E) EN * list (audit_phi_prepare_event (T := T) EN) :=
  let inputs := phi_input_rows EN EE g effects mg in
  let dep := phi_dependency_graph_from_inputs EN mg inputs in
  let prep := prepare EN dep in
  let components := scc prep in
  let cycles := phi_cycle_flags EN dep prep components in
  (PhiDependencyIndex inputs dep prep components cycles,
    [AuditPhiInputs g effects mg inputs; AuditPhiGraph inputs dep; AuditPhiPrepared dep prep;
     AuditPhiScc components; AuditPhiCycles cycles]).

(** The counted preparation yields the same inputs, dependency graph, SCCs and cycle flags. *)
Definition audit_phi_prepare_dependencies_erases_statement : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E) effects mg,
    fst (@audit_phi_prepare_dependencies N E T EN EE g effects mg) =
      phi_prepare_dependencies EN EE g effects mg.

(** Phi dependency preparation records exactly five phase events. *)
Definition audit_phi_prepare_phase_count_statement : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E) effects mg,
    length (snd (@audit_phi_prepare_dependencies N E T EN EE g effects mg)) = 5.
