(** * Memory initialization adequacy

    Initialization retains the prepared graph and the effect table produced by its callbacks.
    For example, an empty graph initializes an empty completed-entry cache.
    Builds on: memory initialization and effect-table adequacy. *)

From Stdlib Require Import List Lia.
From Galois.Graph Require Import GraphCore.
From Galois.Analyses Require Import AnalysesAuditMemoryInitial AnalysesAuditMemoryState
  AnalysesAuditMemoryTable AnalysesAuditMemoryTableAdequacy.

(** * Initialization *)

(** Matching preparation and callback observations recover the exact initial state. *)
Theorem audit_memory_initial_erases : audit_memory_initial_erases_statement.
Proof.
  intros N E T CE OE FE PE EN EE g original mg edge_enc out effects graph_prepare
    Hedge Hout Heffects Hprepare.
  pose proof (audit_memory_effect_table_erases N E T CE OE FE EE g edge_enc out effects
    original Hedge Hout Heffects) as Htable.
  unfold audit_memory_initial.
  destruct (graph_prepare tt) as [prep preparation].
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes g))
    as [table rows].
  cbn in Hprepare, Htable |- *.
  rewrite Hprepare, Htable; reflexivity.
Qed.

(** Initialization pays the same preparation trace and the concrete effect-table budget. *)
Theorem audit_memory_initial_source_bound : audit_memory_initial_source_bound_statement.
Proof.
  intros N E T CE OE FE PE EN g original mg edge_enc out effects graph_prepare
    graph_work edge_work out_work effect_work.
  pose proof (audit_memory_effect_table_source_bound N E T CE OE FE edge_enc out effects
    (Graph.nodes g) edge_work out_work effect_work) as Htable.
  unfold audit_memory_initial.
  destruct (graph_prepare tt) as [prep preparation].
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes g))
    as [table rows].
  cbn in Htable |- *; lia.
Qed.
