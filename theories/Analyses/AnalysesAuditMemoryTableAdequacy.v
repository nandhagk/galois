(** * Adequacy of counted memory effect tables

    The table composes outgoing edges, stable distinctness and tail-first indexed rows.
    For example, a repeated edge is observed twice but indexed once.
    Builds on: AnalysesAuditMemoryTable and its component adequacy proofs. *)

From Stdlib Require Import List Lia.
From Galois.Collections Require Import CollectionsFinSet.
From Galois.Graph Require Import GraphCore.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesMemoryWalk AnalysesAuditMemoryTable
  AnalysesAuditMemoryDistinct AnalysesAuditMemoryEffects AnalysesAuditMemoryIndex
  AnalysesAuditMemoryDistinctAdequacy AnalysesAuditMemoryEffectsAdequacy
  AnalysesAuditMemoryIndexAdequacy.
Import List.ListNotations.

(** The edge observer returns the flat concatenation of the actual outgoing callbacks. *)
Lemma audit_memory_edges_erases N E OE (out : N -> list E * list OE) nodes :
  fst (audit_memory_edges out nodes) = flat_map (fun n => fst (out n)) nodes.
Proof.
  induction nodes as [|node rest IH].
  - reflexivity.
  - cbn [audit_memory_edges flat_map].
    destruct (out node) as [edges calls].
    destruct (audit_memory_edges out rest) as [tail events].
    cbn in IH |- *; now rewrite IH.
Qed.

(** The edge observer's work equals its budget for the callbacks actually invoked. *)
Lemma audit_memory_edges_work_exact N E OE (out : N -> list E * list OE) work nodes :
  audit_memory_edges_work work (snd (audit_memory_edges out nodes)) =
    audit_memory_edges_budget out work nodes.
Proof.
  induction nodes as [|node rest IH].
  - reflexivity.
  - cbn [audit_memory_edges audit_memory_edges_budget].
    destruct (out node) as [edges calls].
    destruct (audit_memory_edges out rest) as [tail events].
    simpl in *; lia.
Qed.

(** Matching callbacks and codes reproduce the original indexed effect table. *)
Theorem audit_memory_effect_table_erases : audit_memory_effect_table_erases_statement.
Proof.
  intros N E T CE OE FE EE g edge_enc out effects original Henc Hout Heffects.
  unfold audit_memory_effect_table, memory_walk_effect_table.
  pose proof (audit_memory_edges_erases N E OE out (Graph.nodes g)) as Hedges.
  destruct (audit_memory_edges out (Graph.nodes g)) as [edges events].
  cbn in Hedges.
  assert (Hedges_original : edges = edges_of g).
  { rewrite Hedges; unfold edges_of; apply flat_map_ext; intro node; apply Hout. }
  pose proof (audit_memory_distinct_erases E CE edge_enc EE edges
    (fun e _ => Henc e)) as Hdistinct.
  destruct (audit_memory_distinct edge_enc edges) as [unique distinct_events].
  cbn in Hdistinct.
  pose proof (audit_memory_result_index_erases E _ CE _ edge_enc EE
    (audit_memory_effect_row effects) (fun e => memory_walk_effects_from 0 (original e)) unique
    (fun e _ => Henc e)) as Hindex.
  assert (Hrow : forall e, In e unique ->
    fst (audit_memory_effect_row effects e) = memory_walk_effects_from 0 (original e)).
  { intros e Hin; unfold audit_memory_effect_row.
    pose proof (audit_memory_effects_from_erases T 0 (fst (effects e))) as Herase.
    pose proof (Heffects e) as Heffect.
    destruct (effects e) as [items calls]; cbn in Herase, Heffect |- *.
    destruct (audit_memory_effects_from 0 items); cbn in Herase |- *.
    rewrite Herase, Heffect; reflexivity. }
  specialize (Hindex Hrow).
  destruct (audit_memory_result_index edge_enc (audit_memory_effect_row effects) unique)
    as [table index_events].
  cbn in Hindex |- *; rewrite Hindex, Hdistinct, Hedges_original; reflexivity.
Qed.

(** The table work is bounded by the component budgets for the exact intermediate values. *)
Theorem audit_memory_effect_table_source_bound : audit_memory_effect_table_source_bound_statement.
Proof.
  intros N E T CE OE FE edge_enc out effects nodes edge_work out_work effect_work.
  unfold audit_memory_effect_table, audit_memory_table_budget.
  pose proof (audit_memory_edges_work_exact N E OE out out_work nodes) as Hedges.
  destruct (audit_memory_edges out nodes) as [edges events].
  pose proof (audit_memory_distinct_source_bound E CE edge_enc edge_work
    CollectionsFinSet.FinSet.empty edges) as Hdistinct.
  unfold audit_memory_distinct in *.
  cbn [fst snd] in *.
  destruct (audit_memory_distinct_from edge_enc CollectionsFinSet.FinSet.empty edges)
    as [unique distinct_events].
  pose proof (audit_memory_result_index_work_bound E _ CE _ edge_enc
    (audit_memory_effect_row effects) edge_work (audit_memory_row_work effect_work) unique)
    as Hindex.
  destruct (audit_memory_result_index edge_enc (audit_memory_effect_row effects) unique)
    as [table index_events].
  simpl in *; lia.
Qed.
