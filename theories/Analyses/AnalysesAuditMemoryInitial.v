(** * Counted memory preparation

    This candidate connects the actual graph preparation and indexed effect-table phases.
    For example, a graph with no listed nodes still prepares an empty effect table.
    Builds on: G4 memory semantics and the composed memory-table observer. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryState
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryTable.
Import List.ListNotations.

Record audit_memory_initial_events (N E T CE OE FE PE : Type) : Type := AuditMemoryInitialEvents {
  audit_memory_initial_prepare : list PE;
  audit_memory_initial_table : list (audit_memory_table_event N E T CE OE FE)
}.

Arguments AuditMemoryInitialEvents {N E T CE OE FE PE} _ _.
Arguments audit_memory_initial_prepare {N E T CE OE FE PE} _.
Arguments audit_memory_initial_table {N E T CE OE FE PE} _.

(** The graph and effect-table phases use the exact intermediate values retained in the state. *)
Definition audit_memory_initial {N E T CE OE FE PE} (EN : encoding N)
    (g : Graph.t N E) (original_effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (effects : E -> list (memory_effect T) * list FE) (graph_prepare : unit -> prepared EN g *
      list PE)
    : memo_state EN g original_effects mg * audit_memory_initial_events N E T CE OE FE PE :=
  let '(prep, pe) := graph_prepare tt in
  let '(table, te) := audit_memory_effect_table edge_enc out effects (Graph.nodes g) in
  (@MemoState N E T EN g original_effects mg prep table Map.empty, AuditMemoryInitialEvents pe te).

(** Matching preparation and callbacks recover the original initial memo state. *)
Definition audit_memory_initial_erases_statement : Prop :=
  forall N E T CE OE FE PE (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (original : E -> list (memory_effect T)) (mg : memory_graph N E)
      (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (effects : E -> list (memory_effect T) * list FE) (graph_prepare : unit -> prepared EN g *
        list PE),
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (effects e) = original e) ->
    fst (graph_prepare tt) = prepare EN g ->
    fst (audit_memory_initial EN g original mg edge_enc out effects graph_prepare) =
      memo_initial EN EE g original mg.

(** Initialization source work is bounded by the captured graph preparation charge and the
    effect-table budget. *)
Definition audit_memory_initial_source_bound_statement : Prop :=
  forall N E T CE OE FE PE (EN : encoding N) (g : Graph.t N E)
      (original : E -> list (memory_effect T)) (mg : memory_graph N E)
      (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (effects : E -> list (memory_effect T) * list FE) (graph_prepare : unit -> prepared EN g *
        list PE)
      graph_work edge_work out_work effect_work,
    let trace := snd (audit_memory_initial EN g original mg edge_enc out effects graph_prepare) in
    2 + graph_work (audit_memory_initial_prepare trace) +
      audit_memory_table_work edge_work out_work effect_work (audit_memory_initial_table trace) <=
    2 + graph_work (snd (graph_prepare tt)) +
      audit_memory_table_budget edge_enc out effects (Graph.nodes g) edge_work out_work effect_work.
