(** * Counted memory effect-table construction

    This mirror connects graph edge collection, stable deduplication and each indexed effect row.
    For example, a repeated edge is collected twice and its effect row is built once.
    Builds on: memory distinctness, effect rows and result-index observers. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore.
From Galois.Views Require Import ViewsGraph ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryWalk AnalysesAuditMemoryDistinct
  AnalysesAuditMemoryEffects AnalysesAuditMemoryIndex.
Import List.ListNotations.

Inductive audit_memory_edges_event (N E OE : Type) : Type :=
  | AuditMemoryEdgesCase (remaining : list N)
  | AuditMemoryEdgesOut (node : N) (edges : list E) (events : list OE).

Arguments AuditMemoryEdgesCase {N E OE} _.
Arguments AuditMemoryEdgesOut {N E OE} _ _ _.

(** Preserve each actual graph callback and the source [flat_map] concatenation order. *)
Fixpoint audit_memory_edges {N E OE} (out : N -> list E * list OE) (nodes : list N)
    : list E * list (audit_memory_edges_event N E OE) :=
  match nodes with
  | [] => ([], [AuditMemoryEdgesCase nodes])
  | n :: rest =>
      let '(edges, oe) := out n in
      let '(tail, te) := audit_memory_edges out rest in
      (edges ++ tail, [AuditMemoryEdgesCase nodes; AuditMemoryEdgesOut n edges oe] ++ te)
  end.

Inductive audit_memory_row_event (E T FE : Type) : Type :=
  | AuditMemoryEffectsCallback (edge : E) (effects : list (memory_effect T)) (events : list FE)
  | AuditMemoryRowBuild (events : list (audit_memory_effect_event T)).

Arguments AuditMemoryEffectsCallback {E T FE} _ _ _.
Arguments AuditMemoryRowBuild {E T FE} _.

(** The row callback composes the actual client effect list and tail-first numeric index builder. *)
Definition audit_memory_effect_row {E T FE} (effects : E -> list (memory_effect T) * list FE)
    (edge : E) : Map.t nat (memory_effect T) * list (audit_memory_row_event E T FE) :=
  let '(items, fe) := effects edge in
  let '(row, re) := audit_memory_effects_from 0 items in
  (row, [AuditMemoryEffectsCallback edge items fe; AuditMemoryRowBuild re]).

Inductive audit_memory_table_event (N E T CE OE FE : Type) : Type :=
  | AuditMemoryTableEdges (events : list (audit_memory_edges_event N E OE))
  | AuditMemoryTableDistinct (events : list (audit_memory_distinct_event E CE))
  | AuditMemoryTableIndex
      (events : list (audit_memory_index_event E (Map.t nat (memory_effect T)) CE
        (audit_memory_row_event E T FE))).

Arguments AuditMemoryTableEdges {N E T CE OE FE} _.
Arguments AuditMemoryTableDistinct {N E T CE OE FE} _.
Arguments AuditMemoryTableIndex {N E T CE OE FE} _.

(** The same actual edge list and deduplicated output flow into the final tail-first index. *)
Definition audit_memory_effect_table {N E T CE OE FE}
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (effects : E -> list (memory_effect T) * list FE) (nodes : list N)
    : Map.t E (Map.t nat (memory_effect T)) * list (audit_memory_table_event N E T CE OE FE) :=
  let '(edges, oe) := audit_memory_edges out nodes in
  let '(unique, de) := audit_memory_distinct edge_enc edges in
  let '(table, ie) := audit_memory_result_index edge_enc (audit_memory_effect_row effects) unique in
  (table, [AuditMemoryTableEdges oe; AuditMemoryTableDistinct de; AuditMemoryTableIndex ie]).

(** Matching edge encoders, outgoing edges and effects recover the original indexed effect
    table, including duplicate behavior. *)
Definition audit_memory_effect_table_erases_statement : Prop :=
  forall N E T CE OE FE (EE : encoding E) (g : Graph.t N E)
      (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (effects : E -> list (memory_effect T) * list FE) (original : E -> list (memory_effect T)),
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (effects e) = original e) ->
    fst (audit_memory_effect_table edge_enc out effects (Graph.nodes g)) =
      memory_walk_effect_table EE g original.

(** * Original-input phase budgets *)

Fixpoint audit_memory_edges_work {N E OE} (out_work : list OE -> nat)
    (events : list (audit_memory_edges_event N E OE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoryEdgesCase _ :: rest => 1 + audit_memory_edges_work out_work rest
  | AuditMemoryEdgesOut _ edges child :: rest =>
      1 + length edges + out_work child + audit_memory_edges_work out_work rest
  end.

Fixpoint audit_memory_edges_budget {N E OE} (out : N -> list E * list OE)
    (out_work : list OE -> nat) (nodes : list N) : nat :=
  match nodes with
  | [] => 1
  | node :: rest => 2 + length (fst (out node)) + out_work (snd (out node)) +
      audit_memory_edges_budget out out_work rest
  end.

Fixpoint audit_memory_row_work {E T FE} (effect_work : list FE -> nat)
    (events : list (audit_memory_row_event E T FE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoryEffectsCallback _ _ child :: rest => 1 + effect_work child +
      audit_memory_row_work effect_work rest
  | AuditMemoryRowBuild child :: rest => 1 + audit_memory_effect_events_work child +
      audit_memory_row_work effect_work rest
  end.

Fixpoint audit_memory_table_work {N E T CE OE FE} (edge_work : list CE -> nat)
    (out_work : list OE -> nat) (effect_work : list FE -> nat)
    (events : list (audit_memory_table_event N E T CE OE FE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoryTableEdges child :: rest => 1 + audit_memory_edges_work out_work child +
      audit_memory_table_work edge_work out_work effect_work rest
  | AuditMemoryTableDistinct child :: rest => 1 + audit_memory_distinct_work edge_work child +
      audit_memory_table_work edge_work out_work effect_work rest
  | AuditMemoryTableIndex child :: rest =>
      1 + audit_memory_index_work edge_work (audit_memory_row_work effect_work) child +
      audit_memory_table_work edge_work out_work effect_work rest
  end.

Definition audit_memory_table_budget {N E T CE OE FE}
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (effects : E -> list (memory_effect T) * list FE) (nodes : list N)
    (edge_work : list CE -> nat) (out_work : list OE -> nat) (effect_work : list FE -> nat) : nat :=
  let edges := fst (audit_memory_edges out nodes) in
  let unique := fst (audit_memory_distinct edge_enc edges) in
  3 + audit_memory_edges_budget out out_work nodes + audit_memory_distinct_budget edge_enc
    edge_work edges +
    audit_memory_index_budget edge_enc (audit_memory_effect_row effects) edge_work
      (audit_memory_row_work effect_work) unique.

(** Indexed effect-table source work is bounded by the edge traversal, distinctness and
    row-index budgets. *)
Definition audit_memory_effect_table_source_bound_statement : Prop :=
  forall N E T CE OE FE (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (effects : E -> list (memory_effect T) * list FE) nodes edge_work out_work effect_work,
    audit_memory_table_work edge_work out_work effect_work
      (snd (audit_memory_effect_table edge_enc out effects nodes)) <=
    audit_memory_table_budget edge_enc out effects nodes edge_work out_work effect_work.
