(** * Dense expression-universe source

    This model captures edge enumeration, generation, set construction and set enumeration.
    For example, duplicate generated expressions retain separate insertion receipts.
    Builds on: AnalysesAuditSegUniverse and the shared collection source models. *)
From Stdlib Require Import List PArith Arith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet
  CollectionsAuditElements.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSegBuilder
  AnalysesAuditSegUniverse.
Import List.ListNotations.

(** * Dense expression-universe source *)

(** The returned list and events are from one actual universe construction. *)
Definition audit_dense_universe {N E U B} (g : Graph.t N E)
    (cb : audit_seg_build_callbacks N E U B) : list U * list (audit_seg_universe_event N E U B) :=
  let '(edges, edge_events) := audit_seg_universe_edges cb (Graph.nodes g) in
  let '(values, gen_events) := audit_seg_universe_gen cb edges in
  let '(set, set_events) := audit_finset_of_list (seg_build_expr_encode cb) values in
  let '(rows, element_events) := audit_map_elements set in
  (map fst rows, edge_events ++ gen_events ++ map SegUniverseSet set_events ++
    map SegUniverseElements element_events ++ [SegUniverseAppend (length rows)]).

(** The original-input budget covers traversal and encoded output widths. *)
Definition audit_dense_universe_budget {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) : nat :=
  let g := cfg (gkview gk) in
  let edges := edges_of g in
  let values := flat_map (gen gk) edges in
  let width := fold_right (fun x total => Pos.size_nat (encode EU x) + total) 0 values in
  (N.to_nat 65536%N) *
    Nat.pow (Nat.succ (length (Graph.nodes g) + length edges + length values + width)) 8.

(** A captured universe has the source result and an input-derived bound plus actual callbacks. *)
Definition audit_dense_universe_source_statement : Prop :=
  forall (S O N E U C B : Type) (EU : encoding U) (gk : genkill_view S O N E U C)
    (cb : audit_seg_build_callbacks N E U B) (weight : B -> nat)
    out_source gen_source expr_source out_budget gen_budget expr_budget,
    (forall n, fst (seg_build_out cb n) = Graph.out (cfg (gkview gk)) n) ->
    (forall e, fst (seg_build_gen cb e) = gen gk e) ->
    (forall x, fst (seg_build_expr_encode cb x) = encode EU x) ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source gen_budget ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      expr_budget ->
    let '(out, events) := audit_dense_universe (cfg (gkview gk)) cb in
    out = expr_universe EU gk /\
      audit_seg_universe_work weight events <= audit_dense_universe_budget EU gk +
        fold_right (fun event n => audit_seg_universe_event_budget out_budget gen_budget
          expr_budget event + n) 0 events.
