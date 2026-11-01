(** * SEG expression-universe source

    Membership traverses the original expression universe at its actual callbacks.
    For example, a generated expression is collected before the membership test.
    Builds on: finite sets, graph views and SEG builder callbacks. *)
From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSeg AnalysesAuditSegBuilder.
Import List.ListNotations.

(** * SEG expression-universe source *)

Inductive audit_seg_universe_event (N E U B : Type) : Type :=
  | SegUniverseCase : nat -> audit_seg_universe_event N E U B
  | SegUniverseOut : N -> list E -> list B -> audit_seg_universe_event N E U B
  | SegUniverseGen : E -> list U -> list B -> audit_seg_universe_event N E U B
  | SegUniverseSet : audit_set_event U B -> audit_seg_universe_event N E U B
  | SegUniverseElements : audit_elements_event (U * unit) -> audit_seg_universe_event N E U B
  | SegUniverseAppend : nat -> audit_seg_universe_event N E U B.

Arguments SegUniverseCase {N E U B} _.

Arguments SegUniverseOut {N E U B} _ _ _.

Arguments SegUniverseGen {N E U B} _ _ _.

Arguments SegUniverseSet {N E U B} _.

Arguments SegUniverseElements {N E U B} _.

Arguments SegUniverseAppend {N E U B} _.

Fixpoint audit_seg_universe_edges {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (nodes : list N)
    : list E * list (audit_seg_universe_event N E U B) :=
  match nodes with
  | [] => ([], [SegUniverseCase 0])
  | n :: rest => let '(edges, body) := seg_build_out cb n in
    let '(later, events) := audit_seg_universe_edges cb rest in
    (edges ++ later, SegUniverseOut n edges body :: events ++ [SegUniverseAppend (length edges)])
  end.

Fixpoint audit_seg_universe_gen {N E U B} (cb : audit_seg_build_callbacks N E U B) (edges : list E)
    : list U * list (audit_seg_universe_event N E U B) :=
  match edges with
  | [] => ([], [SegUniverseCase 1])
  | e :: rest => let '(values, body) := seg_build_gen cb e in
    let '(later, events) := audit_seg_universe_gen cb rest in
    (values ++ later, SegUniverseGen e values body :: events ++
      [SegUniverseAppend (length values)])
  end.

Definition audit_seg_universe_counted {N E U B} (g : Graph.t N E)
    (cb : audit_seg_build_callbacks N E U B) (u : U)
    : bool * list (audit_seg_universe_event N E U B) :=
  let '(edges, out_calls) := audit_seg_universe_edges cb (Graph.nodes g) in
  let '(values, gen_calls) := audit_seg_universe_gen cb edges in
  let '(set, set_calls) := audit_finset_of_list (seg_build_expr_encode cb) values in
  let '(rows, element_calls) := audit_map_elements set in
  let universe := map fst rows in
  let '(again, again_calls) := audit_finset_of_list (seg_build_expr_encode cb) universe in
  let '(found, mem_calls) := audit_finset_mem (seg_build_expr_encode cb) u again in
  (found, out_calls ++ gen_calls ++ map SegUniverseSet set_calls ++
    map SegUniverseElements element_calls ++ [SegUniverseAppend (length rows)] ++
    map SegUniverseSet again_calls ++ map SegUniverseSet mem_calls).

Definition audit_seg_universe_event_work {N E U B} (weight : B -> nat)
    (event : audit_seg_universe_event N E U B) : nat :=
  let body := fun xs => fold_right (fun x total => weight x + total) 0 xs in
  64 + match event with
  | SegUniverseCase _ => 0
  | SegUniverseOut _ _ xs | SegUniverseGen _ _ xs => body xs
  | SegUniverseSet call => audit_finset_source_work body [call]
  | SegUniverseElements call => audit_elements_frame_work call
  | SegUniverseAppend size => size
  end.

Definition audit_seg_universe_work {N E U B} (weight : B -> nat)
    (events : list (audit_seg_universe_event N E U B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event total => audit_seg_universe_event_work weight event + total) 0 events.

Definition audit_seg_universe_event_budget {N E U B} (out_budget : N -> nat) (gen_budget : E -> nat)
    (expr_budget : U -> nat) (event : audit_seg_universe_event N E U B) : nat :=
  match event with
  | SegUniverseOut n _ _ => out_budget n
  | SegUniverseGen e _ _ => gen_budget e
  | SegUniverseSet (AuditSetMem u _ _ _ _ _) | SegUniverseSet (AuditSetAdd u _ _ _ _ _) |
    SegUniverseSet (AuditSetRemove u _ _ _ _ _) => expr_budget u
  | _ => 0
  end.

Definition audit_seg_universe_input_budget {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) : nat :=
  let g := cfg (gkview gk) in let edges := edges_of g in
  let values := u :: flat_map (gen gk) edges in
  let width := fold_right (fun x total => Pos.size_nat (encode EU x) + total) 0 values in
  (N.to_nat 65536%N) *
    Nat.pow (Nat.succ (length (Graph.nodes g) + length edges + length values + width)) 8.

(** Under callback laws, the universe test returns source membership within its input bound. *)
Definition audit_seg_universe_adapted_statement : Prop :=
  forall S O N E U C B (EU : encoding U) (gk : genkill_view S O N E U C)
    (cb : audit_seg_build_callbacks N E U B) u (weight : B -> nat)
    out_source gen_source expr_source out_budget gen_budget expr_budget,
    (forall n, fst (seg_build_out cb n) = Graph.out (cfg (gkview gk)) n) ->
    (forall e, fst (seg_build_gen cb e) = gen gk e) ->
    (forall x, fst (seg_build_expr_encode cb x) = encode EU x) ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source gen_budget ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      expr_budget ->
    let '(found, events) := audit_seg_universe_counted (cfg (gkview gk)) cb u in
    let external := fold_right (fun event total => audit_seg_universe_event_budget out_budget
      gen_budget expr_budget event + total) 0 events in
    found = FinSet.mem EU u (FinSet.of_list EU (expr_universe EU gk)) /\
      audit_seg_universe_work weight events <= audit_seg_universe_input_budget EU gk u + external.
