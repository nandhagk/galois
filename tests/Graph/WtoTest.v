(** * Weak topological order observations

    The fixtures exercise production, independent checking and rank projection.
    For example, the nested graph retains its inner header at vertex two.
    Builds on: graph fixtures, preparation and weak topological orders. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph WtoSig Wto.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition fixture_family :=
  [(Line.graph, Line.roots, Line.order); (Diamond.graph, Diamond.roots, Diamond.order);
   (JoinLoop.graph, JoinLoop.roots, JoinLoop.order);
   (NestedLoop.graph, NestedLoop.roots, NestedLoop.order);
   (TwoEntry.graph, TwoEntry.roots, TwoEntry.order);
   (SelfLoop.graph, SelfLoop.roots, SelfLoop.order);
   (Irreducible.graph, Irreducible.roots, Irreducible.order);
   (EmptyGraph.graph, EmptyGraph.roots, EmptyGraph.order);
   (Singleton.graph, Singleton.roots, Singleton.order);
   (Unreachable.graph, Unreachable.roots, Unreachable.order)].

Example every_candidate_accepts :
  forallb (fun '(g, roots, candidate) =>
    WtoCode.check (DigraphCode.prepare g) roots candidate) fixture_family = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example every_producer_accepts :
  forallb (fun '(g, roots, _) => let p := DigraphCode.prepare g in
    WtoCode.check p roots (WtoCode.build p roots)) fixture_family = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_order_agrees :
  WtoCode.build (DigraphCode.prepare NestedLoop.graph) [1] = NestedLoop.order.
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_order_agrees :
  WtoCode.build (DigraphCode.prepare Irreducible.graph) [1] = Irreducible.order.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_order_agrees :
  WtoCode.build (DigraphCode.prepare Line.graph) [1] = Line.order.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_order_agrees :
  WtoCode.build (DigraphCode.prepare SelfLoop.graph) [1] = WLoop 1 WNil WNil.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_order : WtoCode.build (DigraphCode.prepare EmptyGraph.graph) [] = WNil.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_ranks :
  let w := WtoCode.build (DigraphCode.prepare NestedLoop.graph) [1] in
  map (fun v => trie_get v (WtoCode.ranks w)) [1; 2; 3; 4; 99] =
    [Some 1; Some 2; Some 3; Some 4; None].
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_enclosing_heads :
  let w := WtoCode.build (DigraphCode.prepare NestedLoop.graph) [1] in
  map (fun v => match trie_get v (wto_positions (wto_annotate [] w)) with
    | Some (_, stack) => Some stack
    | None => None
    end) [1; 2; 3; 4; 99] =
    [Some [1]; Some [2; 1]; Some [2; 1]; Some [1]; None].
Proof.
  vm_compute. reflexivity.
Qed.

Definition depth_three := fixture_graph [1; 2; 3; 4; 5; 6; 7]
  [(1, 2); (1, 6); (2, 3); (3, 2); (3, 4); (4, 3); (4, 5); (5, 4);
   (6, 7); (7, 6)].

Example depth_three_and_separate_component :
  WtoCode.build (DigraphCode.prepare depth_three) [1] =
    WVertex 1 (WLoop 6 (WVertex 7 WNil)
      (WLoop 2 (WLoop 3 (WLoop 4 (WVertex 5 WNil) WNil) WNil) WNil)).
Proof.
  vm_compute. reflexivity.
Qed.

Example cycle_with_multiple_entries :
  WtoCode.build (DigraphCode.prepare Irreducible.graph) [3; 2] =
    WLoop 3 (WVertex 2 WNil) WNil.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_missing_node :
  WtoCode.check (DigraphCode.prepare Line.graph) [1]
    (WVertex 1 (WVertex 2 (WVertex 3 WNil))) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_duplicate :
  WtoCode.check (DigraphCode.prepare Singleton.graph) [1]
    (WVertex 1 (WVertex 1 WNil)) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_backward_edge :
  WtoCode.check (DigraphCode.prepare Line.graph) [1]
    (WVertex 1 (WVertex 3 (WVertex 2 (WVertex 4 WNil)))) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unheaded_self_loop :
  WtoCode.check (DigraphCode.prepare SelfLoop.graph) [1] (WVertex 1 WNil) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unknown_id :
  WtoCode.check (DigraphCode.prepare Singleton.graph) [1]
    (WVertex 1 (WVertex 9 WNil)) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unreachable_node :
  WtoCode.check (DigraphCode.prepare Unreachable.graph) [1]
    (WVertex 1 (WVertex 2 (WVertex 3 (WVertex 4 (WVertex 5 WNil))))) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_alternative_roots :
  WtoCode.check (DigraphCode.prepare Diamond.graph) [2]
    (WVertex 2 (WVertex 4 WNil)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_scoped_coverage_as_unrestricted :
  WtoCode.check (DigraphCode.prepare Diamond.graph) [1] (WVertex 1 WNil) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_already_closed_inner_head :
  WtoCode.check (DigraphCode.prepare NestedLoop.graph) [1]
    (WLoop 1 (WLoop 2 WNil (WVertex 3 (WVertex 4 WNil))) WNil) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** The old unmatched-open and unmatched-close candidates have no structural [wto] value.
    GraphCheckWtoTest expected false for both malformed token lists.
    The old ignores_unknown_root test expected true for roots [9] and an empty candidate.
    The new reach predicate includes unlisted roots, so this check returns false.
    GraphHierTest expected an empty hierarchy for roots [99; 99] in the empty graph.
    The new reach predicate includes that root, so the producer emits vertex 99. *)

Definition parallel_graph := fixture_graph [1; 2] [(1, 2); (1, 2); (2, 1)].

Example accepts_headed_parallel_edges :
  WtoCode.check (DigraphCode.prepare parallel_graph) [1]
    (WLoop 1 (WVertex 2 WNil) WNil) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unheaded_parallel_edges :
  WtoCode.check (DigraphCode.prepare parallel_graph) [1]
    (WVertex 1 (WVertex 2 WNil)) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_candidate_boundary :
  WtoCode.check (DigraphCode.prepare EmptyGraph.graph) [] WNil = true.
Proof.
  vm_compute. reflexivity.
Qed.
