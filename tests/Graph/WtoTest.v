(** * Weak topological order observations

    The fixtures exercise production, independent checking and rank projection.
    For example, the nested graph retains its inner header at vertex two.

    Groups:
    - ProducerTests: the orders that the producer builds from the fixtures.
    - CheckerTests: the orders that the independent checker accepts and rejects.
    - RankTests: the ranks and enclosing heads of a built order.
    - EdgeScanTests: the edge scan over ranked and unranked vertices.
    - RootTests: the candidate roots that a check accepts.
    - CoverageTests: the length and membership coverage of a candidate.
    - WideKeyTests: candidate vertices and edges beyond the graph's listed vertices.
    - ParallelEdgeTests: candidates for a graph with parallel edges.
    - StaleCacheTests: counted rebuilding with stale cached counts.

    Builds on: graph fixtures, preparation and weak topological orders. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph WtoSig Wto.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.

(** * Fixtures *)

(** Each fixture graph with its roots and its candidate order. *)
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

(** A nested-loop graph with a second inner cycle, which the scoped shortcut must expand. *)
Definition scoped_nested_graph := fixture_graph [1; 2; 3; 4; 5; 6]
  [(1, 2); (2, 3); (3, 4); (4, 3); (4, 5); (5, 2); (5, 6)].

(** * Producer *)

Module ProducerTests.

  Local Open Scope positive_scope.

  (** The producer builds an order that the checker accepts for every fixture. *)
  Example every_fixture_producer_output_is_accepted :
    forallb (fun '(g, roots, _) => let p := DigraphCode.prepare g in
      WtoCode.check p roots (WtoCode.build p roots)) fixture_family = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The nested-loop fixture builds its fixture order from root 1. *)
  Example nested_loops_build_fixture_order :
    WtoCode.build (DigraphCode.prepare NestedLoop.graph) [1] = NestedLoop.order.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Nested loops in the scoped graph build the order that expands the inner cycle. *)
  Example scoped_nested_loops_build_expected_order :
    WtoCode.build (DigraphCode.prepare scoped_nested_graph) [1] =
      WVertex 1 (WLoop 2 (WLoop 3 (WVertex 4 WNil) (WVertex 5 WNil)) (WVertex 6 WNil)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The irreducible graph builds its fixture order from root 1. *)
  Example irreducible_graph_builds_fixture_order :
    WtoCode.build (DigraphCode.prepare Irreducible.graph) [1] = Irreducible.order.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A path builds its fixture order from root 1. *)
  Example path_builds_fixture_order :
    WtoCode.build (DigraphCode.prepare Line.graph) [1] = Line.order.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop builds a loop on its only vertex. *)
  Example self_loop_builds_loop_on_itself :
    WtoCode.build (DigraphCode.prepare SelfLoop.graph) [1] = WLoop 1 WNil WNil.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty graph with no roots builds the empty order. *)
  Example empty_graph_builds_empty_order :
    WtoCode.build (DigraphCode.prepare EmptyGraph.graph) [] = WNil.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Three levels of loops and a separate cycle give the expected nested order. *)
  Definition depth_three_graph := fixture_graph [1; 2; 3; 4; 5; 6; 7]
    [(1, 2); (1, 6); (2, 3); (3, 2); (3, 4); (4, 3); (4, 5); (5, 4);
     (6, 7); (7, 6)].

  Example three_levels_of_loops_build_nested_order :
    WtoCode.build (DigraphCode.prepare depth_three_graph) [1] =
      WVertex 1 (WLoop 6 (WVertex 7 WNil)
        (WLoop 2 (WLoop 3 (WLoop 4 (WVertex 5 WNil) WNil) WNil) WNil)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A cycle entered at two vertices builds a loop headed by the vertex that is listed first. *)
  Example multi_entry_cycle_builds_loop_from_first_head :
    WtoCode.build (DigraphCode.prepare Irreducible.graph) [3; 2] =
      WLoop 3 (WVertex 2 WNil) WNil.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ProducerTests.

(** * Checker *)

Module CheckerTests.

  Local Open Scope positive_scope.

  (** The checker accepts the fixture order of every fixture graph. *)
  Example every_fixture_order_is_accepted :
    forallb (fun '(g, roots, candidate) =>
      WtoCode.check (DigraphCode.prepare g) roots candidate) fixture_family = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The checker accepts the nested order that the scoped shortcut builds. *)
  Example scoped_nested_order_is_accepted :
    let g := DigraphCode.prepare scoped_nested_graph in
    WtoCode.check g [1] (WtoCode.build g [1]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order that leaves out a reachable vertex is rejected. *)
  Example rejects_order_missing_a_vertex :
    WtoCode.check (DigraphCode.prepare Line.graph) [1]
      (WVertex 1 (WVertex 2 (WVertex 3 WNil))) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order that does not place the target of an edge is rejected. *)
  Example rejects_order_missing_an_edge_target :
    WtoCode.check (DigraphCode.prepare Unreachable.graph) [1]
      (WVertex 1 (WVertex 2 (WVertex 4 WNil))) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A ranked source without its successor in the order is rejected. *)
  Example rejects_source_without_its_successor :
    WtoCode.check (DigraphCode.prepare Unreachable.graph) [2]
      (WVertex 2 (WVertex 3 WNil)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order that lists a vertex twice is rejected. *)
  Example rejects_duplicate_vertex :
    WtoCode.check (DigraphCode.prepare Singleton.graph) [1]
      (WVertex 1 (WVertex 1 WNil)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order that places an edge's target before its source is rejected. *)
  Example rejects_backward_edge :
    WtoCode.check (DigraphCode.prepare Line.graph) [1]
      (WVertex 1 (WVertex 3 (WVertex 2 (WVertex 4 WNil)))) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop that has no loop header in the order is rejected. *)
  Example rejects_self_loop_without_header :
    WtoCode.check (DigraphCode.prepare SelfLoop.graph) [1] (WVertex 1 WNil) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order that names a vertex outside the graph is rejected. *)
  Example rejects_unknown_vertex :
    WtoCode.check (DigraphCode.prepare Singleton.graph) [1]
      (WVertex 1 (WVertex 9 WNil)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order that names a vertex that no root reaches is rejected. *)
  Example rejects_unreachable_vertex :
    WtoCode.check (DigraphCode.prepare Unreachable.graph) [1]
      (WVertex 1 (WVertex 2 (WVertex 3 (WVertex 4 (WVertex 5 WNil))))) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An inner loop head that is already closed when its vertices arrive is rejected. *)
  Example rejects_closed_inner_head :
    WtoCode.check (DigraphCode.prepare NestedLoop.graph) [1]
      (WLoop 1 (WLoop 2 WNil (WVertex 3 (WVertex 4 WNil))) WNil) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Parallel edges into a headed loop are accepted by its loop order. *)
  Definition parallel_graph := fixture_graph [1; 2] [(1, 2); (1, 2); (2, 1)].

  Example headed_parallel_edges_are_accepted :
    WtoCode.check (DigraphCode.prepare parallel_graph) [1]
      (WLoop 1 (WVertex 2 WNil) WNil) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Parallel edges into an unheaded cycle are rejected. *)
  Example rejects_unheaded_parallel_edges :
    WtoCode.check (DigraphCode.prepare parallel_graph) [1]
      (WVertex 1 (WVertex 2 WNil)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The empty candidate is accepted for the empty graph. *)
  Example empty_candidate_is_accepted_for_empty_graph :
    WtoCode.check (DigraphCode.prepare EmptyGraph.graph) [] WNil = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CheckerTests.

(** * Ranks *)

Module RankTests.

  Local Open Scope positive_scope.

  (** The ranks of the nested order follow its position, and an absent vertex has none. *)
  Example ranks_follow_nested_order :
    let w := WtoCode.build (DigraphCode.prepare NestedLoop.graph) [1] in
    map (fun v => trie_get v (WtoCode.ranks w)) [1; 2; 3; 4; 99] =
      [Some 1; Some 2; Some 3; Some 4; None].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each vertex of the nested order has the stack of heads that enclose it. *)
  Example enclosing_heads_follow_nesting :
    let w := WtoCode.build (DigraphCode.prepare NestedLoop.graph) [1] in
    map (fun v => match trie_get v (wto_positions (wto_annotate [] w)) with
      | Some (_, stack) => Some stack
      | None => None
      end) [1; 2; 3; 4; 99] =
      [Some [1]; Some [2; 1]; Some [2; 1]; Some [1]; None].
  Proof.
    vm_compute. reflexivity.
  Qed.

End RankTests.

(** * Edge scan *)

Module EdgeScanTests.

  Local Open Scope positive_scope.

  (** A sink that has no rank passes the edge scan. *)
  Example unranked_sink_passes_edge_scan :
    wto_edges_ok Unreachable.graph Empty Empty [5] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A source that has no rank fails the edge scan. *)
  Example unranked_source_fails_edge_scan :
    wto_edges_ok Unreachable.graph Empty Empty [1] = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EdgeScanTests.

(** * Roots *)

Module RootTests.

  Local Open Scope positive_scope.

  (** A second root accepts the order that starts from it. *)
  Example second_root_accepts_its_order :
    WtoCode.check (DigraphCode.prepare Diamond.graph) [2]
      (WVertex 2 (WVertex 4 WNil)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order that stops at the root is rejected, since the diamond has more reachable vertices. *)
  Example scoped_order_is_rejected_as_unrestricted :
    WtoCode.check (DigraphCode.prepare Diamond.graph) [1] (WVertex 1 WNil) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RootTests.

(** * Coverage *)

Module CoverageTests.

  Local Open Scope positive_scope.

  (** A repeated root does not change the reachable vertices that the order must cover. *)
  Definition isolated_coverage_graph := fixture_graph [1; 2; 3] [].

  Example repeated_roots_accept_unique_reachable_vertices :
    WtoCode.check (DigraphCode.prepare isolated_coverage_graph) [1; 1; 2]
      (WVertex 1 (WVertex 2 WNil)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order of the right length that names the wrong vertices is rejected. *)
  Example equal_length_with_wrong_vertices_is_rejected :
    WtoCode.check (DigraphCode.prepare isolated_coverage_graph) [1; 2]
      (WVertex 1 (WVertex 3 WNil)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A longer order is rejected even when it contains every reachable vertex. *)
  Example longer_order_is_rejected :
    WtoCode.check (DigraphCode.prepare isolated_coverage_graph) [1; 2]
      (WVertex 1 (WVertex 2 (WVertex 3 WNil))) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CoverageTests.

(** * Wide keys *)

Module WideKeyTests.

  Local Open Scope positive_scope.

  (** A wide vertex that no root reaches does not block a narrow order. *)
  Definition wide_unlisted_graph := fixture_graph [1; 2] [(2, 1024)].

  Example narrow_order_ignores_wide_unreachable_edge :
    WtoCode.check (DigraphCode.prepare wide_unlisted_graph) [1] (WVertex 1 WNil) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order that names the wide vertex 1024, which the graph does not list, is rejected. *)
  Example rejects_wide_unlisted_vertex :
    WtoCode.check (DigraphCode.prepare wide_unlisted_graph) [1]
      (WVertex 1 (WVertex 1024 WNil)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End WideKeyTests.

(** * Stale caches *)

Module StaleCacheTests.

  Local Open Scope positive_scope.

  (** A stale cached count does not change the check, which ignores rows of unlisted sources. *)
  Definition stale_count_graph :=
    Prepared (Digraph [1; 2] (PTrieCode.set 3 [4] (PTrieCode.set 1 [2] Empty)))
      Empty BinNums.N0 BinNums.N0.

  Example stale_counts_do_not_change_check :
    WtoCode.check stale_count_graph [1] (WVertex 1 (WVertex 2 WNil)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A stale cached count does not change the built order. *)
  Example stale_counts_do_not_change_build :
    WtoCode.build stale_count_graph [1] = WVertex 1 (WVertex 2 WNil).
  Proof.
    vm_compute. reflexivity.
  Qed.

End StaleCacheTests.
