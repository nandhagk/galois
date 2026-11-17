(** * Dominator certificate observations

    These cases retain parent-map observations and supply independent low-high orders.
    For example, the diamond places its join between its two incoming branches.

    Groups:
    - [CheckTests] Which parent maps and orders the dominator checker accepts.
    - [EdgeRowTests] The edge rows that the fast check builds from a source row.
    - [AncestorTests] Which vertices dominate which.
    - [LowHighTests] The low-high parent maps and their path compression.
    - [ProducerTests] The certificates that the producer builds.
    - [SubtreeSizeTests] The positions and subtree sizes of an order.

    Builds on: graph fixtures, preparation and the dominator code tower. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph DomSig DomProducer Dom.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.

(** * Fixtures *)

(** The parent map that holds the given child-parent pairs. *)
Definition parent_map (pairs : list (positive * positive)) : ptrie positive :=
  fold_right (fun pair acc => PTrieCode.set (fst pair) (snd pair) acc) Empty pairs.

(** * Checker *)

Module CheckTests.

  Local Open Scope positive_scope.

  (** The checker accepts the certificate of a path. *)
  Example accepts_path_certificate :
    DomCode.check (DigraphCode.prepare Line.graph) 1 (parent_map Line.parents) [1; 2; 3; 4] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The checker accepts the certificate of a diamond, given in one valid order. *)
  Example accepts_diamond_certificate :
    DomCode.check (DigraphCode.prepare Diamond.graph) 1
      (parent_map Diamond.parents) [1; 2; 4; 3] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A graph with a dense join accepts its certificate in an unusual valid order. *)
  Definition dense_join_graph := fixture_graph [1; 2; 3; 4; 5; 6; 7]
    [(1, 2); (1, 3); (1, 4); (2, 5); (2, 6); (3, 5); (3, 6); (4, 5); (4, 6);
      (5, 7); (6, 7)].

  Example accepts_dense_join_certificate :
    DomCode.check (DigraphCode.prepare dense_join_graph) 1
      (parent_map [(2, 1); (3, 1); (4, 1); (5, 1); (6, 1); (7, 1)])
      [1; 2; 5; 7; 6; 3; 4] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An order may leave out a source vertex that no path from the root reaches. *)
  Example accepts_order_without_unreachable_source :
    DomCode.check (DigraphCode.prepare Unreachable.graph) 1
      (parent_map Unreachable.parents) [1; 2; 3; 4] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A graph whose vertex 1024 is a successor of 2 but is not listed as a vertex. *)
  Definition wide_graph := fixture_graph [1; 2] [(1, 2); (2, 1024)].

  (** A graph whose subtree of vertex 2 is split by vertex 3 in the order [1; 2; 3; 4]. *)
  Definition split_subtree_graph := fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4)].

  Definition split_subtree_parents := parent_map [(2, 1); (3, 1); (4, 2)].

  Definition split_subtree_order := [1; 2; 3; 4].

  (** Each case is a graph, a parent map and an order that the checker rejects at root 1. *)
  Definition rejected_cases : list (digraph * ptrie positive * list positive) :=
    [ (* The parent of 3 is 1 instead of 2. *)
      (Line.graph, parent_map [(2, 1); (3, 1); (4, 3)], [1; 2; 3; 4]);
      (* The parents of 2 and 3 form a cycle. *)
      (Line.graph, parent_map [(2, 3); (3, 2); (4, 3)], [1; 2; 3; 4]);
      (* There is no binding for vertex 3. *)
      (Line.graph, parent_map [(2, 1); (4, 3)], [1; 2; 3; 4]);
      (* Vertex 9 has a parent but is not in the graph. *)
      (Line.graph, PTrieCode.set 9 1 (parent_map Line.parents), [1; 2; 3; 4]);
      (* The parent map is valid, but the order has no high witness for it. *)
      (Diamond.graph, parent_map Diamond.parents, [1; 2; 3; 4]);
      (* The order lists vertex 2 twice. *)
      (Line.graph, parent_map Line.parents, [1; 2; 2; 3; 4]);
      (* The order repeats a vertex before the parent map is rebuilt. *)
      (Line.graph, parent_map Line.parents, [1; 2; 2; 4]);
      (* The root has a parent, although the order is valid. *)
      (Line.graph, PTrieCode.set 1 4 (parent_map Line.parents), [1; 2; 3; 4]);
      (* The parent key 1024 is not listed in the graph. *)
      (wide_graph, parent_map [(1024, 1)], [1; 1024]);
      (* The parent value 1024 is a wide vertex outside the order. *)
      (wide_graph, parent_map [(2, 1024)], [1; 2]);
      (* The subtree of vertex 2 is not contiguous in the order. *)
      (split_subtree_graph, split_subtree_parents, split_subtree_order) ].

  (** The checker rejects every case of the table. *)
  Example rejects_every_bad_certificate :
    forallb (fun '(g, m, o) => negb (DomCode.check (DigraphCode.prepare g) 1 m o))
      rejected_cases = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The known-vertex check alone accepts the parents of the split subtree. *)
  Example split_subtree_passes_known_check :
    dom_map_check_known (dom_scan (DigraphCode.prepare split_subtree_graph)) 1
      split_subtree_parents split_subtree_order = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The size check rejects the parents of the split subtree. *)
  Example split_subtree_fails_size_check :
    dom_info_sizes_ok split_subtree_parents
      (dom_info_sizes split_subtree_parents split_subtree_order
        (dom_positions split_subtree_order)) split_subtree_order = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CheckTests.

(** * Edge rows *)

Module EdgeRowTests.

  Local Open Scope positive_scope.

  (** A row with no sources keeps the flags of the empty row. *)
  Example empty_row_without_source_keeps_flags :
    dom_edges_from_fast (DigraphCode.prepare Unreachable.graph) 1
      (parent_map Unreachable.parents) (dom_positions [1; 2; 3; 4]) Empty (Some Empty) 5 =
      Some Empty.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A nonempty row with no sources is rejected. *)
  Example nonempty_row_without_source_is_rejected :
    dom_edges_from_fast (DigraphCode.prepare Unreachable.graph) 1
      (parent_map Unreachable.parents) Empty Empty (Some Empty) 1 = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A rejected edge row stays rejected when the edge is read again. *)
  Example rejected_edge_row_stays_rejected :
    dom_edges_from_fast (DigraphCode.prepare Diamond.graph) 1
      (parent_map Diamond.parents) (dom_positions [1; 2; 4; 3]) Empty None 1 = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EdgeRowTests.

(** * Ancestors *)

Module AncestorTests.

  Local Open Scope positive_scope.

  (** The tree of a path, with root 1, for the ancestor queries. *)
  Definition line_tree :=
    DomCode.tree (DigraphCode.prepare Line.graph) 1 (parent_map Line.parents) [1; 2; 3; 4].

  (** The root dominates the last vertex of a path. *)
  Example root_dominates_last_vertex :
    DomCode.dominates_b line_tree 1 4 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A middle vertex of a path dominates the last vertex. *)
  Example middle_vertex_dominates_last :
    DomCode.dominates_b line_tree 2 4 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The last vertex of a path does not dominate the root. *)
  Example last_vertex_does_not_dominate_root :
    DomCode.dominates_b line_tree 4 1 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A vertex that is not in the tree dominates nothing. *)
  Example unknown_vertex_dominates_nothing :
    DomCode.dominates_b line_tree 9 4 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AncestorTests.

(** * Low-high parents *)

Module LowHighTests.

  Local Open Scope positive_scope.

  (** The low-high parent map of a path is its parent map. *)
  Example line_low_high_parents :
    dom_lt_parents (DigraphCode.prepare Line.graph) 1 = parent_map Line.parents.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The low-high parent map of a diamond is its parent map. *)
  Example diamond_low_high_parents :
    dom_lt_parents (DigraphCode.prepare Diamond.graph) 1 = parent_map Diamond.parents.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A chain of four links, built by linking each vertex to the one before it. *)
  Definition compression_chain :=
    dom_lt_link (dom_lt_link (dom_lt_link (DomLtLinks Empty Empty []) 2%N 1%N)
      3%N 2%N) 4%N 3%N.

  Definition compression_tied_semis :=
    PTrieCode.set (dom_lt_key 4%N) 1%N
      (PTrieCode.set (dom_lt_key 3%N) 1%N
        (PTrieCode.set (dom_lt_key 2%N) 1%N Empty)).

  (** Equal stored semidominators still select the fresh label at every unwind frame. *)
  Example compression_prefers_fresh_label_on_ties :
    snd (dom_lt_eval 4%N compression_tied_semis compression_chain 4%N) = 4%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The links and label that an evaluation leaves after it runs out of fuel at once. *)
  Definition exhausted_prefix :=
    (DomLtLinks (lt_shortcut compression_chain) (lt_label compression_chain)
      (LtEval 4%N :: lt_operations compression_chain), 4%N).

  (** Exhaustion just after the first score prefetch preserves the exact partial links. *)
  Example compression_preserves_exhausted_prefix :
    dom_lt_eval 1%N compression_tied_semis compression_chain 4%N = exhausted_prefix.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LowHighTests.

(** * Producer *)

Module ProducerTests.

  Local Open Scope positive_scope.

  (** Each fixture graph with the parent list that its dominator tree must have. *)
  Definition producer_fixtures : list (digraph * list (positive * positive)) :=
    [(Line.graph, Line.parents); (Diamond.graph, Diamond.parents);
      (JoinLoop.graph, JoinLoop.parents); (NestedLoop.graph, NestedLoop.parents);
      (SelfLoop.graph, SelfLoop.parents); (Irreducible.graph, Irreducible.parents);
      (Singleton.graph, Singleton.parents); (Unreachable.graph, Unreachable.parents)].

  (** The producer builds a certificate that the checker accepts for each fixture. *)
  Example producer_certificates_are_accepted :
    forallb (fun c =>
      let p := DigraphCode.prepare (fst c) in
      let '(m, o) := DomCode.build p 1 in DomCode.check p 1 m o)
      producer_fixtures = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A graph whose sources come from sibling subtrees gets an accepted certificate. *)
  Definition derived_sources_graph := fixture_graph [1; 2; 3; 4; 5; 6; 7]
    [(1, 2); (1, 3); (2, 4); (3, 5); (4, 6); (5, 6); (6, 7)].

  Example producer_derives_sources_from_sibling_subtrees :
    let p := DigraphCode.prepare derived_sources_graph in
    let '(m, o) := DomCode.build p 1 in DomCode.check p 1 m o = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A path of eight vertices with a backedge from 8 to 2. *)
  Definition compression_loop_graph := fixture_graph [1; 2; 3; 4; 5; 6; 7; 8]
    [(1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 7); (7, 8); (8, 2)].

  (** The certificate of the loop graph, a parent map that follows the path and its order. *)
  Definition compression_loop_certificate :=
    (parent_map [(2, 1); (3, 2); (4, 3); (5, 4); (6, 5); (7, 6); (8, 7)],
      [1; 2; 3; 4; 5; 6; 7; 8]).

  (** A long backedge path gets its parent chain compressed into the expected parents. *)
  Example producer_compresses_long_backedge_path :
    DomCode.build (DigraphCode.prepare compression_loop_graph) 1 = compression_loop_certificate.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The producer gives the parent map of each fixture, in fixture order. *)
  Example producer_parent_maps_of_fixtures :
    map (fun c => fst (DomCode.build (DigraphCode.prepare (fst c)) 1)) producer_fixtures =
      map (fun c => parent_map (snd c)) producer_fixtures.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A root with no row gives an empty parent map and an empty order. *)
  Example missing_root_row_gives_empty_certificate :
    DomCode.build (DigraphCode.prepare (fixture_graph [1; 4] [(1, 4)])) 2 = (Empty, []).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A listed vertex with an empty row is the only vertex of its order. *)
  Example listed_empty_row_is_its_own_order :
    DomCode.build (DigraphCode.prepare (fixture_graph [1; 4] [(1, 4)])) 4 = (Empty, [4]).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A successor that is not listed as a vertex is ignored by the producer. *)
  Example producer_ignores_unlisted_wide_successor :
    DomCode.build (DigraphCode.prepare (fixture_graph [1; 2] [(1, 2); (2, 1024)])) 1 =
      (parent_map [(2, 1)], [1; 2]).
  Proof.
    vm_compute. reflexivity.
  Qed.

End ProducerTests.

(** * Subtree sizes *)

Module SubtreeSizeTests.

  Local Open Scope positive_scope.

  (** Each vertex of a path has its position in the order and its subtree size. *)
  Example path_positions_and_subtree_sizes :
    let o := [1; 2; 3; 4] in
    let info := dom_info_sizes (parent_map Line.parents) o (dom_positions o) in
    map (fun v => trie_get v info) [1; 2; 3; 4; 9] =
      [Some (0%N, 4%N); Some (1%N, 3%N); Some (2%N, 2%N); Some (3%N, 1%N); None].
  Proof.
    vm_compute. reflexivity.
  Qed.

End SubtreeSizeTests.
