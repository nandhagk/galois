(** * Natural loop observations

    Forests retain nested ownership and reducibility observations from graph fixtures.
    For example, the inner cycle assigns vertex 3 to header 2.

    Groups:
    - [ForestTests] The parent and header of each vertex in the loop forest.
    - [ReducibilityTests] Which fixture graphs are reducible.
    - [BodyTests] The natural loop body of each header.

    Builds on: graph fixtures, dominator construction and loop code. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Dom LoopsSig Loops.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.

(** * Fixtures *)

(** The dominator tree of a prepared graph, rooted at vertex 1. *)
Definition fixture_tree (g : prepared) :=
  let '(parents, order) := DomCode.build g 1 in DomCode.tree g 1 parents order.

(** The loop forest of a graph, computed from its dominator tree. *)
Definition forest_of (graph : digraph) :=
  let g := DigraphCode.prepare graph in
  LoopsCode.forest g (fixture_tree g).

(** Whether the loop structure of a graph is reducible. *)
Definition reducible_of (graph : digraph) :=
  let g := DigraphCode.prepare graph in
  LoopsCode.reducible_b g (fixture_tree g).

(** The loop forest of the nested-cycle fixture. *)
Definition nested_forest := forest_of NestedLoop.graph.

(** The loop forest of the self-loop fixture. *)
Definition self_loop_forest := forest_of SelfLoop.graph.

(** * Forest *)

Module ForestTests.

  Local Open Scope positive_scope.

  (** The inner header 2 has the outer header 1 as its parent, and the others have none. *)
  Example inner_header_has_outer_parent :
    map (fun v => trie_get v (parent nested_forest)) [1; 2; 3; 4; 99] =
      [None; Some 1; None; None; None].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each vertex of the nested cycles has its innermost header. *)
  Example nested_cycles_innermost_headers :
    map (fun v => trie_get v (header nested_forest)) [1; 2; 3; 4; 99] =
      [Some 1; Some 2; Some 2; Some 1; None].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A path has no loop header, so vertex 2 has none. *)
  Example path_has_no_header :
    trie_get 2 (header (forest_of Line.graph)) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop makes its vertex its own header. *)
  Example self_loop_is_its_own_header :
    trie_get 1 (header self_loop_forest) = Some 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop has no parent loop. *)
  Example self_loop_has_no_parent :
    trie_get 1 (parent self_loop_forest) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ForestTests.

(** * Reducibility *)

Module ReducibilityTests.

  Local Open Scope positive_scope.

  (** Nested cycles with a single entry are reducible. *)
  Example nested_cycles_are_reducible :
    reducible_of NestedLoop.graph = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A cycle entered at two vertices is not reducible. *)
  Example irreducible_cycle_is_not_reducible :
    reducible_of Irreducible.graph = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A path is reducible. *)
  Example path_is_reducible :
    reducible_of Line.graph = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop is reducible. *)
  Example self_loop_is_reducible :
    reducible_of SelfLoop.graph = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty graph is reducible. *)
  Example empty_graph_is_reducible :
    reducible_of EmptyGraph.graph = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ReducibilityTests.

(** * Loop bodies *)

Module BodyTests.

  Local Open Scope positive_scope.

  (** The body of the inner header 2 is the inner cycle, and it excludes the outer vertices. *)
  Example inner_body_is_inner_cycle :
    map (fun v => existsb (Pos.eqb v) (loop_body nested_forest 2)) [1; 2; 3; 4] =
      [false; true; true; false].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The body of the outer header 1 contains every vertex of the nested cycles. *)
  Example outer_body_is_every_vertex :
    map (fun v => existsb (Pos.eqb v) (loop_body nested_forest 1)) [1; 2; 3; 4] =
      [true; true; true; true].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The body of a self-loop is its own vertex. *)
  Example self_loop_body_is_itself :
    loop_body self_loop_forest 1 = [1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Only the headers 1 and 2 of the nested cycles have a loop body. *)
  Example only_headers_have_bodies :
    filter (fun v => match trie_get v (body nested_forest) with
      | Some _ => true
      | None => false
      end) [1; 2; 3; 4] = [1; 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty graph has no loop body for any vertex. *)
  Example empty_graph_has_no_body :
    trie_get 99 (body (forest_of EmptyGraph.graph)) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A predecessor that no path from the root reaches is not in the loop body. *)
  Definition detached_predecessor_graph := fixture_graph [1; 2; 3; 4]
    [(1, 2); (2, 3); (3, 2); (4, 3)].

  Example unreachable_predecessor_is_not_in_body :
    existsb (Pos.eqb 4) (loop_body (forest_of detached_predecessor_graph) 2) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A duplicated raw vertex is stored once in its loop body. *)
  Definition duplicate_root_graph := DigraphCode.prepare (fixture_graph [1; 1] [(1, 1); (1, 1)]).

  Definition duplicate_root_tree :=
    DomTree Empty Empty (PTrieCode.set 1 0%N Empty) (PTrieCode.set 1 1%N Empty).

  Example duplicate_raw_vertex_body_is_single :
    loop_body (LoopsCode.forest duplicate_root_graph duplicate_root_tree) 1 = [1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Repeated latches add each body vertex only once. *)
  Definition latch_graph := DigraphCode.prepare (fixture_graph [1; 2] [(1, 2); (2, 2); (2, 2)]).

  Definition latch_tree :=
    DomTree Empty Empty (PTrieCode.set 1 0%N (PTrieCode.set 2 1%N Empty)) Empty.

  Example repeated_latches_add_each_vertex_once :
    collect latch_graph latch_tree 1 [2; 2; 2] = [1; 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

End BodyTests.
