(** * Graph preparation observations

    Preparation retains adjacency and builds predecessor rows.
    For example, the diamond has two predecessors at its join.

    Groups:
    - [SuccessorTests] The successor rows that preparation keeps.
    - [PredecessorTests] The predecessor rows that preparation builds.
    - [CountTests] The vertex and edge counts that preparation caches.

    Builds on: graph fixtures and preparation. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.

(** * Successor rows *)

Module SuccessorTests.

  Local Open Scope positive_scope.

  (** The root of the diamond has the two branches as successors. *)
  Example root_has_two_successors :
    succs (base (DigraphCode.prepare Diamond.graph)) 1 = [2; 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop keeps its vertex as its own successor. *)
  Example self_loop_successor :
    succs (base (DigraphCode.prepare SelfLoop.graph)) 1 = [1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty graph has no successors. *)
  Example empty_successors :
    succs (base (DigraphCode.prepare EmptyGraph.graph)) 1 = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End SuccessorTests.

(** * Predecessor rows *)

Module PredecessorTests.

  Local Open Scope positive_scope.

  (** The join of the diamond has both branches as predecessors. *)
  Example join_has_two_predecessors :
    preds (DigraphCode.prepare Diamond.graph) 4 = [2; 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop keeps its vertex as its own predecessor. *)
  Example self_loop_predecessor :
    preds (DigraphCode.prepare SelfLoop.graph) 1 = [1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty graph has no predecessors. *)
  Example empty_predecessors :
    preds (DigraphCode.prepare EmptyGraph.graph) 1 = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Repeated source rows and parallel edges keep all four predecessor occurrences of vertex 2. *)
  Definition duplicate_rows := Digraph [1; 1; 2] (PTrieCode.set 1 [2; 2] Empty).

  Example duplicate_rows_keep_predecessor_occurrences :
    preds (DigraphCode.prepare duplicate_rows) 2 = [1; 1; 1; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

End PredecessorTests.

(** * Counts *)

Module CountTests.

  Local Open Scope positive_scope.

  (** A vertex listed twice is counted twice, so the listing has three vertices. *)
  Definition duplicate_rows := Digraph [1; 1; 2] (PTrieCode.set 1 [2; 2] Empty).

  Example duplicate_rows_vertex_count :
    nv (DigraphCode.prepare duplicate_rows) = 3%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each listing of a row counts its edges again, so the parallel edges give four. *)
  Example duplicate_rows_edge_count :
    ne (DigraphCode.prepare duplicate_rows) = 4%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A graph with five edges keeps its vertex count of four through preparation. *)
  Definition five_edge_graph :=
    fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (1, 4); (2, 3); (3, 4)].

  Example five_edge_graph_vertex_count :
    nv (DigraphCode.prepare five_edge_graph) = 4%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The same graph keeps its edge count of five through preparation. *)
  Example five_edge_graph_edge_count :
    ne (DigraphCode.prepare five_edge_graph) = 5%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The same graph keeps the predecessors of vertex 4 in the order 1, 3. *)
  Example five_edge_graph_predecessor_order :
    preds (DigraphCode.prepare five_edge_graph) 4 = [1; 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

End CountTests.
