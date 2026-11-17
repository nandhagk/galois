(** * Strongly connected component observations

    Components retain the producer's reverse topological order.
    For example, a self-loop forms one singleton component.

    Groups:
    - [ComponentTests] The components of the graph fixtures.
    - [PreparedInputTests] Components from prepared inputs with stale or unlisted parts.

    Builds on: graph fixtures, preparation and SCC computation. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Scc.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.

(** * Fixtures *)

(** The components of a graph after preparation. *)
Definition components g := comps (SccCode.run (DigraphCode.prepare g)).

(** * Components *)

Module ComponentTests.

  Local Open Scope positive_scope.

  (** A path has one singleton component per vertex, in reverse topological order. *)
  Example line_components : components Line.graph = [[4]; [3]; [2]; [1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The two branches of a diamond are separate components between the root and the join. *)
  Example diamond_components : components Diamond.graph = [[4]; [2]; [3]; [1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An edge into a component that is already finished does not merge the components. *)
  Definition cross_edge_graph := fixture_graph [1; 2; 3] [(1, 2); (1, 3); (3, 2)].

  Example cross_edge_keeps_components_apart :
    components cross_edge_graph = [[2]; [3]; [1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop forms one singleton component. *)
  Example self_loop_component : components SelfLoop.graph = [[1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The nested cycles form one maximal component that contains all four vertices. *)
  Example nested_cycles_form_one_component :
    components NestedLoop.graph = [[4; 3; 2; 1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The irreducible cycle 2-3 is one component, and the root 1 is another. *)
  Example irreducible_components : components Irreducible.graph = [[3; 2]; [1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty graph has no components. *)
  Example empty_graph_has_no_components : components EmptyGraph.graph = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ComponentTests.

(** * Prepared inputs *)

Module PreparedInputTests.

  Local Open Scope positive_scope.

  (** Wrong cached counts do not change the components of a prepared path. *)
  Example wrong_count_caches_are_ignored :
    comps (SccCode.run (Prepared Line.graph Empty 0%N 0%N)) = [[4]; [3]; [2]; [1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Successors that are not listed as vertices are left out of the components. *)
  Definition unlisted_successor_graph := Digraph [1] (succ Line.graph).

  Example unlisted_successors_are_excluded :
    comps (SccCode.run (Prepared unlisted_successor_graph Empty 0%N 0%N)) = [[1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A repeated listed row stays in the rebuilt graph, and an unlisted successor does not. *)
  Definition repeated_row_graph :=
    Prepared (Digraph [1; 1; 2] (PTrieCode.set 1 [2; 2; 99] Empty)) Empty 0%N 0%N.

  (** The repeated row still yields the components 2 and then 1. *)
  Example repeated_row_components : comps (SccCode.run repeated_row_graph) = [[2]; [1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rebuilt graph counts three listed vertices. *)
  Example repeated_row_vertex_count : nv (scc_graph_counted repeated_row_graph) = 3%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rebuilt graph counts four edges, since the repeated row gives each edge twice. *)
  Example repeated_row_edge_count : ne (scc_graph_counted repeated_row_graph) = 4%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PreparedInputTests.
