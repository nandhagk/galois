(** * Strongly connected component observations

    Components retain the producer's reverse topological order.
    For example, a self-loop forms one singleton component.
    Builds on: graph fixtures, preparation and SCC computation. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Scc.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition components g := comps (SccCode.run (DigraphCode.prepare g)).

Example line_components : components Line.graph = [[4]; [3]; [2]; [1]].
Proof. vm_compute. reflexivity. Qed.

Example diamond_components : components Diamond.graph = [[4]; [2]; [3]; [1]].
Proof. vm_compute. reflexivity. Qed.

Example cross_edge_into_finished_component :
  components (fixture_graph [1; 2; 3] [(1, 2); (1, 3); (3, 2)]) = [[2]; [3]; [1]].
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_component : components SelfLoop.graph = [[1]].
Proof. vm_compute. reflexivity. Qed.

Example nested_is_one_maximal_component : components NestedLoop.graph = [[4; 3; 2; 1]].
Proof. vm_compute. reflexivity. Qed.

Example irreducible_components : components Irreducible.graph = [[3; 2]; [1]].
Proof. vm_compute. reflexivity. Qed.

Example empty_components : components EmptyGraph.graph = [].
Proof. vm_compute. reflexivity. Qed.

Example ignores_wrong_count_caches :
  comps (SccCode.run (Prepared Line.graph Empty 0%N 0%N)) = [[4]; [3]; [2]; [1]].
Proof.
  vm_compute. reflexivity.
Qed.

Example filters_unlisted_successors_and_rows :
  comps (SccCode.run (Prepared (Digraph [1] (succ Line.graph)) Empty 0%N 0%N)) = [[1]].
Proof.
  vm_compute. reflexivity.
Qed.

(** Counting retains repeated listed rows while excluding unlisted successor occurrences. *)
Example counted_rebuild_retains_repeated_rows :
  let g := Prepared (Digraph [1; 1; 2] (PTrieCode.set 1 [2; 2; 99] Empty)) Empty 0%N 0%N in
  (comps (SccCode.run g), nv (scc_graph_counted g), ne (scc_graph_counted g)) =
    ([[2]; [1]], 3%N, 4%N).
Proof.
  vm_compute. reflexivity.
Qed.
