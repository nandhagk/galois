(** * Dominance frontier observations

    Frontier rows and their closure preserve the graph fixture results.
    For example, both branches of a diamond have the join in their frontier.
    Builds on: graph fixtures, dominator construction and frontier code. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Dom FrontierSig Frontier.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition fixture_frontiers graph :=
  let g := DigraphCode.prepare graph in
  let '(parents, order) := DomCode.build g 1 in
  FrontierCode.df g (DomCode.tree g 1 parents order).

Example diamond_frontiers :
  map (frontier_row (fixture_frontiers Diamond.graph)) [1; 2; 3; 4] =
    [[]; [4]; [4]; []].
Proof. vm_compute. reflexivity. Qed.

Example loop_frontiers :
  map (frontier_row (fixture_frontiers JoinLoop.graph)) [1; 2; 3; 4] =
    [[]; [4]; [4]; [4]].
Proof. vm_compute. reflexivity. Qed.

(** Nested columns share their target parent through repeated climbs and a root return. *)
Example nested_loop_frontiers :
  map (frontier_row (fixture_frontiers NestedLoop.graph)) [1; 2; 3; 4] =
    [[1]; [2; 1]; [2; 1]; [1]].
Proof.
  vm_compute. reflexivity.
Qed.

Example line_frontiers :
  map (frontier_row (fixture_frontiers Line.graph)) [1; 2; 3; 4] = [[]; []; []; []].
Proof. vm_compute. reflexivity. Qed.

Example diamond_idf : FrontierCode.idf (fixture_frontiers Diamond.graph) [2] = [4].
Proof. vm_compute. reflexivity. Qed.

Example loop_idf : FrontierCode.idf (fixture_frontiers JoinLoop.graph) [4] = [4].
Proof. vm_compute. reflexivity. Qed.

Example empty_seeds : FrontierCode.idf (fixture_frontiers Diamond.graph) [] = [].
Proof. vm_compute. reflexivity. Qed.

Example unknown_seed : FrontierCode.idf (fixture_frontiers Diamond.graph) [42] = [].
Proof. vm_compute. reflexivity. Qed.

Example repeated_seed : FrontierCode.idf (fixture_frontiers Diamond.graph) [2; 2] = [4].
Proof. vm_compute. reflexivity. Qed.

Example unknown_row : frontier_row (fixture_frontiers Diamond.graph) 42 = [].
Proof. vm_compute. reflexivity. Qed.

Example empty_frontier :
  map (frontier_row (fixture_frontiers EmptyGraph.graph)) [1; 42] = [[]; []].
Proof. vm_compute. reflexivity. Qed.

Example singleton_frontier :
  map (frontier_row (fixture_frontiers Singleton.graph)) [1; 42] = [[]; []].
Proof. vm_compute. reflexivity. Qed.

Example returning_seed_is_discovered :
  FrontierCode.idf (fixture_frontiers JoinLoop.graph) [4; 4] = [4].
Proof. vm_compute. reflexivity. Qed.

Example repeated_seeds_pass_accessibility_prefix :
  FrontierCode.idf (fixture_frontiers Diamond.graph) (repeat 2 40) = [4].
Proof. vm_compute. reflexivity. Qed.

(** Repeated raw columns and repeated members still contribute one target per row. *)
Example raw_transpose_repeated_pairs :
  map (frontier_row (df_transpose [(4, [2; 2]); (4, [2; 3; 2]); (5, [2; 2])])) [2; 3] =
    [[5; 4]; [4]].
Proof. vm_compute. reflexivity. Qed.

Definition repeated_cycle_rows :=
  PTrieCode.set 1 [2; 2] (PTrieCode.set 2 [1; 1] Empty).

(** A repeated raw seed is discovered when a cycle returns to it as a target. *)
Example raw_idf_repeated_cycle : FrontierCode.idf repeated_cycle_rows [1; 1] = [2; 1].
Proof. vm_compute. reflexivity. Qed.
