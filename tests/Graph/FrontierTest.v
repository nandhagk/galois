(** * Dominance frontier observations

    Frontier rows and their closure preserve the graph fixture results.
    For example, both branches of a diamond have the join in their frontier.
    Builds on: graph fixtures, dominator construction and frontier code. *)

From Stdlib Require Import List PArith.
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
