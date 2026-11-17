(** * Dominance frontier observations

    Frontier rows and their closure preserve the graph fixture results.
    For example, both branches of a diamond have the join in their frontier.

    Groups:
    - FrontierRowTests: the frontier of each vertex in the fixtures.
    - IdfTests: the iterated frontier of a set of seeds.
    - RawInputTests: frontiers from raw rows that repeat vertices.

    Builds on: graph fixtures, dominator construction and frontier code. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Dom FrontierSig Frontier.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.

(** * Fixtures *)

(** The dominance frontier of each vertex of a graph, rooted at vertex 1. *)
Definition fixture_frontiers graph :=
  let g := DigraphCode.prepare graph in
  let '(parents, order) := DomCode.build g 1 in
  FrontierCode.df g (DomCode.tree g 1 parents order).

(** * Frontier rows *)

Module FrontierRowTests.

  Local Open Scope positive_scope.

  (** Both branches of a diamond have the join in their frontier. *)
  Example diamond_branches_have_join :
    map (frontier_row (fixture_frontiers Diamond.graph)) [1; 2; 3; 4] =
      [[]; [4]; [4]; []].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-loop at the join puts the join in the frontier of every vertex but the root. *)
  Example loop_join_is_in_every_frontier :
    map (frontier_row (fixture_frontiers JoinLoop.graph)) [1; 2; 3; 4] =
      [[]; [4]; [4]; [4]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Nested cycles put the headers and the root into the frontiers of the inner vertices. *)
  Example nested_cycles_frontiers :
    map (frontier_row (fixture_frontiers NestedLoop.graph)) [1; 2; 3; 4] =
      [[1]; [2; 1]; [2; 1]; [1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A path has an empty frontier at every vertex. *)
  Example line_frontiers_are_empty :
    map (frontier_row (fixture_frontiers Line.graph)) [1; 2; 3; 4] = [[]; []; []; []].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A vertex that is not in the graph has an empty frontier row. *)
  Example unknown_vertex_row_is_empty :
    frontier_row (fixture_frontiers Diamond.graph) 42 = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Every row of an empty graph is empty. *)
  Example empty_graph_rows_are_empty :
    map (frontier_row (fixture_frontiers EmptyGraph.graph)) [1; 42] = [[]; []].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A singleton vertex has an empty frontier row. *)
  Example singleton_row_is_empty :
    map (frontier_row (fixture_frontiers Singleton.graph)) [1; 42] = [[]; []].
  Proof.
    vm_compute. reflexivity.
  Qed.

End FrontierRowTests.

(** * Iterated frontier *)

Module IdfTests.

  Local Open Scope positive_scope.

  (** The iterated frontier of one branch of a diamond is the join. *)
  Example branch_seed_gives_join :
    FrontierCode.idf (fixture_frontiers Diamond.graph) [2] = [4].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The iterated frontier of a looping join contains the join itself. *)
  Example loop_join_seed_gives_itself :
    FrontierCode.idf (fixture_frontiers JoinLoop.graph) [4] = [4].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** No seeds give an empty iterated frontier. *)
  Example no_seeds_give_nothing :
    FrontierCode.idf (fixture_frontiers Diamond.graph) [] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A seed that is not in the graph gives an empty iterated frontier. *)
  Example unknown_seed_gives_nothing :
    FrontierCode.idf (fixture_frontiers Diamond.graph) [42] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A seed listed twice gives the same result as a seed listed once. *)
  Example repeated_seed_counts_once :
    FrontierCode.idf (fixture_frontiers Diamond.graph) [2; 2] = [4].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A seed that the loop returns to is discovered again, and reported once. *)
  Example returning_seed_is_discovered :
    FrontierCode.idf (fixture_frontiers JoinLoop.graph) [4; 4] = [4].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Forty copies of a seed give the same result as one copy. *)
  Example many_repeated_seeds_give_join :
    FrontierCode.idf (fixture_frontiers Diamond.graph) (repeat 2 40) = [4].
  Proof.
    vm_compute. reflexivity.
  Qed.

End IdfTests.

(** * Raw input *)

Module RawInputTests.

  Local Open Scope positive_scope.

  (** A repeated pair in raw columns adds one target per row, not one per listing. *)
  Example repeated_pairs_add_one_target_per_row :
    map (frontier_row (df_transpose [(4, [2; 2]); (4, [2; 3; 2]); (5, [2; 2])])) [2; 3] =
      [[5; 4]; [4]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Raw rows of the two-vertex cycle 1-2, with each edge listed twice. *)
  Definition repeated_cycle_rows :=
    PTrieCode.set 1 [2; 2] (PTrieCode.set 2 [1; 1] Empty).

  (** A repeated raw seed is discovered when a cycle returns to it as a target. *)
  Example repeated_seed_in_cycle_is_discovered :
    FrontierCode.idf repeated_cycle_rows [1; 1] = [2; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

End RawInputTests.
