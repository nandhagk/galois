(** * Graph fixtures

    Named graphs supply vertices, roots, edges and candidate orders.
    For example, the diamond has two branches that meet at vertex four.
    Builds on: graph data and binary tries. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data.
Import List.ListNotations.
Open Scope positive_scope.

Definition fixture_graph (vertices : list positive) (edges : list (positive * positive)) : digraph :=
  Digraph vertices (fold_right (fun u tr =>
    PTrieCode.set u (map snd (filter (fun e => Pos.eqb (fst e) u) edges)) tr)
    Empty vertices).

Module Line.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
  Definition parents := [(2, 1); (3, 2); (4, 3)].
  Definition order := WVertex 1 (WVertex 2 (WVertex 3 (WVertex 4 WNil))).
End Line.

Module Diamond.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
  Definition parents := [(2, 1); (3, 1); (4, 1)].
  Definition order := WVertex 1 (WVertex 2 (WVertex 3 (WVertex 4 WNil))).
End Diamond.

Module JoinLoop.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4); (4, 4)].
  Definition parents := Diamond.parents.
  Definition order := WVertex 1 (WVertex 2 (WVertex 3 (WLoop 4 WNil WNil))).
End JoinLoop.

Module NestedLoop.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
  Definition parents := Line.parents.
  Definition order := WLoop 1 (WLoop 2 (WVertex 3 WNil) (WVertex 4 WNil)) WNil.
End NestedLoop.

Module TwoEntry.
  Definition roots := [1; 2].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 3); (2, 3); (3, 4)].
  Definition parents := [(4, 3)].
  Definition order := Line.order.
End TwoEntry.

Module SelfLoop.
  Definition roots := [1].
  Definition graph := fixture_graph [1] [(1, 1)].
  Definition parents : list (positive * positive) := [].
  Definition order := WLoop 1 WNil WNil.
End SelfLoop.

Module Irreducible.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3] [(1, 2); (1, 3); (2, 3); (3, 2)].
  Definition parents := [(2, 1); (3, 1)].
  Definition order := WVertex 1 (WLoop 2 (WVertex 3 WNil) WNil).
End Irreducible.

Module EmptyGraph.
  Definition roots : list positive := [].
  Definition graph := fixture_graph [] [].
  Definition parents : list (positive * positive) := [].
  Definition order := WNil.
End EmptyGraph.

Module Singleton.
  Definition roots := [1].
  Definition graph := fixture_graph [1] [].
  Definition parents := EmptyGraph.parents.
  Definition order := WVertex 1 WNil.
End Singleton.

Module Unreachable.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4; 5] [(1, 2); (2, 3); (3, 4)].
  Definition parents := Line.parents.
  Definition order := Line.order.
End Unreachable.
