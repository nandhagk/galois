(** * Graph fixtures

    Named graphs supply vertices, roots, edges and candidate orders.
    For example, the diamond has two branches that meet at vertex four.

    Groups:
    - Line: a path from vertex 1 to vertex 4.
    - Diamond: two branches from 1 that meet at 4.
    - JoinLoop: the diamond with a self-loop at the join.
    - NestedLoop: an inner cycle 2-3 inside an outer cycle through 1 and 4.
    - TwoEntry: two roots, 1 and 2, that enter the same vertex 3.
    - SelfLoop: one vertex with an edge to itself.
    - Irreducible: a cycle 2-3 entered at both vertices.
    - EmptyGraph: no vertices and no edges.
    - Singleton: one vertex and no edges.
    - Unreachable: a path with a fifth vertex that no edge reaches.

    Builds on: graph data and binary tries. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data.
Import List.ListNotations.
Open Scope positive_scope.

(** * Fixtures *)

(** The digraph on the given vertices, with the given edges. *)
Definition fixture_graph (vertices : list positive)
  (edges : list (positive * positive)) : digraph :=
  Digraph vertices (fold_right (fun u tr =>
    PTrieCode.set u (map snd (filter (fun e => Pos.eqb (fst e) u) edges)) tr)
    Empty vertices).

(** * Line *)

Module Line.
  (** The root of the path. *)
  Definition roots := [1].
  (** The path 1 to 2 to 3 to 4. *)
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
  (** Each vertex after the root has its predecessor as parent. *)
  Definition parents := [(2, 1); (3, 2); (4, 3)].
  (** The order that visits the path from its root. *)
  Definition order := WVertex 1 (WVertex 2 (WVertex 3 (WVertex 4 WNil))).
End Line.

(** * Diamond *)

Module Diamond.
  (** The root of the diamond. *)
  Definition roots := [1].
  (** Two branches, 2 and 3, from 1 that meet at 4. *)
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
  (** The join 4 has the root 1 as its parent, not either branch. *)
  Definition parents := [(2, 1); (3, 1); (4, 1)].
  (** The order that visits the branches and then the join. *)
  Definition order := WVertex 1 (WVertex 2 (WVertex 3 (WVertex 4 WNil))).
End Diamond.

(** * JoinLoop *)

Module JoinLoop.
  (** The root of the looping diamond. *)
  Definition roots := [1].
  (** The diamond with an extra self-loop at the join 4. *)
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4); (4, 4)].
  (** The parents of the diamond, which the loop does not change. *)
  Definition parents := Diamond.parents.
  (** The order with the join 4 as a loop header. *)
  Definition order := WVertex 1 (WVertex 2 (WVertex 3 (WLoop 4 WNil WNil))).
End JoinLoop.

(** * NestedLoop *)

Module NestedLoop.
  (** The root of the nested cycles. *)
  Definition roots := [1].
  (** An inner cycle 2 to 3 and back, inside an outer cycle through 1 and 4. *)
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
  (** The parents of the path, which the cycles keep. *)
  Definition parents := Line.parents.
  (** The order with the outer loop on 1 and the inner loop on 2. *)
  Definition order := WLoop 1 (WLoop 2 (WVertex 3 WNil) (WVertex 4 WNil)) WNil.
End NestedLoop.

(** * TwoEntry *)

Module TwoEntry.
  (** Two roots, 1 and 2, that both enter vertex 3. *)
  Definition roots := [1; 2].
  (** Vertices 1 and 2 both point at 3, which leads to 4. *)
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 3); (2, 3); (3, 4)].
  (** Only the edge into 4 has a parent binding. *)
  Definition parents := [(4, 3)].
  (** The order of the path, which the two entries share. *)
  Definition order := Line.order.
End TwoEntry.

(** * SelfLoop *)

Module SelfLoop.
  (** The only root, which is also the only vertex. *)
  Definition roots := [1].
  (** One vertex with an edge to itself. *)
  Definition graph := fixture_graph [1] [(1, 1)].
  (** The self-loop has no parent binding. *)
  Definition parents : list (positive * positive) := [].
  (** A loop on the single vertex. *)
  Definition order := WLoop 1 WNil WNil.
End SelfLoop.

(** * Irreducible *)

Module Irreducible.
  (** The root of the irreducible graph. *)
  Definition roots := [1].
  (** A cycle 2 to 3 and back, entered from 1 at both vertices. *)
  Definition graph := fixture_graph [1; 2; 3] [(1, 2); (1, 3); (2, 3); (3, 2)].
  (** Both entries from 1 are parent bindings. *)
  Definition parents := [(2, 1); (3, 1)].
  (** The order that has the cycle 2-3 as a loop on 2. *)
  Definition order := WVertex 1 (WLoop 2 (WVertex 3 WNil) WNil).
End Irreducible.

(** * EmptyGraph *)

Module EmptyGraph.
  (** No roots. *)
  Definition roots : list positive := [].
  (** No vertices and no edges. *)
  Definition graph := fixture_graph [] [].
  (** No parent bindings. *)
  Definition parents : list (positive * positive) := [].
  (** The empty order. *)
  Definition order := WNil.
End EmptyGraph.

(** * Singleton *)

Module Singleton.
  (** The only root. *)
  Definition roots := [1].
  (** One vertex and no edges. *)
  Definition graph := fixture_graph [1] [].
  (** The empty parent bindings of the empty graph. *)
  Definition parents := EmptyGraph.parents.
  (** The order of the single vertex. *)
  Definition order := WVertex 1 WNil.
End Singleton.

(** * Unreachable *)

Module Unreachable.
  (** The root of the path. *)
  Definition roots := [1].
  (** The path 1 to 4, plus vertex 5 that no edge reaches. *)
  Definition graph := fixture_graph [1; 2; 3; 4; 5] [(1, 2); (2, 3); (3, 4)].
  (** The parents of the path, since 5 has none. *)
  Definition parents := Line.parents.
  (** The order of the path, which leaves 5 out. *)
  Definition order := Line.order.
End Unreachable.
