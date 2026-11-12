(** * Natural loop observations

    Forests retain nested ownership and reducibility observations from graph fixtures.
    For example, the inner cycle assigns vertex 3 to header 2.
    Builds on: graph fixtures, dominator construction and loop code. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Dom LoopsSig Loops.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition fixture_tree (g : prepared) :=
  let '(parents, order) := DomCode.build g 1 in DomCode.tree g 1 parents order.

Example nested_parents :
  let g := DigraphCode.prepare NestedLoop.graph in
  let l := LoopsCode.forest g (fixture_tree g) in
  map (fun v => trie_get v (parent l)) [1; 2; 3; 4; 99] =
    [None; Some 1; None; None; None].
Proof. vm_compute. reflexivity. Qed.

Example nested_innermost :
  let g := DigraphCode.prepare NestedLoop.graph in
  let l := LoopsCode.forest g (fixture_tree g) in
  map (fun v => trie_get v (header l)) [1; 2; 3; 4; 99] =
    [Some 1; Some 2; Some 2; Some 1; None].
Proof. vm_compute. reflexivity. Qed.

Example line_has_no_loops :
  let g := DigraphCode.prepare Line.graph in
  trie_get 2 (header (LoopsCode.forest g (fixture_tree g))) = None.
Proof. vm_compute. reflexivity. Qed.

Example self_loop_owns_itself :
  let g := DigraphCode.prepare SelfLoop.graph in
  let l := LoopsCode.forest g (fixture_tree g) in
  trie_get 1 (header l) = Some 1 /\ trie_get 1 (parent l) = None.
Proof. vm_compute. split; reflexivity. Qed.

Example reducibility_controls :
  map (fun graph => let g := DigraphCode.prepare graph in
    LoopsCode.reducible_b g (fixture_tree g))
    [NestedLoop.graph; Irreducible.graph; Line.graph; SelfLoop.graph; EmptyGraph.graph] =
    [true; false; true; true; true].
Proof. vm_compute. reflexivity. Qed.

(* The old empty-rank nested-tree observation was false; the new result is true. *)

Example natural_inner :
  let g := DigraphCode.prepare NestedLoop.graph in
  let l := LoopsCode.forest g (fixture_tree g) in
  map (fun v => existsb (Pos.eqb v) (loop_body l 2)) [1; 2; 3; 4] =
    [false; true; true; false].
Proof. vm_compute. reflexivity. Qed.

Example natural_outer :
  let g := DigraphCode.prepare NestedLoop.graph in
  let l := LoopsCode.forest g (fixture_tree g) in
  map (fun v => existsb (Pos.eqb v) (loop_body l 1)) [1; 2; 3; 4] =
    [true; true; true; true].
Proof. vm_compute. reflexivity. Qed.

Example natural_self :
  let g := DigraphCode.prepare SelfLoop.graph in
  loop_body (LoopsCode.forest g (fixture_tree g)) 1 = [1].
Proof. vm_compute. reflexivity. Qed.

Example nested_headers :
  let g := DigraphCode.prepare NestedLoop.graph in
  let l := LoopsCode.forest g (fixture_tree g) in
  filter (fun v => match trie_get v (body l) with Some _ => true | None => false end)
    [1; 2; 3; 4] = [1; 2].
Proof. vm_compute. reflexivity. Qed.

Example empty_loop_projection :
  let g := DigraphCode.prepare EmptyGraph.graph in
  let l := LoopsCode.forest g (fixture_tree g) in
  trie_get 99 (body l) = None.
Proof. vm_compute. reflexivity. Qed.

Definition detached_predecessor := fixture_graph [1; 2; 3; 4]
  [(1, 2); (2, 3); (3, 2); (4, 3)].

Example unreachable_predecessor_excluded :
  let g := DigraphCode.prepare detached_predecessor in
  let l := LoopsCode.forest g (fixture_tree g) in
  existsb (Pos.eqb 4) (loop_body l 2) = false.
Proof. vm_compute. reflexivity. Qed.
