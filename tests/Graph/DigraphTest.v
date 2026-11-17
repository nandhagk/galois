(** * Graph preparation observations

    Preparation retains adjacency and builds predecessor rows.
    For example, the diamond has two predecessors at its join.
    Builds on: graph fixtures and preparation. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Example diamond_succ : succs (base (DigraphCode.prepare Diamond.graph)) 1 = [2; 3].
Proof. vm_compute. reflexivity. Qed.

Example diamond_pred : preds (DigraphCode.prepare Diamond.graph) 4 = [2; 3].
Proof. vm_compute. reflexivity. Qed.

Example loop_indexes :
  (succs (base (DigraphCode.prepare SelfLoop.graph)) 1,
   preds (DigraphCode.prepare SelfLoop.graph) 1) = ([1], [1]).
Proof. vm_compute. reflexivity. Qed.

Example empty_indexes :
  (succs (base (DigraphCode.prepare EmptyGraph.graph)) 1,
   preds (DigraphCode.prepare EmptyGraph.graph) 1) = ([], []).
Proof. vm_compute. reflexivity. Qed.

(** Duplicate source rows and parallel edges retain all four predecessor occurrences. *)
Example repeated_occurrences :
  let g := Digraph [1; 1; 2] (PTrieCode.set 1 [2; 2] Empty) in
  let p := DigraphCode.prepare g in
  (preds p 2, nv p, ne p) = ([1; 1; 1; 1], 3%N, 4%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Binary carry propagation preserves cached counts and predecessor order. *)
Example counts_while_indexing :
  let g := fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (1, 4); (2, 3); (3, 4)] in
  let p := DigraphCode.prepare g in
  (nv p, ne p, preds p 4) = (4%N, 5%N, [1; 3]).
Proof.
  vm_compute. reflexivity.
Qed.
