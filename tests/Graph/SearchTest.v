(** * Depth-first search observations

    Traces retain visit order and edge classifications.
    For example, a self-loop produces a back edge.
    Builds on: graph fixtures and search. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import Data Digraph SearchSig Search.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Example singleton_orders : entered (prepared_search_trace (DigraphCode.prepare Singleton.graph) [1]) = [1].
Proof. vm_compute. reflexivity. Qed.

Example self_loop_events :
  prepared_search_trace (DigraphCode.prepare SelfLoop.graph) [1] = [Enter 1; Edge Back 1 1; Leave 1].
Proof. vm_compute. reflexivity. Qed.

Example diamond_orders : entered (prepared_search_trace (DigraphCode.prepare Diamond.graph) [1]) = [1; 2; 4; 3].
Proof. vm_compute. reflexivity. Qed.

Example repeated_roots : entered (prepared_search_trace (DigraphCode.prepare Line.graph) [3; 1; 3]) = [3; 4; 1; 2].
Proof. vm_compute. reflexivity. Qed.

Example empty_roots : prepared_search_trace (DigraphCode.prepare Diamond.graph) [] = [].
Proof. vm_compute. reflexivity. Qed.
