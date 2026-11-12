(** * Graph preparation observations

    Preparation retains adjacency and builds predecessor rows.
    For example, the diamond has two predecessors at its join.
    Builds on: graph fixtures and preparation. *)

From Stdlib Require Import List PArith.
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
