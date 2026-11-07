(** * Frontier sweep fixtures

    Named certificates exercise branches, loops and separate entry roots.
    For example, a two-entry join lies in both entries' frontiers.
    Builds on: GraphFrontierSweep and GraphFixtures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphFixtures GraphCheckDom
  GraphFrontierSweep.
Import List.ListNotations.

Definition row {V E} (p : Prepared.t V E) t i :=
  FinSet.elements (Map.find_or positive_encoding FinSet.empty i
    (FrontierSweep.dominance_frontier p t)).

Example diamond_checked :
  DomCheck.check Fixtures.Diamond.prepared Fixtures.Diamond.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_frontiers :
  map (row Fixtures.Diamond.prepared Fixtures.Diamond.tree) [1; 2; 3; 4]%positive =
    [[]; [4]; [4]; []]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_checked :
  DomCheck.check Fixtures.JoinLoop.prepared Fixtures.JoinLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_frontiers :
  map (row Fixtures.JoinLoop.prepared Fixtures.JoinLoop.tree) [1; 2; 3; 4]%positive =
    [[]; [4]; [4]; [4]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_checked :
  DomCheck.check Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_frontiers :
  map (row Fixtures.TwoEntry.prepared Fixtures.TwoEntry.tree) [1; 2; 3; 4]%positive =
    [[3]; [3]; []; []]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_checked :
  DomCheck.check Fixtures.Line.prepared Fixtures.Line.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_frontiers :
  map (row Fixtures.Line.prepared Fixtures.Line.tree) [1; 2; 3; 4]%positive =
    [[]; []; []; []].
Proof.
  vm_compute. reflexivity.
Qed.

Definition empty_graph := Fixtures.prepare [] [] [].
Definition empty_parents := Fixtures.parents [].
Definition empty_tree := DomCheck.of_parents empty_graph empty_parents.

Example empty_checked : DomCheck.check empty_graph empty_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_frontier :
  Map.elements (FrontierSweep.dominance_frontier empty_graph empty_tree) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_frontier_ticks :
  Cost.ticks (FrontierSweep.dominance_frontier_c empty_graph empty_tree) = 1%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition singleton_graph := Fixtures.prepare [1] [1] [].
Definition singleton_tree := DomCheck.of_parents singleton_graph empty_parents.

Example singleton_checked : DomCheck.check singleton_graph empty_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_frontier :
  Map.elements (FrontierSweep.dominance_frontier singleton_graph singleton_tree) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example rejected_parents :
  DomCheck.check Fixtures.Diamond.prepared (Fixtures.parents [(4, 2)]%positive) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_row :
  row Fixtures.Diamond.prepared Fixtures.Diamond.tree 42 = [].
Proof.
  vm_compute. reflexivity.
Qed.
