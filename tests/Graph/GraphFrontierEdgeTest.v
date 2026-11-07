(** * Dominating incoming-edge fixtures

    Checked trees distinguish first-arrival edges from loop edges and parallel labels.
    For example, two parallel incoming labels prevent a singleton choice.
    Builds on: GraphFrontierEdge and GraphFixtures. *)

From Stdlib Require Import List PArith Arith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphFixtures GraphCheckDom
  GraphFrontierEdge.
Import List.ListNotations.

Example line_checked :
  DomCheck.check Fixtures.Line.prepared Fixtures.Line.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_incoming_edges :
  Map.elements (FrontierEdge.edge_dominators Fixtures.Line.prepared Fixtures.Line.tree) =
    [(4%positive, (3, 4)); (2%positive, (1, 2)); (3%positive, (2, 3))].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_checked :
  DomCheck.check Fixtures.Diamond.prepared Fixtures.Diamond.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_incoming_edges :
  Map.elements (FrontierEdge.edge_dominators Fixtures.Diamond.prepared Fixtures.Diamond.tree) =
    [(2%positive, (1, 2)); (3%positive, (1, 3))].
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_checked :
  DomCheck.check Fixtures.NestedLoop.prepared Fixtures.NestedLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_incoming_edges :
  Map.elements (FrontierEdge.edge_dominators
    Fixtures.NestedLoop.prepared Fixtures.NestedLoop.tree) =
    [(4%positive, (3, 4)); (2%positive, (1, 2)); (3%positive, (2, 3))].
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_checked :
  DomCheck.check Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_incoming_edges :
  Map.elements (FrontierEdge.edge_dominators Fixtures.TwoEntry.prepared Fixtures.TwoEntry.tree) =
    [(4%positive, (3, 4))].
Proof.
  vm_compute. reflexivity.
Qed.

Definition parallel_graph :=
  Graph.of_pure [1] [1; 2] (fun n => if Nat.eqb n 1 then [11; 12] else [])
    (fun _ => 1) (fun _ => 2).
Definition parallel := Prepared.prepare nat_encoding parallel_graph.
Definition parallel_parents := Fixtures.parents [(2, 1)]%positive.
Definition parallel_tree := DomCheck.of_parents parallel parallel_parents.

Example parallel_checked : DomCheck.check parallel parallel_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example parallel_incoming_edges :
  Map.elements (FrontierEdge.edge_dominators parallel parallel_tree) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Definition disconnected := Fixtures.prepare [1] [1; 2] [].
Definition no_parents := Fixtures.parents [].
Definition disconnected_tree := DomCheck.of_parents disconnected no_parents.

Example disconnected_checked : DomCheck.check disconnected no_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example unreachable_no_binding :
  Map.get positive_encoding 2%positive
    (FrontierEdge.edge_dominators disconnected disconnected_tree) =
    None.
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_no_binding :
  Map.get positive_encoding 42%positive (FrontierEdge.edge_dominators
    Fixtures.Line.prepared Fixtures.Line.tree) = None.
Proof.
  vm_compute. reflexivity.
Qed.
