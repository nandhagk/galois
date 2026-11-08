(** * Actual recursive hierarchy computations

    These tests run the well-founded producer directly on cyclic and boundary inputs.
    For example, removing the first header of the nested fixture exposes its inner cycle.
    Builds on: GraphHier and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphHierSpec GraphHier GraphFixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition unrestricted := Scope.Make FinSet.empty None.

Example actual_nested_tokens :
  Wto.of_forest (HierRun.compute Fixtures.NestedLoop.prepared unrestricted [1]) =
    Fixtures.NestedLoop.wto.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_self_loop :
  HierRun.compute Fixtures.SelfLoop.prepared unrestricted [1] =
    Hier.Cons (Hier.Component 1 Hier.Nil) Hier.Nil.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_empty :
  HierRun.compute Fixtures.Empty.prepared unrestricted [99; 99] = Hier.Nil.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_line_tokens :
  Wto.of_forest (HierRun.compute Fixtures.Line.prepared unrestricted [1]) = Fixtures.Line.wto.
Proof.
  vm_compute. reflexivity.
Qed.
