(** * Actual recursive hierarchy computations

    These tests run the well-founded producer directly on cyclic and boundary inputs.
    For example, removing the first header of the nested fixture exposes its inner cycle.
    Builds on: GraphHier and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphHierSpec GraphHier
  GraphHierExact GraphFixtures.
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

Definition depth_three :=
  Fixtures.prepare [1%nat] [1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat]
    [(1%nat, 2%nat); (1%nat, 6%nat); (2%nat, 3%nat); (3%nat, 2%nat);
     (3%nat, 4%nat); (4%nat, 3%nat); (4%nat, 5%nat); (5%nat, 4%nat);
     (6%nat, 7%nat); (7%nat, 6%nat)].

Example actual_depth_three_and_separate_component :
  Wto.of_forest (HierRun.compute depth_three unrestricted [1]) =
    [Wto.WVertex 1; Wto.WOpen 6; Wto.WVertex 7; Wto.WClose;
     Wto.WOpen 2; Wto.WOpen 3; Wto.WOpen 4; Wto.WVertex 5;
     Wto.WClose; Wto.WClose; Wto.WClose].
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_depth_three_annotation :
  In (5, [4; 3; 2])
    (Wto.annotate [] (Wto.of_forest (HierRun.compute depth_three unrestricted [1]))).
Proof.
  vm_compute. tauto.
Qed.

Example nested_producer_exact :
  Hier.exact Fixtures.NestedLoop.prepared unrestricted [1]
    (HierRun.compute Fixtures.NestedLoop.prepared unrestricted [1]).
Proof.
  apply HierExact.compute_exact, Fixtures.NestedLoop.fixture_ready.
Qed.

Example scoped_unknown_repeated_producer_exact :
  let scope := Scope.Make (FinSet.of_list positive_encoding [1])
    (Some (FinSet.of_list positive_encoding [2; 3])) in
  Hier.exact Fixtures.NestedLoop.prepared scope [99; 2; 2; 1]
    (HierRun.compute Fixtures.NestedLoop.prepared scope [99; 2; 2; 1]).
Proof.
  apply HierExact.compute_exact, Fixtures.NestedLoop.fixture_ready.
Qed.

Example nested_two_reachable :
  Search.scoped_reachable Fixtures.NestedLoop.prepared unrestricted [1] 2.
Proof.
  apply (proj1 (Wto.covers _ _ _ _ Fixtures.NestedLoop.wto_valid 2)).
  vm_compute. tauto.
Qed.

Example nested_inner_cycle :
  Search.scoped_path Fixtures.NestedLoop.prepared unrestricted 2
    [(2%nat, 3%nat); (3%nat, 2%nat)] 2.
Proof.
  eapply Search.scoped_cons with (v := 3).
  - exists 2%nat. split; vm_compute; auto.
  - vm_compute. reflexivity.
  - exists 2%nat, 3%nat. repeat split; vm_compute; auto.
  - eapply Search.scoped_cons with (v := 2).
    + exists 3%nat. split; vm_compute; auto.
    + vm_compute. reflexivity.
    + exists 3%nat, 2%nat. repeat split; vm_compute; auto.
    + apply Search.scoped_nil.
      * exists 2%nat. split; vm_compute; auto.
      * vm_compute. reflexivity.
Qed.
