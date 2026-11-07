(** * Orders, cycle witnesses and selected paths

    These computations observe the actual RPO, back-edge label and parent-path label.
    For example, the parallel-edge path uses the first label selected by DFS.
    Builds on: GraphSearchOrder and GraphSearchTest. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchOrder.
From Galois.Tests.Graph Require Import GraphSearchTest.
Import List.ListNotations.

Example diamond_rpo :
  SearchOrder.rpo
    (SearchRun.dfs SearchFixtures.diamond SearchFixtures.unrestricted [1]%positive) =
    [1; 3; 2; 4]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_topological :
  SearchOrder.topological SearchFixtures.diamond SearchFixtures.unrestricted [1]%positive =
    inl [1; 3; 2; 4]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_back_witness :
  SearchOrder.topological SearchFixtures.self_loop SearchFixtures.unrestricted [1]%positive =
    inr ((1, 1)%nat, 1%positive, 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_topological :
  SearchOrder.topological SearchFixtures.diamond SearchFixtures.unrestricted [] = inl [].
Proof.
  vm_compute. reflexivity.
Qed.

Example blocked_topological :
  SearchOrder.topological SearchFixtures.self_loop SearchFixtures.blocked_one [1]%positive =
    inl [].
Proof.
  vm_compute. reflexivity.
Qed.

Example selected_parallel_path :
  SearchOrder.tree_path SearchFixtures.parallel
    (SearchRun.dfs SearchFixtures.parallel SearchFixtures.unrestricted [1]%positive)
    2%positive = Some [10].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_tree_path :
  SearchOrder.tree_path SearchFixtures.diamond
    (SearchRun.dfs SearchFixtures.diamond SearchFixtures.unrestricted [1]%positive)
    4%positive = Some [(1, 2); (2, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example root_empty_path :
  SearchOrder.tree_path SearchFixtures.single
    (SearchRun.dfs SearchFixtures.single SearchFixtures.unrestricted [1]%positive)
    1%positive = Some [].
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_path :
  SearchOrder.tree_path SearchFixtures.diamond
    (SearchRun.dfs SearchFixtures.diamond SearchFixtures.unrestricted [1]%positive)
    99%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition malformed_result : Search.result nat :=
  Search.Result [1]%positive [1]%positive
    (Map.set positive_encoding 1%positive (10, 1%positive) Map.empty)
    Map.empty Map.empty (FinSet.of_list positive_encoding [1]%positive).

Example cyclic_parent_map_rejected :
  SearchOrder.tree_path SearchFixtures.parallel malformed_result 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.
