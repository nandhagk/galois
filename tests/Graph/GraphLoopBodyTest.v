(** * Natural-loop computation controls

    Actual reverse searches distinguish nested bodies, self loops and unknown IDs.
    For example, stopping at the inner header excludes its outer predecessor.
    Builds on: GraphLoopBody and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphLoopBody GraphFixtures.
From Galois.Tests.Graph Require Import GraphReducibilityTest.
Import List.ListNotations.
Open Scope positive_scope.

Example natural_inner :
  LoopBody.natural_loop Fixtures.NestedLoop.prepared 2 3 =
    FinSet.of_list positive_encoding [2; 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example natural_outer :
  LoopBody.natural_loop Fixtures.NestedLoop.prepared 1 4 =
    FinSet.of_list positive_encoding [1; 2; 3; 4].
Proof.
  vm_compute. reflexivity.
Qed.

Example natural_self :
  LoopBody.natural_loop Fixtures.SelfLoop.prepared 1 1 =
    FinSet.of_list positive_encoding [1].
Proof.
  vm_compute. reflexivity.
Qed.

Example natural_unknown_tail :
  LoopBody.natural_loop Fixtures.NestedLoop.prepared 2 99 =
    FinSet.of_list positive_encoding [2].
Proof.
  vm_compute. reflexivity.
Qed.

Example natural_empty_unknown_header :
  LoopBody.natural_loop Fixtures.Empty.prepared 99 99 =
    FinSet.of_list positive_encoding [99].
Proof.
  vm_compute. reflexivity.
Qed.

Example natural_inner_semantic_client :
  FinSet.mem positive_encoding 3 (LoopBody.natural_loop Fixtures.NestedLoop.prepared 2 3) = true <->
    LoopBody.natural_loop_spec Fixtures.NestedLoop.prepared 2 3 3.
Proof.
  apply LoopBody.natural_loop_exact; [exact Fixtures.NestedLoop.fixture_ready|].
  exists 3%nat. split; vm_compute; auto.
Qed.

Example natural_self_semantic_client :
  FinSet.mem positive_encoding 1 (LoopBody.natural_loop Fixtures.SelfLoop.prepared 1 1) = true <->
    LoopBody.natural_loop_spec Fixtures.SelfLoop.prepared 1 1 1.
Proof.
  apply LoopBody.natural_loop_exact; [exact Fixtures.SelfLoop.fixture_ready|].
  exists 1%nat. split; vm_compute; auto.
Qed.

Example natural_inner_has_real_back_edge :
  back_edge (Prepared.graph Fixtures.NestedLoop.prepared) (3%nat, 2%nat).
Proof.
  split; [vm_compute; auto|].
  apply (proj1 exact_tree_dominance_client). vm_compute. reflexivity.
Qed.

Example exact_dominator_and_back_edge_control :
  Dom.exact Fixtures.NestedLoop.prepared Fixtures.NestedLoop.tree /\
  back_edge (Prepared.graph Fixtures.NestedLoop.prepared) (3%nat, 2%nat) /\
  (forall v, FinSet.mem positive_encoding v
      (LoopBody.natural_loop Fixtures.NestedLoop.prepared 2 3) = true <->
    LoopBody.natural_loop_spec Fixtures.NestedLoop.prepared 2 3 v).
Proof.
  split; [exact Fixtures.NestedLoop.tree_exact|].
  split; [exact natural_inner_has_real_back_edge|].
  intro v. apply LoopBody.natural_loop_exact; [exact Fixtures.NestedLoop.fixture_ready|].
  exists 3%nat. split; vm_compute; auto.
Qed.
