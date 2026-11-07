(** * Partition update fixtures

    Tests cover union, compression and forgetting a class's middle key.
    For example, forgetting 2 from [1 = 2 = 3] retains [1 = 3].
    Builds on: LatticePartitionOps and LatticePartitionTest. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseUnionFind.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticePartition LatticePartitionOps.
From Galois.Tests.Lattice Require Import LatticePartitionTest.
Import List.ListNotations.
Open Scope positive_scope.

Definition fixture_union := partition_union positive_encoding positive_encoding_laws.
Definition fixture_forget := partition_forget positive_encoding positive_encoding_laws.
Definition fixture_test := partition_test positive_encoding positive_encoding_laws.

Example partition_union_then_test :
  (fst (fixture_test 1 4 (fixture_union 3 4 partition_three)),
    fst (fixture_test 1 99 (fixture_union 3 4 partition_three))) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_forget_middle :
  let forgotten := fixture_forget 2 partition_three in
  (fst (fixture_test 1 3 forgotten), fst (fixture_test 1 2 forgotten),
    fst (fixture_test 2 3 forgotten), fst (fixture_test 2 2 forgotten)) =
    (true, false, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_forget_root :
  let forgotten := fixture_forget 1 partition_three in
  (fst (fixture_test 2 3 forgotten), fst (fixture_test 1 2 forgotten)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_forget_unknown :
  let forgotten := fixture_forget 99 partition_three in
  (fst (fixture_test 1 3 forgotten), fst (fixture_test 99 1 forgotten)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_unreachable_updates :
  (fixture_union 1 2 None, fixture_forget 2 None, fixture_test 1 2 None) =
    (None, None, (true, None)).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_test_preserves_classes :
  let compressed := snd (fixture_test 3 1 partition_three) in
  (fst (fixture_test 1 2 compressed), fst (fixture_test 1 3 compressed),
    fst (fixture_test 1 4 compressed)) = (true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_failed_test_preserves_returned_classes :
  let tested := fixture_test 3 4 partition_three in
  let compressed := snd tested in
  (fst tested, fst (fixture_test 1 2 compressed), fst (fixture_test 1 3 compressed),
    fst (fixture_test 3 4 compressed)) = (false, true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_unknown_test_preserves_returned_classes :
  let tested := fixture_test 99 3 partition_three in
  let compressed := snd tested in
  (fst tested, fst (fixture_test 1 2 compressed), fst (fixture_test 1 3 compressed),
    fst (fixture_test 99 99 compressed), fst (fixture_test 99 1 compressed)) =
    (false, true, true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_reached_ticks :
  (Cost.ticks (partition_join_c positive_encoding positive_encoding_laws
      partition_two partition_three),
    Cost.ticks (partition_forget_c positive_encoding positive_encoding_laws 2 partition_three),
    Cost.ticks (partition_test_c positive_encoding positive_encoding_laws 3 1 partition_three)) =
    (471%N, 176%N, 23%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_update_ticks :
  (Cost.ticks (partition_union_c positive_encoding positive_encoding_laws 1 2 partition_discrete),
    Cost.ticks (partition_forget_c positive_encoding positive_encoding_laws 1 None),
    Cost.ticks (partition_test_c positive_encoding positive_encoding_laws 1 2 None)) =
    (32%N, 1%N, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.
