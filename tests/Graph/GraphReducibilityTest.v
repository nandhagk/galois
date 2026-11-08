(** * Exact-tree reducibility observations

    Actual event visitors distinguish nested loops from irreducible cycle entries.
    For example, replacing the exact nested-loop tree by an empty tree changes acceptance.
    Builds on: GraphReducibility and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphHierSpec
  GraphReducibility GraphFixtures.
Import List.ListNotations.
Open Scope positive_scope.

Example nested_reducible :
  Reducibility.test Fixtures.NestedLoop.prepared Fixtures.NestedLoop.tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_rejected :
  Reducibility.test Fixtures.Irreducible.prepared Fixtures.Irreducible.tree = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_reducible :
  Reducibility.test Fixtures.Line.prepared Fixtures.Line.tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_reducible :
  Reducibility.test Fixtures.SelfLoop.prepared Fixtures.SelfLoop.tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_reducible :
  Reducibility.test Fixtures.Empty.prepared Fixtures.Empty.tree = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example missing_ranks_do_not_accept_cycle :
  Reducibility.test Fixtures.NestedLoop.prepared (Dom.Tree Map.empty Map.empty Map.empty) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example exact_tree_dominance_client :
  Reducibility.dominates Fixtures.NestedLoop.tree 2 3 = true <->
    GraphDomSpec.dominates (Prepared.graph Fixtures.NestedLoop.prepared) 2%nat 3%nat.
Proof.
  apply (Reducibility.dominates_correct Fixtures.NestedLoop.prepared
    Fixtures.NestedLoop.tree 3%nat 2%nat 3 2 Fixtures.NestedLoop.fixture_ready
    Fixtures.NestedLoop.tree_exact).
  - apply reachable_iff_path. exists 1%nat, [(1%nat, 2%nat); (2%nat, 3%nat)].
    split; [vm_compute; now left|].
    apply (@path_cons nat (nat * nat) (Prepared.graph Fixtures.NestedLoop.prepared)
      (1%nat, 2%nat) [(2%nat, 3%nat)] 3%nat).
    + vm_compute. auto.
    + apply (@path_cons nat (nat * nat) (Prepared.graph Fixtures.NestedLoop.prepared)
        (2%nat, 3%nat) [] 3%nat); [vm_compute; auto|constructor].
  - apply reachable_iff_path. exists 1%nat, [(1%nat, 2%nat)].
    split; [vm_compute; now left|].
    apply (@path_cons nat (nat * nat) (Prepared.graph Fixtures.NestedLoop.prepared)
      (1%nat, 2%nat) [] 2%nat); [vm_compute; auto|constructor].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Example nested_semantically_reducible : reducible (Prepared.graph Fixtures.NestedLoop.prepared).
Proof.
  apply (Reducibility.reducible_b_sound Fixtures.NestedLoop.prepared Fixtures.NestedLoop.tree
    Fixtures.NestedLoop.fixture_ready Fixtures.NestedLoop.tree_exact).
  exact nested_reducible.
Qed.

Example irreducible_semantic_rejection :
  ~ reducible (Prepared.graph Fixtures.Irreducible.prepared).
Proof.
  intro Hreducible.
  apply (proj2 (Reducibility.reducible_b_correct Fixtures.Irreducible.prepared
    Fixtures.Irreducible.tree Fixtures.Irreducible.fixture_ready
    Fixtures.Irreducible.tree_exact)) in Hreducible.
  rewrite irreducible_rejected in Hreducible. discriminate.
Qed.

Example empty_semantically_reducible : reducible (Prepared.graph Fixtures.Empty.prepared).
Proof.
  apply (Reducibility.reducible_b_sound Fixtures.Empty.prepared Fixtures.Empty.tree
    Fixtures.Empty.fixture_ready Fixtures.Empty.tree_exact).
  exact empty_reducible.
Qed.
