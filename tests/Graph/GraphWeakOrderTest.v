(** * Produced weak-order and rank observations

    The independent checker accepts the actual hierarchy producer on every named fixture.
    For example, the irreducible cycle still gets a headed weak-order component.
    Builds on: GraphWeakOrder, GraphCheckWto and GraphFixtures. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphPrepared GraphHierSpec GraphWeakOrder GraphCheckWto
  GraphFixtures GraphHierCycles.
From Galois.Tests.Graph Require Import GraphHierTest.
Import List.ListNotations.
Open Scope positive_scope.

Definition fixture_family :=
  [Fixtures.Line.prepared; Fixtures.Diamond.prepared; Fixtures.JoinLoop.prepared;
   Fixtures.NestedLoop.prepared; Fixtures.TwoEntry.prepared; Fixtures.SelfLoop.prepared;
   Fixtures.Irreducible.prepared; Fixtures.Empty.prepared; Fixtures.Singleton.prepared;
   Fixtures.Unreachable.prepared].

Example every_fixture_accepts :
  forallb (fun p => WtoCheck.check p (Prepared.entry_ids p)
    (WeakOrder.compute p (Prepared.entry_ids p))) fixture_family = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_tokens_agree :
  WeakOrder.compute Fixtures.NestedLoop.prepared [1] = Fixtures.NestedLoop.wto.
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_tokens :
  WeakOrder.compute Fixtures.Irreducible.prepared [1] = Fixtures.Irreducible.wto.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_ranks :
  let w := WeakOrder.compute Fixtures.NestedLoop.prepared [1] in
  map (fun v => Map.get positive_encoding v (WeakOrder.ranks w)) [1; 2; 3; 4; 99] =
    [Some 1; Some 2; Some 3; Some 4; None].
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_heads :
  let w := WeakOrder.compute Fixtures.NestedLoop.prepared [1] in
  map (WeakOrder.heads_of w) [1; 2; 3; 4; 99] =
    [Some [1]; Some [2; 1]; Some [2; 1]; Some [1]; None].
Proof.
  vm_compute. reflexivity.
Qed.

Example acyclic_heads_and_unknown :
  let w := WeakOrder.compute Fixtures.Line.prepared [1] in
  map (WeakOrder.heads_of w) [2; 99] = [Some []; None].
Proof.
  vm_compute. reflexivity.
Qed.

Example forward_rank_client :
  exists i j,
    Map.get positive_encoding 2 (WeakOrder.ranks Fixtures.Line.wto) = Some i /\
    Map.get positive_encoding 3 (WeakOrder.ranks Fixtures.Line.wto) = Some j /\
    (i < j)%positive.
Proof.
  apply (WeakOrder.ranks_before Fixtures.Line.wto 2 3).
  - exact (Wto.unique _ _ _ _ Fixtures.Line.wto_valid).
  - exists [1], [], [4]. reflexivity.
Qed.

Example nested_producer_valid :
  Wto.valid Fixtures.NestedLoop.prepared [1]
    (WeakOrder.compute Fixtures.NestedLoop.prepared [1]).
Proof.
  apply WeakOrder.compute_valid, Fixtures.NestedLoop.fixture_ready.
Qed.

Example inner_cycle_common_head_client :
  exists h, In h (HierCycles.points Fixtures.NestedLoop.prepared 2
      [(2%nat, 3%nat); (3%nat, 2%nat)]) /\
    forall x, In x (HierCycles.points Fixtures.NestedLoop.prepared 2
      [(2%nat, 3%nat); (3%nat, 2%nat)]) ->
      exists stack, In (x, stack)
        (Wto.annotate [] (WeakOrder.compute Fixtures.NestedLoop.prepared [1])) /\ In h stack.
Proof.
  apply (WeakOrder.cycles_have_head Fixtures.NestedLoop.prepared [1] 2
    [(2%nat, 3%nat); (3%nat, 2%nat)] Fixtures.NestedLoop.fixture_ready
    nested_two_reachable nested_inner_cycle).
  discriminate.
Qed.
