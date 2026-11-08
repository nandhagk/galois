(** * Produced loop table observations

    Tables from the actual hierarchy distinguish nested ownership, acyclic nodes and missing IDs.
    For example, node 3 belongs to the inner loop headed by 2.
    Builds on: GraphLoopForest and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSccSpec
  GraphHierSpec GraphHier GraphHierExact GraphLoopForest GraphTarjan GraphTarjanExact GraphFixtures.
Import List.ListNotations.
Open Scope positive_scope.

Example nested_headers :
  Loops.headers (LoopForest.compute Fixtures.NestedLoop.prepared [1]) = [1; 2].
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_parents :
  let loops := LoopForest.compute Fixtures.NestedLoop.prepared [1] in
  map (fun v => Map.get positive_encoding v (Loops.loop_parent loops)) [1; 2; 3; 4; 99] =
    [None; Some 1; None; None; None].
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_innermost :
  let loops := LoopForest.compute Fixtures.NestedLoop.prepared [1] in
  map (fun v => Map.get positive_encoding v (Loops.innermost loops)) [1; 2; 3; 4; 99] =
    [Some 1; Some 2; Some 2; Some 1; None].
Proof.
  vm_compute. reflexivity.
Qed.

Example line_has_no_loops :
  let loops := LoopForest.compute Fixtures.Line.prepared [1] in
  Loops.headers loops = [] /\
    Map.get positive_encoding 2 (Loops.innermost loops) = None.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example self_loop_owns_itself :
  let loops := LoopForest.compute Fixtures.SelfLoop.prepared [1] in
  Loops.headers loops = [1] /\
    Map.get positive_encoding 1 (Loops.innermost loops) = Some 1 /\
    Map.get positive_encoding 1 (Loops.loop_parent loops) = None.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example empty_loop_projection :
  Loops.headers (LoopForest.compute Fixtures.Empty.prepared [99]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Definition self_forest := Hier.Cons (Hier.Component 1 Hier.Nil) Hier.Nil.
Definition unrestricted := Scope.Make FinSet.empty None.

Local Lemma self_exact :
  Hier.exact Fixtures.SelfLoop.prepared unrestricted [1] self_forest.
Proof.
  assert (Hcomponents :
    Scc.components (Tarjan.compute Fixtures.SelfLoop.prepared unrestricted [1]) = [[1]]).
  { vm_compute. reflexivity. }
  assert (Hcover : forall v, In v [1] <->
    Search.scoped_reachable Fixtures.SelfLoop.prepared unrestricted [1] v).
  { intro v.
    pose proof (TarjanExact.partition_complete Fixtures.SelfLoop.prepared unrestricted [1] v
      Fixtures.SelfLoop.fixture_ready) as Hcoverage.
    rewrite Hcomponents in Hcoverage. exact Hcoverage. }
  constructor.
  - constructor; [intro Hfalse; contradiction|constructor].
  - exact Hcover.
  - apply Hier.blocks_component.
    + apply (TarjanExact.block_exact Fixtures.SelfLoop.prepared unrestricted [1] [1]
        Fixtures.SelfLoop.fixture_ready).
      rewrite Hcomponents. now left.
    + right. exists (1%nat, 1%nat). exists 1%nat, 1%nat.
      repeat split; vm_compute; auto.
    + intros _. split; [now left|left; now left].
    + apply HierExact.empty_roots_exact.
    + constructor.
  - intros u e v Harc Hu Hv. right.
    exists (Hier.Component 1 Hier.Nil). split; [constructor|exact (conj Hu Hv)].
Qed.

Example actual_self_producer_exact :
  Loops.exact Fixtures.SelfLoop.prepared unrestricted [1]
    (HierRun.compute Fixtures.SelfLoop.prepared unrestricted [1])
    (LoopForest.compute Fixtures.SelfLoop.prepared [1]).
Proof.
  rewrite LoopForest.compute_equation.
  apply LoopForest.of_forest_exact.
  fold unrestricted.
  assert (Hforest : HierRun.compute Fixtures.SelfLoop.prepared unrestricted [1] = self_forest).
  { vm_compute. reflexivity. }
  rewrite Hforest. exact self_exact.
Qed.

Example self_loop_parent_and_owner_semantic_client :
  Map.get positive_encoding 1 (Loops.innermost (LoopForest.of_forest self_forest)) = Some 1.
Proof.
  apply (proj2 (Loops.innermost_exact _ _ _ _ _
    (LoopForest.of_forest_exact _ _ _ _ self_exact) 1 1)).
  exists []. vm_compute. now left.
Qed.

Example nested_producer_exact :
  Loops.exact Fixtures.NestedLoop.prepared unrestricted [1]
    (HierRun.compute Fixtures.NestedLoop.prepared unrestricted [1])
    (LoopForest.compute Fixtures.NestedLoop.prepared [1]).
Proof.
  apply LoopForest.compute_exact, Fixtures.NestedLoop.fixture_ready.
Qed.
