(** * Candidate weak-order checks

    Every token list is hand-written and checked without a hierarchy producer.
    For example, the irreducible triangle admits an enclosing head at node 2.
    Builds on: GraphCheckWto and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import GraphPrepared GraphHierSpec GraphCheckWto GraphFixtures.
Import List.ListNotations.
Open Scope positive_scope.

Example accepts_line :
  WtoCheck.check Fixtures.Line.prepared [1] Fixtures.Line.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_diamond :
  WtoCheck.check Fixtures.Diamond.prepared [1] Fixtures.Diamond.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_join_loop :
  WtoCheck.check Fixtures.JoinLoop.prepared [1] Fixtures.JoinLoop.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_nested_loop :
  WtoCheck.check Fixtures.NestedLoop.prepared [1] Fixtures.NestedLoop.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_two_entries :
  WtoCheck.check Fixtures.TwoEntry.prepared [1; 2] Fixtures.TwoEntry.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_self_loop :
  WtoCheck.check Fixtures.SelfLoop.prepared [1] Fixtures.SelfLoop.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_irreducible :
  WtoCheck.check Fixtures.Irreducible.prepared [1] Fixtures.Irreducible.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_empty :
  WtoCheck.check Fixtures.Empty.prepared [] Fixtures.Empty.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_singleton :
  WtoCheck.check Fixtures.Singleton.prepared [1] Fixtures.Singleton.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example excludes_unreachable :
  WtoCheck.check Fixtures.Unreachable.prepared [1] Fixtures.Unreachable.wto = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_missing_node :
  WtoCheck.check Fixtures.Line.prepared [1] [Wto.WVertex 1; Wto.WVertex 2; Wto.WVertex 3] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unmatched_close :
  WtoCheck.check Fixtures.Singleton.prepared [1] [Wto.WVertex 1; Wto.WClose] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unmatched_open :
  WtoCheck.check Fixtures.Singleton.prepared [1] [Wto.WOpen 1] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_duplicate :
  WtoCheck.check Fixtures.Singleton.prepared [1] [Wto.WVertex 1; Wto.WVertex 1] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_backward_edge :
  WtoCheck.check Fixtures.Line.prepared [1]
    [Wto.WVertex 1; Wto.WVertex 3; Wto.WVertex 2; Wto.WVertex 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unheaded_self_loop :
  WtoCheck.check Fixtures.SelfLoop.prepared [1] [Wto.WVertex 1] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unknown_id :
  WtoCheck.check Fixtures.Singleton.prepared [1] [Wto.WVertex 1; Wto.WVertex 9] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unreachable_node :
  WtoCheck.check Fixtures.Unreachable.prepared [1]
    (Fixtures.Unreachable.wto ++ [Wto.WVertex 5]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example ignores_unknown_root :
  WtoCheck.check Fixtures.Singleton.prepared [9] [] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_alternative_roots :
  WtoCheck.check Fixtures.Diamond.prepared [2] [Wto.WVertex 2; Wto.WVertex 4] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_scoped_coverage_as_unrestricted :
  WtoCheck.check Fixtures.Diamond.prepared [1] [Wto.WVertex 1] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_forest_boundary :
  WtoCheck.check_forest Fixtures.Empty.prepared [] Hier.Nil = true.
Proof.
  vm_compute. reflexivity.
Qed.
