(** * Subtree table observations

    Examples exercise every constructor and preserve exact subtree positions.
    For example, an invalid third direction has no table binding.
    Builds on: FrameworkRegion. *)

From Stdlib Require Import List Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseMap.
From Galois.Program Require Import ProgramSkeleton.
From Galois.Framework Require Import FrameworkRegion.
Import List.ListNotations Cost.Notations Skeleton.

Definition size_alg : Region.algebra nat bool nat :=
  Region.of_pure (fun _ => 1) (fun a b => S (a + b)) (fun _ a b => S (a + b))
    S S (fun _ => 1) (fun _ _ => 1) (fun _ _ _ => 1).

Definition program : stmt nat bool :=
  Block (Seq (If true (Atom 7) (JumpIf false 0)) (Loop (JumpTable true [0; 1] 1))).

Example root_fold : Region.fold size_alg program = 7.
Proof.
  vm_compute; reflexivity.
Qed.

Example table_child :
  Map.get position_encoding [DBody; DFirst] (Region.table size_alg program) = Some 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example table_missing :
  Map.get position_encoding [DFirst] (Region.table size_alg program) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example leaf_table :
  Map.get position_encoding [] (Region.table size_alg (Atom 3)) = Some 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example jump_fold : Region.fold size_alg (Jump 0) = 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example leaf_visit_ticks :
  Cost.ticks (Region.visit_c size_alg (Atom 3)) = 3%N.
Proof.
  vm_compute; reflexivity.
Qed.
