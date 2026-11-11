(** * Cached checker and finite class-count controls

    The supplied partitions exercise equal additions, impurity and unlisted support.
    For example, merging an addition with an impure definition is rejected.
    Builds on: AnalysesEqualitySignature and AnalysesEqualityProblemTest. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseUnionFind.
From Galois.Lattice Require Import LatticePartition LatticePartitionOps.
From Galois.Program Require Import ProgramSsa.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualitySignature
  AnalysesEqualityClasses.
From Galois.Tests.Analyses.Equality Require Import AnalysesEqualityProblemTest.
Import List.ListNotations NumberingSignature EqualityFixture.

Definition discrete : partition_t nat_encoding :=
  Some (exist _ UnionFind.make (UnionFind.wf_make nat_encoding)).

Definition additions := partition_union nat_encoding nat_encoding_laws 2 3 discrete.
Definition impure_merge := partition_union nat_encoding nat_encoding_laws 2 4 discrete.
Definition wrong_block := partition_union nat_encoding nat_encoding_laws 5 7 discrete.
Definition unlisted_merge := partition_union nat_encoding nat_encoding_laws 9 10 discrete.

Definition empty_problem :=
  Numbering.of_pure
    (Ssa.of_pure cfg nat_encoding [] (fun _ => @Arbitrary nat nat nat)
      (fun _ => 0) (fun _ => []) (fun _ => []) (fun _ => @nil (unit * list nat)))
    nat_encoding (fun _ => true).

Example equal_additions_accepted : check problem additions = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example identity_accepted : check problem discrete = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example impure_merge_rejected : check problem impure_merge = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example other_block_rejected : check problem wrong_block = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example unlisted_class_rejected : check problem unlisted_merge = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example unreachable_rejected : check problem None = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_inventory_accepted : check empty_problem discrete = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_inventory_does_not_hide_unlisted_classes :
  check empty_problem unlisted_merge = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example signature_constructor_separation :
  eqb sig_encoding (SigOp 1 []) (SigParam 1 []) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example three_classes : NumberingClasses.classes Nat.eqb [0; 1; 0; 2; 1] = 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example class_count_increases :
  (NumberingClasses.classes (fun _ _ : nat => true) [0; 1; 2],
    NumberingClasses.classes Nat.eqb [0; 1; 2]) = (1, 3).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_class_count : NumberingClasses.classes Nat.eqb [] = 0.
Proof.
  vm_compute; reflexivity.
Qed.
