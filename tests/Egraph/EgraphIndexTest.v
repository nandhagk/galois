(** * Reference memo-scan fixtures

    Index observations distinguish repeated classes from collisions.
    For example, the same key at two different classes yields a collision pair.
    Builds on: EgraphIndex. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseMap.
From Galois.Egraph Require Import EgraphIndex.
Import List.ListNotations.

Example repeated_class_is_not_a_collision :
  snd (fold_left EggIndex.step [(1%positive, 2%positive); (1%positive, 2%positive)]
    (Map.empty, None)) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example different_classes_collide :
  snd (fold_left EggIndex.step [(1%positive, 2%positive); (1%positive, 3%positive)]
    (Map.empty, None)) = Some (3%positive, 2%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_index_has_no_collision :
  snd (fold_left EggIndex.step [] (Map.empty, None)) = @None (positive * positive).
Proof.
  vm_compute. reflexivity.
Qed.
