(** * Threshold construction examples

    Construction sorts and removes repeated thresholds before building a balanced tree.
    For example, a search around four in thresholds zero and eight returns those bounds.
    Builds on: Thresholds. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import Thresholds ThresholdsSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Example make_sorted_unique :
  ThresholdsCode.make [8; 0; 8; -3; 0] =
    TNode (TNode TLeaf (-3) TLeaf) 0 (TNode TLeaf 8 TLeaf).
Proof. vm_compute. reflexivity. Qed.

Example search_boundaries :
  let t := ThresholdsCode.make [8; 0; 8; -3; 0] in
  (ThresholdsCode.below t 4, ThresholdsCode.above t 4,
   ThresholdsCode.below t (-3), ThresholdsCode.above t 9) =
  (Some 0, Some 8, Some (-3), None).
Proof. vm_compute. reflexivity. Qed.
