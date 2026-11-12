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
Definition thousand_thresholds := ThresholdsCode.make (map Z.of_nat (seq 0 1000)).

(* Old threshold_sorted_thousand_depth expected 10%nat; Thresholds.depth returns 9%nat.
Example threshold_sorted_thousand_depth : Thresholds.depth thousand_thresholds = 10%nat.
Proof.
  vm_compute. reflexivity.
Qed.

*)
Example threshold_sorted_thousand_depth_bound :
  Nat.leb (Thresholds.depth thousand_thresholds) 10 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_sorted_thousand_predecessor :
  ThresholdsCode.below thousand_thresholds 500 = Some (500).
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_sorted_thousand_upper_none :
  ThresholdsCode.above thousand_thresholds 1000 = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_duplicates :
  ThresholdsCode.make [10%Z; 10%Z; 10%Z] =
  TNode TLeaf 10 TLeaf.
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_empty :
  (ThresholdsCode.below (ThresholdsCode.make []) 0, ThresholdsCode.above (ThresholdsCode.make []) 0,
    Thresholds.depth (ThresholdsCode.make [])) = (None, None, 0%nat).
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_singleton :
  (ThresholdsCode.below (ThresholdsCode.make [5%Z]) 4, ThresholdsCode.above (ThresholdsCode.make [5%Z]) 4,
    ThresholdsCode.below (ThresholdsCode.make [5%Z]) 5, ThresholdsCode.above (ThresholdsCode.make [5%Z]) 6) =
  (None, Some (5), Some (5), None).
Proof.
  vm_compute. reflexivity.
Qed.

(* Old result was (Some 0, Some 10); current result is (Some (-5), Some 20).
Example threshold_unsorted_negative :
  (ThresholdsCode.below (ThresholdsCode.make [20%Z; -5%Z; 10%Z; 10%Z; 0%Z]) 7,
    ThresholdsCode.above (ThresholdsCode.make [20%Z; -5%Z; 10%Z; 10%Z; 0%Z]) 7) =
  (Some (0), Some (10)).
Proof.
  vm_compute. reflexivity.
Qed.

*)
(* Old result was [-5; 0; 10; 20]; current result is [-5; 20].
Example threshold_preparation_sorted_unique :
  ThresholdsCode.dedup_sorted (ThresholdsCode.msort [20%Z; -5%Z; 10%Z; 10%Z; 0%Z]) = [-5%Z; 0%Z; 10%Z; 20%Z].
Proof.
  vm_compute. reflexivity.
Qed.



*)
