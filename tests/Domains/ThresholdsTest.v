(** * Threshold construction examples

    Construction sorts and removes repeated thresholds before building a balanced tree.
    For example, a search around four in thresholds zero and eight returns those bounds.

    Groups:
    - [ConstructionTests] Building a tree from an unsorted list, with duplicates and edge sizes.
    - [SearchTests] The nearest threshold below and above a value.
    - [DepthTests] The depth of a tree built from a thousand thresholds.
    - [PreparationTests] Sorting and removing repeats before construction.
    - [LargeSetTests] Searches in a thousand and in a hundred and one thresholds.

    Builds on: Thresholds. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import Thresholds ThresholdsSig.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

(** Thresholds built from an unsorted list with a repeat. *)
Definition sample_thresholds := ThresholdsCode.make [8; 0; 8; -3; 0].
(** The thresholds zero to 999, built in increasing order. *)
Definition thousand_thresholds := ThresholdsCode.make (map Z.of_nat (seq 0 1000)).
(** The multiples of seven from zero to 700. *)
Definition seven_thresholds :=
  ThresholdsCode.make (map (fun n => 7 * Z.of_nat n) (seq 0 101)).

(** * Construction *)

Module ConstructionTests.

  (** Construction sorts the thresholds and drops the repeated zero and eight. *)
  Example make_sorts_and_removes_repeats :
    sample_thresholds = TNode (TNode TLeaf (-3) TLeaf) 0 (TNode TLeaf 8 TLeaf).
  Proof. vm_compute. reflexivity. Qed.

  (** Three copies of one threshold build a tree with that threshold once. *)
  Example equal_thresholds_collapse_to_one :
    ThresholdsCode.make [10; 10; 10] = TNode TLeaf 10 TLeaf.
  Proof. vm_compute. reflexivity. Qed.

  (** An unsorted list with negatives and repeats gives bounds among its distinct values. *)
  Example unsorted_with_negatives_builds_sorted_bounds :
    (ThresholdsCode.below (ThresholdsCode.make [20; -5; 10; 10; 0]) 7,
      ThresholdsCode.above (ThresholdsCode.make [20; -5; 10; 10; 0]) 7) =
    (Some 0, Some 10).
  Proof. vm_compute. reflexivity. Qed.

End ConstructionTests.

(** * Search *)

Module SearchTests.

  (** Below a value between two thresholds, the search returns the lower one. *)
  Example below_finds_lower_neighbour :
    ThresholdsCode.below sample_thresholds 4 = Some 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Above a value between two thresholds, the search returns the upper one. *)
  Example above_finds_upper_neighbour :
    ThresholdsCode.above sample_thresholds 4 = Some 8.
  Proof. vm_compute. reflexivity. Qed.

  (** Below a threshold itself, the search returns that threshold. *)
  Example below_threshold_is_itself :
    ThresholdsCode.below sample_thresholds (-3) = Some (-3).
  Proof. vm_compute. reflexivity. Qed.

  (** Above every threshold, the search returns no bound. *)
  Example above_past_largest_is_none :
    ThresholdsCode.above sample_thresholds 9 = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Searching an empty tree below a value returns no bound. *)
  Example below_empty_is_none :
    ThresholdsCode.below (ThresholdsCode.make []) 0 = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Searching an empty tree above a value returns no bound. *)
  Example above_empty_is_none :
    ThresholdsCode.above (ThresholdsCode.make []) 0 = None.
  Proof. vm_compute. reflexivity. Qed.

  (** A single threshold bounds a value below it from above only. *)
  Example singleton_above_lower_value :
    ThresholdsCode.above (ThresholdsCode.make [5]) 4 = Some 5.
  Proof. vm_compute. reflexivity. Qed.

  (** Below the only threshold itself, the search returns that threshold. *)
  Example singleton_below_at_threshold_is_itself :
    ThresholdsCode.below (ThresholdsCode.make [5]) 5 = Some 5.
  Proof. vm_compute. reflexivity. Qed.

  (** Below a value under the only threshold, the search returns no bound. *)
  Example singleton_below_lower_value_is_none :
    ThresholdsCode.below (ThresholdsCode.make [5]) 4 = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Above a value over the only threshold, the search returns no bound. *)
  Example singleton_above_higher_value_is_none :
    ThresholdsCode.above (ThresholdsCode.make [5]) 6 = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Searching the empty tree below a value returns no bound. *)
  Example empty_tree_below_is_none :
    ThresholdsCode.below TLeaf 77 = None.
  Proof. vm_compute. reflexivity. Qed.

  (** Searching the empty tree above a value returns no bound. *)
  Example empty_tree_above_is_none :
    ThresholdsCode.above TLeaf 77 = None.
  Proof. vm_compute. reflexivity. Qed.

End SearchTests.

(** * Depth *)

Module DepthTests.

  (** The tree of a thousand thresholds has depth ten. *)
  Example thousand_thresholds_depth_is_ten :
    Thresholds.depth thousand_thresholds = 10%nat.
  Proof. vm_compute. reflexivity. Qed.

  (** The depth of a thousand thresholds is at most ten. *)
  Example thousand_thresholds_depth_within_ten :
    Nat.leb (Thresholds.depth thousand_thresholds) 10 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** An empty set of thresholds has depth zero. *)
  Example empty_thresholds_have_depth_zero :
    Thresholds.depth (ThresholdsCode.make []) = 0%nat.
  Proof. vm_compute. reflexivity. Qed.

End DepthTests.

(** * Preparation *)

Module PreparationTests.

  (** Sorting and then removing repeats leaves the distinct values in order. *)
  Example sort_then_dedup_gives_distinct_sorted :
    ThresholdsCode.dedup_sorted (ThresholdsCode.msort [20; -5; 10; 10; 0]) =
    [-5; 0; 10; 20].
  Proof. vm_compute. reflexivity. Qed.

  (** Sorting keeps every copy of a repeated value. *)
  Example msort_keeps_duplicates :
    ThresholdsCode.msort [20; -5; 10; 10; 0] = [-5; 0; 10; 10; 20].
  Proof. vm_compute. reflexivity. Qed.

  (** Removing repeats from a sorted list keeps one copy of each value. *)
  Example dedup_sorted_keeps_one_copy :
    ThresholdsCode.dedup_sorted [-5; 0; 10; 10; 20] = [-5; 0; 10; 20].
  Proof. vm_compute. reflexivity. Qed.

End PreparationTests.

(** * Large sets *)

Module LargeSetTests.

  (** The largest threshold below a stored value is that value itself. *)
  Example below_stored_value_is_itself :
    ThresholdsCode.below thousand_thresholds 500 = Some 500.
  Proof. vm_compute. reflexivity. Qed.

  (** Above the largest stored value there is no bound. *)
  Example above_largest_stored_is_none :
    ThresholdsCode.above thousand_thresholds 1000 = None.
  Proof. vm_compute. reflexivity. Qed.

  (** A multiple of seven that is stored is its own lower bound. *)
  Example below_multiple_of_seven_is_itself :
    ThresholdsCode.below seven_thresholds 77 = Some 77.
  Proof. vm_compute. reflexivity. Qed.

  (** A multiple of seven that is stored is its own upper bound. *)
  Example above_multiple_of_seven_is_itself :
    ThresholdsCode.above seven_thresholds 77 = Some 77.
  Proof. vm_compute. reflexivity. Qed.

End LargeSetTests.
