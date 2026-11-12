(** * Stable bucket fixtures

    Grouping checks interleaved buckets, absent keys and empty input.
    For example, one bucket retains both its first and last input values.
    Builds on: Intern and Key. *)

From Stdlib Require Import List.
From Galois.Base Require Import Intern Key.
Import List.ListNotations.

Definition grouped := group_by BoolKeyCode.encode Nat.even [2; 1; 4; 3; 6].

Example index_order : find_group BoolKeyCode.encode true grouped = [2; 4; 6].
Proof.
  vm_compute. reflexivity.
Qed.

Example index_missing :
  find_group BoolKeyCode.encode false (group_by BoolKeyCode.encode Nat.even [2; 4]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example index_empty :
  find_group BoolKeyCode.encode true (group_by BoolKeyCode.encode Nat.even []) = [].
Proof.
  vm_compute. reflexivity.
Qed.
