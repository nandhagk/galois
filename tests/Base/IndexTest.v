(** * Stable bucket fixtures

    Grouping checks interleaved buckets, absent keys and empty input.
    For example, one bucket retains both its first and last input values.
    Builds on: Intern and Key.

    Groups:
    - [GroupTests] The members of one bucket, in input order, for each input. *)

From Stdlib Require Import List.
From Galois.Base Require Import Intern Key.
Import List.ListNotations.

(** * Fixtures *)

(** The numbers 2, 1, 4, 3 and 6 grouped by parity. *)
Definition grouped := group_by BoolKeyCode.encode Nat.even [2; 1; 4; 3; 6].

(** * Group *)

Module GroupTests.

  (** The even bucket keeps its members in input order. *)
  Example bucket_keeps_input_order :
    find_group BoolKeyCode.encode true grouped = [2; 4; 6].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A bucket that no input reaches is empty. *)
  Example absent_bucket_is_empty :
    find_group BoolKeyCode.encode false (group_by BoolKeyCode.encode Nat.even [2; 4]) = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Grouping an empty input gives an empty bucket. *)
  Example empty_input_gives_empty_bucket :
    find_group BoolKeyCode.encode true (group_by BoolKeyCode.encode Nat.even []) = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End GroupTests.

(* BaseIndexTest.index_ticks and index_singleton_ticks retire with Cost.ticks.
   Their expected values were 0%N and 16%N. Grouping values use group_by above. *)
