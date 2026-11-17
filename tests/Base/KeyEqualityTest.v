(** * Encoded equality tests

    Equality tests distinguish matching, different and boundary keys.
    For example, lists compare by their injective serialized codes.
    Builds on: Key and Code.

    Groups:
    - [ListTests] Equality of lists of natural numbers through their codes.
    - [PositiveKeyTests] Equality of positive scalar keys. *)

From Stdlib Require Import Bool List NArith.
From Galois.Base Require Import Key Code.
Import List.ListNotations.

(** * Fixtures *)

(** Lists of natural numbers, compared through their encoded keys. *)
Module NatList := ListKeyCode NatKeyCode.

(** * List equality *)

Module ListTests.

  (** Two lists with the same elements in the same order are equal. *)
  Example equal_lists_are_equal : NatList.eqb [1; 2]%nat [1; 2]%nat = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two lists with the same elements in a different order are not equal. *)
  Example different_order_is_not_equal : NatList.eqb [1; 2]%nat [2; 1]%nat = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The empty list is equal to itself. *)
  Example empty_lists_are_equal : NatList.eqb [] [] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ListTests.

(** * Positive key equality *)

Module PositiveKeyTests.

  Local Open Scope positive_scope.

  (** A positive key is equal to itself. *)
  Example same_positive_key_is_equal : PosKeyCode.eqb 1 1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Two different positive keys are not equal. *)
  Example different_positive_keys_differ : PosKeyCode.eqb 1 2 = false.
  Proof. vm_compute. reflexivity. Qed.

End PositiveKeyTests.
