(** * Finite-set fixtures

    These fixtures cover duplicate keys, set operations and empty input.
    For example, removing a singleton's member empties it.
    Builds on: BaseSet and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
Import List.ListNotations.

Definition left_set := FinSet.of_list positive_encoding [1; 2; 1]%positive.
Definition right_set := FinSet.of_list positive_encoding [2; 3]%positive.

Example set_members : FinSet.elements left_set = [2; 1]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example set_intersection :
  FinSet.elements (FinSet.inter left_set right_set) = [2]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example set_difference :
  FinSet.elements (FinSet.diff left_set right_set) = [1]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example set_nonmember : FinSet.mem positive_encoding 3%positive left_set = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example set_empty : FinSet.equal (FinSet.of_list positive_encoding []) FinSet.empty = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example set_ticks :
  Cost.ticks (FinSet.mem_c positive_encoding 1%positive
    (FinSet.add positive_encoding 1%positive FinSet.empty)) = 4%N.
Proof.
  vm_compute. reflexivity.
Qed.
