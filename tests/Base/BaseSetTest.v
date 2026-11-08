(** * Finite-set fixtures

    These fixtures cover duplicate keys, set operations and empty input.
    For example, removing a singleton's member empties it.
    Builds on: BaseSet and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
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
    (FinSet.add positive_encoding 1%positive FinSet.empty)) = 3%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_add_client {K} (enc : encoding K) k a (s : FinSet.t K) :
  FinSet.mem enc k (FinSet.add enc a s) = (eqb enc k a || FinSet.mem enc k s)%bool.
Proof.
  apply FinSet.mem_add_raw.
Qed.

Definition collision_encoding : encoding positive := of_pure (fun _ => 1%positive).
Definition malformed_storage := FinSet.add collision_encoding 2%positive FinSet.empty.

Example malformed_set_control : ~ FinSet.wf positive_encoding malformed_storage.
Proof.
  intro Hwf.
  pose proof (Hwf 1%positive 2%positive tt ltac:(vm_compute; reflexivity)) as Hcode.
  vm_compute in Hcode. discriminate.
Qed.

Example malformed_set_update_client :
  FinSet.mem positive_encoding 1%positive
    (FinSet.add positive_encoding 3%positive malformed_storage) = true.
Proof.
  rewrite FinSet.mem_add_raw. vm_compute. reflexivity.
Qed.

Example colliding_membership_client :
  FinSet.mem collision_encoding 1%positive
    (FinSet.add collision_encoding 2%positive FinSet.empty) = true.
Proof.
  rewrite FinSet.mem_add_raw. vm_compute. reflexivity.
Qed.
