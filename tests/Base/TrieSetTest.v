(** * Finite-set fixtures

    These fixtures cover duplicate keys, set operations and empty input.
    For example, removing a singleton's member empties it.
    Builds on: TrieSet and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key TrieSet Trie.
Import List.ListNotations.

Module PosSet := TrieSetCode PosKeyCode.
Definition left_set := fold_right PosSet.add PosSet.empty [1; 2; 1]%positive.
Definition right_set := fold_right PosSet.add PosSet.empty [2; 3]%positive.

Example set_members : PosSet.elements left_set = [2; 1]%positive.
Proof. vm_compute. reflexivity. Qed.

Example set_intersection : PosSet.elements (PosSet.inter left_set right_set) = [2]%positive.
Proof. vm_compute. reflexivity. Qed.

Example set_difference : PosSet.elements (PosSet.diff left_set right_set) = [1]%positive.
Proof. vm_compute. reflexivity. Qed.

Example set_nonmember : PosSet.mem 3%positive left_set = false.
Proof. vm_compute. reflexivity. Qed.

Example set_empty : PosSet.equal PosSet.empty PosSet.empty = true.
Proof. vm_compute. reflexivity. Qed.

Definition malformed_storage : PosSet.t := PTrieCode.set 1%positive 2%positive PTrieCode.empty.
Module CollisionKey.
  Definition t := positive.
  Definition encode (_ : t) := 1%positive.
  Definition eqb (_ _ : t) := true.
End CollisionKey.
Module CollisionSet := TrieSetCode CollisionKey.

Example malformed_set_update_client :
  PosSet.mem 1%positive (PosSet.add 3%positive malformed_storage) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example colliding_membership_client :
  CollisionSet.mem 1%positive (CollisionSet.add 2%positive CollisionSet.empty) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(* BaseSetTest.set_ticks retires with Cost.ticks. raw_add_client and
   malformed_set_control are symbolic law clients. colliding_membership_client
   uses a constant encoder through the operations layer, which needs no laws. *)

Module UnitSet := TrieSetCode UnitKeyCode.
Definition raw_unit_set : UnitSet.t := PTrieCode.set 2%positive tt PTrieCode.empty.
Example set_raw_code :
  (UnitSet.mem tt raw_unit_set, UnitSet.has 2%positive raw_unit_set,
   UnitSet.subset raw_unit_set UnitSet.empty) = (false, true, false).
Proof. vm_compute. reflexivity. Qed.

(** Union keeps both one-sided branches and their shared member. *)
Example set_union_shared_branches :
  List.map (fun k => PosSet.mem k (PosSet.union left_set right_set))
    [1; 2; 3; 4]%positive = [true; true; true; false].
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty union side leaves the other trie unchanged in either order. *)
Example set_union_empty_sharing :
  (PosSet.union PosSet.empty left_set, PosSet.union left_set PosSet.empty) =
    (left_set, left_set).
Proof.
  vm_compute. reflexivity.
Qed.

(** Intersection drops each one-sided branch. *)
Example set_intersection_shared_branches :
  List.map (fun k => PosSet.mem k (PosSet.inter left_set right_set))
    [1; 2; 3]%positive = [false; true; false].
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty intersection side drops the other trie in either order. *)
Example set_intersection_empty :
  (PosSet.inter PosSet.empty right_set, PosSet.inter right_set PosSet.empty) =
    (PosSet.empty, PosSet.empty).
Proof.
  vm_compute. reflexivity.
Qed.

(** Difference keeps only the left-only branch. *)
Example set_difference_shared_branches :
  List.map (fun k => PosSet.mem k (PosSet.diff left_set right_set))
    [1; 2; 3]%positive = [true; false; false].
Proof.
  vm_compute. reflexivity.
Qed.

(** Difference shares its left input or drops its right input at the empty boundary. *)
Example set_difference_empty :
  (PosSet.diff left_set PosSet.empty, PosSet.diff PosSet.empty right_set) =
    (left_set, PosSet.empty).
Proof.
  vm_compute. reflexivity.
Qed.

(** Equality checks shared members and rejects a member on either side only. *)
Example set_equality_shared_and_one_sided :
  (PosSet.equal left_set (fold_right PosSet.add PosSet.empty [1; 2]%positive),
   PosSet.equal left_set right_set, PosSet.equal right_set left_set,
   PosSet.equal left_set PosSet.empty, PosSet.equal PosSet.empty left_set) =
    (true, false, false, false, false).
Proof.
  vm_compute. reflexivity.
Qed.
