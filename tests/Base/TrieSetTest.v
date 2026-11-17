(** * Finite-set fixtures

    These fixtures cover duplicate keys, set operations and empty input.
    For example, removing a singleton's member empties it.
    Builds on: TrieSet and Key.

    Groups:
    - MembershipTests: members, non-members and the listing of a set.
    - OperationTests: union, intersection and difference, including the empty sets.
    - EqualityTests: equality of sets with shared and one-sided members.
    - CollisionTests: sets whose keys share one encoded code, or whose storage is malformed.
    - RawTests: a set over a unit key, read back through its raw code. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key TrieSet Trie.
Import List.ListNotations.

(** * Fixtures *)

(** Positive-keyed sets built by the trie set functor. *)
Module PosSet := TrieSetCode PosKeyCode.

(** The set with members 1 and 2, where the duplicate 1 is added once. *)
Definition left_set := fold_right PosSet.add PosSet.empty [1; 2; 1]%positive.

(** The set with members 2 and 3. *)
Definition right_set := fold_right PosSet.add PosSet.empty [2; 3]%positive.

(** A key type whose every key encodes to the same code. *)
Module CollisionKey.
  Definition t := positive.
  Definition encode (_ : t) := 1%positive.
  Definition eqb (_ _ : t) := true.
End CollisionKey.

(** Sets over the colliding key type. *)
Module CollisionSet := TrieSetCode CollisionKey.

(** A trie whose member is stored under a key that does not match its path. *)
Definition malformed_storage : PosSet.t :=
  PTrieCode.set 1%positive 2%positive PTrieCode.empty.

(** Sets over unit keys. *)
Module UnitSet := TrieSetCode UnitKeyCode.

(** A raw trie with one member, stored at key 2. *)
Definition raw_unit_set : UnitSet.t := PTrieCode.set 2%positive tt PTrieCode.empty.

(** * Membership *)

Module MembershipTests.

  (** The elements of a set are listed in trie order, each member once. *)
  Example elements_list_members_in_trie_order :
    PosSet.elements left_set = [2; 1]%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** A key that is not a member is reported as absent. *)
  Example absent_member_is_false : PosSet.mem 3%positive left_set = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Adding a member to a malformed set keeps the stored member readable. *)
  Example add_keeps_malformed_member :
    PosSet.mem 1%positive (PosSet.add 3%positive malformed_storage) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Keys that encode to one code share their membership. *)
  Example colliding_keys_share_membership :
    CollisionSet.mem 1%positive (CollisionSet.add 2%positive CollisionSet.empty) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A unit set misses a key that was never added. *)
  Example unit_set_misses_absent_member : UnitSet.mem tt raw_unit_set = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A raw unit set has its stored key. *)
  Example unit_set_has_stored_key : UnitSet.has 2%positive raw_unit_set = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A non-empty raw set is not a subset of the empty set. *)
  Example nonempty_set_not_subset_of_empty :
    UnitSet.subset raw_unit_set UnitSet.empty = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The empty set equals itself. *)
  Example empty_sets_are_equal : PosSet.equal PosSet.empty PosSet.empty = true.
  Proof. vm_compute. reflexivity. Qed.

End MembershipTests.

(** * Operations *)

Module OperationTests.

  (** The intersection keeps the member that both sets share. *)
  Example intersection_keeps_shared_member :
    PosSet.elements (PosSet.inter left_set right_set) = [2]%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** The difference keeps the member that only the left set has. *)
  Example difference_keeps_left_only_member :
    PosSet.elements (PosSet.diff left_set right_set) = [1]%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** The union contains the member of the left set. *)
  Example union_contains_left_member :
    PosSet.mem 1%positive (PosSet.union left_set right_set) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The union contains the member that both sets share. *)
  Example union_contains_shared_member :
    PosSet.mem 2%positive (PosSet.union left_set right_set) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The union contains the member of the right set. *)
  Example union_contains_right_member :
    PosSet.mem 3%positive (PosSet.union left_set right_set) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The union contains no member that neither set has. *)
  Example union_omits_unknown_member :
    PosSet.mem 4%positive (PosSet.union left_set right_set) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The union with an empty left set is the right set. *)
  Example union_with_empty_left_is_identity :
    PosSet.union PosSet.empty left_set = left_set.
  Proof. vm_compute. reflexivity. Qed.

  (** The union with an empty right set is the left set. *)
  Example union_with_empty_right_is_identity :
    PosSet.union left_set PosSet.empty = left_set.
  Proof. vm_compute. reflexivity. Qed.

  (** The intersection drops the member that only the left set has. *)
  Example intersection_drops_left_only_member :
    PosSet.mem 1%positive (PosSet.inter left_set right_set) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The intersection keeps the member that both sets share. *)
  Example intersection_keeps_shared_member_checked :
    PosSet.mem 2%positive (PosSet.inter left_set right_set) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The intersection drops the member that only the right set has. *)
  Example intersection_drops_right_only_member :
    PosSet.mem 3%positive (PosSet.inter left_set right_set) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The intersection with an empty left set is empty. *)
  Example intersection_with_empty_left_is_empty :
    PosSet.inter PosSet.empty right_set = PosSet.empty.
  Proof. vm_compute. reflexivity. Qed.

  (** The intersection with an empty right set is empty. *)
  Example intersection_with_empty_right_is_empty :
    PosSet.inter right_set PosSet.empty = PosSet.empty.
  Proof. vm_compute. reflexivity. Qed.

  (** The difference drops the member that only the right set has, keeping the left member. *)
  Example difference_keeps_left_member :
    PosSet.mem 1%positive (PosSet.diff left_set right_set) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The difference drops the member that both sets share. *)
  Example difference_drops_shared_member :
    PosSet.mem 2%positive (PosSet.diff left_set right_set) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The difference drops the member that only the right set has. *)
  Example difference_drops_right_only_member :
    PosSet.mem 3%positive (PosSet.diff left_set right_set) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The difference with an empty right set is the left set. *)
  Example difference_with_empty_right_is_identity :
    PosSet.diff left_set PosSet.empty = left_set.
  Proof. vm_compute. reflexivity. Qed.

  (** The difference of an empty left set is empty. *)
  Example difference_of_empty_left_is_empty :
    PosSet.diff PosSet.empty right_set = PosSet.empty.
  Proof. vm_compute. reflexivity. Qed.

End OperationTests.

(** * Equality *)

Module EqualityTests.

  (** A set equals another set with the same members. *)
  Example equal_sets_with_same_members :
    PosSet.equal left_set (fold_right PosSet.add PosSet.empty [1; 2]%positive) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Two sets with different members are not equal. *)
  Example different_sets_are_unequal : PosSet.equal left_set right_set = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The right set is not equal to the left set. *)
  Example right_set_unequal_to_left : PosSet.equal right_set left_set = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A non-empty set is not equal to the empty set. *)
  Example set_unequal_to_empty : PosSet.equal left_set PosSet.empty = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The empty set is not equal to a non-empty set. *)
  Example empty_unequal_to_set : PosSet.equal PosSet.empty left_set = false.
  Proof. vm_compute. reflexivity. Qed.

End EqualityTests.

(* BaseSetTest.set_ticks retires with Cost.ticks. raw_add_client and
   malformed_set_control are symbolic law clients. colliding_membership_client
   uses a constant encoder through the operations layer, which needs no laws. *)
