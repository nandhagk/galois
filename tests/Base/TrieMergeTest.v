(** * Trie merge tests

    These examples cover shared and disjoint bindings.
    For example, a callback combines values at a shared key.
    Builds on: Trie.

    Groups:
    - [MergeTests] The bindings that a merge keeps, adds or drops.
    - [ForallTests] Pointwise comparison of two tries.
    - [ComparisonTests] Equality of tries and their binding counts. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Trie.
Import List.ListNotations.

(** * Fixtures *)

(** A trie with bindings 1 to 10 and 2 to 20. *)
Definition left_map : PTrieCode.t nat :=
  PTrieCode.set 1 10 (PTrieCode.set 2 20 PTrieCode.empty).

(** A trie with bindings 1 to 100 and 3 to 300. *)
Definition right_map : PTrieCode.t nat :=
  PTrieCode.set 1 100 (PTrieCode.set 3 300 PTrieCode.empty).

(** Adds two values present on both sides, and drops a key present on one side. *)
Definition inter_add a b :=
  match a, b with Some x, Some y => Some (x + y) | _, _ => None end.

(** Keeps the left value unless the right side has a value at the same key. *)
Definition difference {A B} (a : option A) (b : option B) :=
  match b with Some _ => None | None => a end.

(** Adds values present on both sides and keeps values present on one side. *)
Definition union_add a b :=
  match a, b with
  | Some x, Some y => Some (x + y)
  | Some x, None => Some x
  | None, Some y => Some y
  | None, None => None
  end.

(** * Merge *)

Module MergeTests.

  (** The intersection adds the values of the keys that both sides hold. *)
  Example intersection_adds_shared_keys :
    PTrieCode.elements (PTrieCode.merge inter_add left_map right_map) = [(1%positive, 110)].
  Proof. vm_compute. reflexivity. Qed.

  (** The difference keeps only the keys that the left side alone holds. *)
  Example difference_keeps_left_only_keys :
    PTrieCode.elements (PTrieCode.merge difference left_map right_map) = [(2%positive, 20)].
  Proof. vm_compute. reflexivity. Qed.

  (** The union lists its keys in trie order. *)
  Example union_lists_keys_in_trie_order :
    PTrieCode.elements (PTrieCode.merge union_add left_map right_map) =
      [(2%positive, 20); (1%positive, 110); (3%positive, 300)].
  Proof. vm_compute. reflexivity. Qed.

  (** A callback that maps values changes only the bindings from one side. *)
  Example single_side_values_are_mapped :
    PTrieCode.elements (PTrieCode.merge
      (fun a (_ : option bool) => option_map S a) left_map PTrieCode.empty) =
      [(2%positive, 21); (1%positive, 11)].
  Proof. vm_compute. reflexivity. Qed.

  (** Merging with the empty trie under union leaves the trie unchanged. *)
  Example union_with_empty_is_identity :
    PTrieCode.merge union_add left_map PTrieCode.empty = left_map.
  Proof. vm_compute. reflexivity. Qed.

  (** Merging with the empty trie under intersection gives the empty trie. *)
  Example intersection_with_empty_is_empty :
    PTrieCode.merge inter_add left_map PTrieCode.empty = PTrieCode.empty.
  Proof. vm_compute. reflexivity. Qed.

  (** Subtracting the empty trie leaves the trie unchanged. *)
  Example difference_with_empty_is_identity :
    PTrieCode.merge difference left_map (PTrieCode.empty : PTrieCode.t bool) = left_map.
  Proof. vm_compute. reflexivity. Qed.

  (** The intersection of tries with disjoint keys is empty. *)
  Example intersection_of_disjoint_is_empty :
    PTrieCode.merge inter_add (PTrieCode.set 2 20 PTrieCode.empty)
      (PTrieCode.set 3 30 PTrieCode.empty) = PTrieCode.empty.
  Proof. vm_compute. reflexivity. Qed.

  (** The difference of a trie with itself is empty. *)
  Example difference_of_equal_is_empty :
    PTrieCode.merge difference left_map left_map = PTrieCode.empty.
  Proof. vm_compute. reflexivity. Qed.

  (** The intersection of a trie with itself is the trie. *)
  Example intersection_of_equal_is_identity :
    PTrieCode.merge (fun a b => match a, b with Some x, Some _ => Some x | _, _ => None end)
      left_map left_map = left_map.
  Proof. vm_compute. reflexivity. Qed.

  (** The union of a trie with itself is the trie. *)
  Example union_of_equal_is_identity :
    PTrieCode.merge (fun a b => match a with Some _ => a | None => b end)
      left_map left_map = left_map.
  Proof. vm_compute. reflexivity. Qed.

  (** An empty left side makes the intersection empty. *)
  Example empty_left_intersection_is_empty :
    PTrieCode.elements (PTrieCode.merge inter_add PTrieCode.empty right_map) = [].
  Proof. vm_compute. reflexivity. Qed.

  (** An empty left side makes the difference empty. *)
  Example empty_left_difference_is_empty :
    PTrieCode.elements
      (PTrieCode.merge difference (PTrieCode.empty : PTrieCode.t nat) right_map) = [].
  Proof. vm_compute. reflexivity. Qed.

End MergeTests.

(** * Pairwise comparison *)

Module ForallTests.

  (** A key that only the left side holds makes the comparison fail. *)
  Example left_only_key_fails_forall :
    PTrieCode.forall2 (fun _ b => match b with Some _ => true | None => false end)
      left_map right_map = false.
  Proof. vm_compute. reflexivity. Qed.

  (** An empty left side makes the comparison succeed for any right side. *)
  Example empty_left_forall_is_true :
    PTrieCode.forall2 (fun (_ : nat) (_ : option nat) => false) PTrieCode.empty right_map = true.
  Proof. vm_compute. reflexivity. Qed.

End ForallTests.

(** * Comparison *)

Module ComparisonTests.

  (** A trie compares equal to itself at every key. *)
  Example trie_equals_itself :
    PTrieCode.forall2 (fun x y => match y with Some y => Nat.eqb x y | None => false end)
      left_map left_map = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two different tries do not compare equal in both directions. *)
  Example left_against_right_fails :
    PTrieCode.forall2 (fun x y => match y with Some y => Nat.eqb x y | None => false end)
      left_map right_map = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The comparison of right against left also fails. *)
  Example right_against_left_fails :
    PTrieCode.forall2 (fun x y => match y with Some y => Nat.eqb x y | None => false end)
      right_map left_map = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The left trie has two bindings. *)
  Example left_map_has_two_bindings : length (PTrieCode.elements left_map) = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ComparisonTests.
