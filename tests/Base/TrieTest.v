(** * Canonical trie boundary tests

    These examples check deep paths, absent keys and canonical collapse.
    For example, removing the only binding returns the empty constructor.
    Builds on: PTrieCode.

    Groups:
    - [LookupTests] Reading keys from a trie, present or absent.
    - [UpdateTests] Setting a key, present or absent, and removing one.
    - [ForallTests] Pairwise comparison of two tries. *)

From Stdlib Require Import NArith.
From Galois.Base Require Import Trie.

(** * Fixtures *)

(** A trie with three bindings, one of them at the deep key 13. *)
Definition full : PTrieCode.t nat :=
  PTrieCode.set 13 130 (PTrieCode.set 1 10 (PTrieCode.set 2 20 PTrieCode.empty)).

(** Two boolean bindings used to compare tries pointwise. *)
Definition paired_trie : PTrieCode.t bool :=
  PTrieCode.set 2 true (PTrieCode.set 3 false PTrieCode.empty).

(** Two optional booleans are equal when both are absent or both carry the same value. *)
Definition paired_eq (a b : option bool) : bool :=
  match a, b with
  | None, None | Some true, Some true | Some false, Some false => true
  | _, _ => false
  end.

(** * Lookup *)

Module LookupTests.

  (** A key at the root of the trie reads its stored value. *)
  Example root_key_reads_value : PTrieCode.get 1 full = Some 10.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A deep key reads its stored value. *)
  Example deep_key_reads_value : PTrieCode.get 13 full = Some 130.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A key that was never stored reads as absent. *)
  Example absent_key_reads_none : PTrieCode.get 12 full = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Any key reads as absent in the empty trie. *)
  Example empty_trie_reads_none :
    PTrieCode.get 13 (PTrieCode.empty : PTrieCode.t nat) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LookupTests.

(** * Update *)

Module UpdateTests.

  (** Setting a present key replaces its value. *)
  Example set_replaces_present_value :
    PTrieCode.get 13 (PTrieCode.set 13 131 full) = Some 131.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Setting an absent key adds it. *)
  Example set_adds_absent_key :
    PTrieCode.get 12 (PTrieCode.set 12 120 full) = Some 120.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A removed key reads as absent. *)
  Example removed_key_reads_none :
    PTrieCode.get 1 (PTrieCode.remove 1 full) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Removing the only binding leaves the empty trie. *)
  Example removing_only_binding_gives_empty :
    PTrieCode.remove 13 (PTrieCode.set 13 130 PTrieCode.empty) = PTrieCode.empty.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Removing an absent key leaves the trie unchanged. *)
  Example removing_absent_key_keeps_trie : PTrieCode.remove 12 full = full.
  Proof.
    vm_compute. reflexivity.
  Qed.

End UpdateTests.

(** * Pairwise comparison *)

Module ForallTests.

  (** A trie compared with itself agrees at every key. *)
  Example equal_tries_agree_everywhere :
    PTrieCode.forall2b paired_eq paired_trie paired_trie = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A changed value at a shared key is detected. *)
  Example changed_value_is_detected :
    PTrieCode.forall2b paired_eq paired_trie (PTrieCode.set 3 true paired_trie) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A key present on only one side is detected. *)
  Example extra_right_key_is_detected :
    PTrieCode.forall2b paired_eq paired_trie (PTrieCode.set 8 false paired_trie) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** When both sides hold a key, the comparison looks at its values. *)
  Example shared_keys_both_present :
    PTrieCode.forall2b
      (fun a b => match a, b with Some _, Some _ => true | _, _ => false end)
      paired_trie paired_trie = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ForallTests.
