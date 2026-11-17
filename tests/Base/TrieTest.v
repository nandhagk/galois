(** * Canonical trie boundary tests

    These examples check deep paths, absent keys and canonical collapse.
    For example, removing the only binding returns the empty constructor.
    Builds on: PTrieCode. *)

From Stdlib Require Import NArith.
From Galois.Base Require Import Trie.

Definition full : PTrieCode.t nat :=
  PTrieCode.set 13 130 (PTrieCode.set 1 10 (PTrieCode.set 2 20 PTrieCode.empty)).

Example root_lookup : PTrieCode.get 1 full = Some 10.
Proof.
  vm_compute. reflexivity.
Qed.

Example deep_lookup : PTrieCode.get 13 full = Some 130.
Proof.
  vm_compute. reflexivity.
Qed.

Example absent_lookup : PTrieCode.get 12 full = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_lookup : PTrieCode.get 13 (PTrieCode.empty : PTrieCode.t nat) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example overwrite : PTrieCode.get 13 (PTrieCode.set 13 131 full) = Some 131.
Proof.
  vm_compute. reflexivity.
Qed.

Example collapse : PTrieCode.remove 13 (PTrieCode.set 13 130 PTrieCode.empty) = PTrieCode.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example remove_absent : PTrieCode.remove 12 full = full.
Proof.
  vm_compute. reflexivity.
Qed.

Example update_present :
  PTrieCode.get 13 (PTrieCode.set 13 131 full) = Some 131.
Proof.
  vm_compute. reflexivity.
Qed.

Example update_absent : PTrieCode.get 12 (PTrieCode.set 12 120 full) = Some 120.
Proof.
  vm_compute. reflexivity.
Qed.

Example update_remove :
  PTrieCode.get 1 (PTrieCode.remove 1 full) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition paired_trie : PTrieCode.t bool :=
  PTrieCode.set 2 true (PTrieCode.set 3 false PTrieCode.empty).

Definition paired_eq (a b : option bool) : bool :=
  match a, b with
  | None, None | Some true, Some true | Some false, Some false => true
  | _, _ => false
  end.

Example paired_shared_equal : PTrieCode.forall2b paired_eq paired_trie paired_trie = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example paired_shared_different :
  PTrieCode.forall2b paired_eq paired_trie (PTrieCode.set 3 true paired_trie) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example paired_right_only :
  PTrieCode.forall2b paired_eq paired_trie (PTrieCode.set 8 false paired_trie) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example paired_skips_absent_root :
  PTrieCode.forall2b
    (fun a b => match a, b with Some _, Some _ => true | _, _ => false end)
    paired_trie paired_trie = true.
Proof.
  vm_compute. reflexivity.
Qed.

(* BaseTrieTest.update_present and update_absent use constant Some callbacks.
   Their public composition is set. update_remove uses a constant None callback,
   whose public composition is remove. The old equality to remove is definitional
   after this substitution. The get observation also checks that the key is absent. *)

(* BaseTrieTest.exact_bits expects (4%N, 4%N, 4%N) from Cost.ticks.
   It retires with Cost. *)
