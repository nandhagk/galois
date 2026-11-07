(** * Canonical trie boundary tests

    These examples check deep paths, absent keys and canonical collapse.
    For example, removing the only binding returns the empty constructor.
    Builds on: BaseTrie. *)

From Stdlib Require Import NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseTrie.

Definition full : Trie.t nat :=
  Trie.set 13 130 (Trie.set 1 10 (Trie.set 2 20 Trie.empty)).

Example root_lookup : Trie.get 1 full = Some 10.
Proof.
  vm_compute. reflexivity.
Qed.

Example deep_lookup : Trie.get 13 full = Some 130.
Proof.
  vm_compute. reflexivity.
Qed.

Example absent_lookup : Trie.get 12 full = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_lookup : Trie.get 13 (Trie.empty : Trie.t nat) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example overwrite : Trie.get 13 (Trie.set 13 131 full) = Some 131.
Proof.
  vm_compute. reflexivity.
Qed.

Example collapse : Trie.remove 13 (Trie.set 13 130 Trie.empty) = Trie.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example remove_absent : Trie.remove 12 full = full.
Proof.
  vm_compute. reflexivity.
Qed.

Example update_present :
  Trie.get 13 (Trie.update 13 (fun _ => Some 131) full) = Some 131.
Proof.
  vm_compute. reflexivity.
Qed.

Example update_absent :
  Trie.get 12 (Trie.update 12 (fun _ => Some 120) full) = Some 120.
Proof.
  vm_compute. reflexivity.
Qed.

Example update_remove : Trie.update 1 (fun _ => None) full = Trie.remove 1 full.
Proof.
  vm_compute. reflexivity.
Qed.

Example exact_bits :
  (Cost.ticks (Trie.get_c 13 full), Cost.ticks (Trie.set_c 13 131 full),
    Cost.ticks (Trie.remove_c 13 full)) = (4%N, 4%N, 4%N).
Proof.
  vm_compute. reflexivity.
Qed.
