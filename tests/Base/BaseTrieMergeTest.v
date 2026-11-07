(** * Sharing trie merge tests

    These examples distinguish general combination from specialized skipping.
    For example, a one-sided callback can change a general combination's binding.
    Builds on: BaseTrie and BaseTrieMerge. *)

From Stdlib Require Import NArith List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseTrie BaseTrieMerge.
Import List.ListNotations.

Definition left_map : Trie.t nat := Trie.set 1 10 (Trie.set 2 20 Trie.empty).
Definition right_map : Trie.t nat := Trie.set 1 100 (Trie.set 3 300 Trie.empty).

Example inter_shared :
  TrieMerge.elements (TrieMerge.inter_with Nat.add left_map right_map) = [(1%positive, 110)].
Proof.
  vm_compute. reflexivity.
Qed.

Example diff_shared :
  TrieMerge.elements (TrieMerge.diff left_map right_map) = [(2%positive, 20)].
Proof.
  vm_compute. reflexivity.
Qed.

Example union_order :
  TrieMerge.elements (TrieMerge.union_with Nat.add left_map right_map) =
    [(2%positive, 20); (1%positive, 110); (3%positive, 300)].
Proof.
  vm_compute. reflexivity.
Qed.

Example union_empty : TrieMerge.union_with Nat.add left_map Trie.empty = left_map.
Proof.
  vm_compute. reflexivity.
Qed.

Example inter_empty :
  TrieMerge.inter_with Nat.add left_map Trie.empty = Trie.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example diff_empty : TrieMerge.diff left_map (Trie.empty : Trie.t bool) = left_map.
Proof.
  vm_compute. reflexivity.
Qed.

Example inter_disjoint :
  TrieMerge.inter_with Nat.add (Trie.set 2 20 Trie.empty) (Trie.set 3 30 Trie.empty) =
    Trie.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example diff_equal : TrieMerge.diff left_map left_map = Trie.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example combine_changes_one_side :
  TrieMerge.elements (TrieMerge.combine
    (fun a (_ : option bool) => option_map S a) left_map Trie.empty) =
    [(2%positive, 21); (1%positive, 11)].
Proof.
  vm_compute. reflexivity.
Qed.

Example subset_reject :
  TrieMerge.forall2 (fun _ b => match b with Some _ => true | None => false end)
    left_map right_map = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_accept : TrieMerge.beq Nat.eqb left_map left_map = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example count_bindings : TrieMerge.size left_map = 2%nat.
Proof.
  vm_compute. reflexivity.
Qed.
