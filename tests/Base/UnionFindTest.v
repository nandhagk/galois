(** * Union-find reference fixtures

    These fixtures observe representatives and path compression.
    For example, a lookup of an unknown key returns that key.
    Builds on: UnionFind and Trie. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Trie UnionFind.
Import List.ListNotations.

Definition uf_pairs : list (positive * positive) := [(1, 2); (3, 4); (1, 3)]%positive.
Definition uf_sample := fold_left
  (fun u xy => snd (UnionFindCode.union (fst xy) (snd xy) u)) uf_pairs UnionFindCode.empty.
Definition uf_pair := snd (UnionFindCode.union 1%positive 2%positive UnionFindCode.empty).

Example uf_successful_find : fst (UnionFindCode.find 4%positive uf_sample) = 1%positive.
Proof. vm_compute. reflexivity. Qed.
Example uf_unknown_find :
  UnionFindCode.find 5%positive uf_sample = (5%positive, uf_sample).
Proof. vm_compute. reflexivity. Qed.
Example uf_empty_find :
  UnionFindCode.find 1%positive UnionFindCode.empty = (1%positive, UnionFindCode.empty).
Proof. vm_compute. reflexivity. Qed.
Example uf_left_lower_rank :
  fst (UnionFindCode.find 3%positive (snd (UnionFindCode.union 3%positive 1%positive uf_pair))) =
    1%positive.
Proof. vm_compute. reflexivity. Qed.
Example uf_right_lower_rank :
  fst (UnionFindCode.find 3%positive (snd (UnionFindCode.union 1%positive 3%positive uf_pair))) =
    1%positive.
Proof. vm_compute. reflexivity. Qed.

(* Other operations, representation and cost examples are in BaseUnionFindTest.v at 87192fe. *)
