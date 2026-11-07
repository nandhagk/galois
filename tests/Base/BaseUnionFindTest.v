(** * Union-find reference fixtures

    These fixtures observe representative choice, domain order and path compression.
    For example, balanced pair unions create a two-link path that find shortens.
    Builds on: BaseUnionFind, BaseMap, BaseEncoding and CostMonad. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
Import List.ListNotations.

Definition uf_pairs : list (positive * positive) := [(1, 2); (3, 4); (1, 3)]%positive.
Definition uf_sample := UnionFind.of_unions positive_encoding uf_pairs.
Definition uf_compressed := snd (UnionFind.find positive_encoding 4%positive uf_sample).
Definition uf_pair := UnionFind.union positive_encoding 1%positive 2%positive UnionFind.make.

Example uf_successful_find :
  fst (UnionFind.find positive_encoding 4%positive uf_sample) = 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_successful_union :
  fst (UnionFind.equivb positive_encoding 2%positive 4%positive uf_sample) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_unrelated :
  fst (UnionFind.equivb positive_encoding 1%positive 3%positive
    (UnionFind.union positive_encoding 1%positive 2%positive UnionFind.make)) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_unknown :
  fst (UnionFind.equivb positive_encoding 4%positive 5%positive uf_sample) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_unknown_find :
  UnionFind.find positive_encoding 5%positive uf_sample = (5%positive, uf_sample).
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_empty : UnionFind.keys positive_encoding (@UnionFind.make positive) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_empty_find :
  UnionFind.find positive_encoding 1%positive UnionFind.make = (1%positive, UnionFind.make).
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_singleton :
  UnionFind.keys positive_encoding
    (UnionFind.union positive_encoding 1%positive 1%positive UnionFind.make) = [1%positive].
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_unknown_reflexive :
  fst (UnionFind.equivb positive_encoding 5%positive 5%positive uf_sample) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_same_class :
  UnionFind.union positive_encoding 1%positive 2%positive
    (UnionFind.union positive_encoding 1%positive 2%positive UnionFind.make) =
  UnionFind.union positive_encoding 1%positive 2%positive UnionFind.make.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_left_lower_rank :
  fst (UnionFind.find positive_encoding 3%positive
    (UnionFind.union positive_encoding 3%positive 1%positive uf_pair)) = 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_right_lower_rank :
  fst (UnionFind.find positive_encoding 3%positive
    (UnionFind.union positive_encoding 1%positive 3%positive uf_pair)) = 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_key_order : UnionFind.keys positive_encoding uf_sample = [4; 2; 1; 3]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_before_compression :
  Map.get positive_encoding 4%positive (UnionFind.parents uf_sample) = Some 3%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_after_compression :
  Map.get positive_encoding 4%positive (UnionFind.parents uf_compressed) = Some 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_compression_classes :
  fst (UnionFind.equivb positive_encoding 2%positive 4%positive uf_compressed) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_compression_ranks :
  (UnionFind.ranks uf_compressed, UnionFind.max_rank uf_compressed) =
  (UnionFind.ranks uf_sample, UnionFind.max_rank uf_sample).
Proof.
  vm_compute. reflexivity.
Qed.

(** A zero budget returns the current key without inspecting its parent. *)
Example uf_exhausted :
  UnionFind.find_fuel positive_encoding 0 4%positive uf_sample = (4%positive, uf_sample).
Proof.
  vm_compute. reflexivity.
Qed.

(** A one-link budget compresses to the intermediate key even when that key has a parent. *)
Example uf_exhausted_prefix :
  fst (UnionFind.find_fuel positive_encoding 1 4%positive uf_sample) = 3%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** Exact reference-backend counts may change with a backend's proved replacement bounds. *)
Example uf_empty_find_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 1%positive UnionFind.make) = 4%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_exhausted_ticks :
  Cost.ticks (UnionFind.find_fuel_c positive_encoding 0 4%positive uf_sample) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_singleton_union_ticks :
  Cost.ticks (UnionFind.union_c positive_encoding 1%positive 1%positive UnionFind.make) = 19%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_distinct_union_ticks :
  Cost.ticks (UnionFind.union_c positive_encoding 1%positive 2%positive UnionFind.make) = 31%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_pair_find_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 2%positive uf_pair) = 13%N.
Proof.
  vm_compute. reflexivity.
Qed.
