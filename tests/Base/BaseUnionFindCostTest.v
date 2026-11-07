(** * Balanced rank and compression accounting fixtures

    Equal-rank unions reach logarithmic rank and path compression reduces subsequent find work.
    For example, eight known keys reach rank three and a three-link path compresses to one link.
    Builds on: BaseUnionFindRank and the public Map observations. *)

From Stdlib Require Import List NArith PeanoNat.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind BaseUnionFindRank
  BaseUnionFindCost.
Import List.ListNotations.

Definition balanced_pairs : list (positive * positive) :=
  [(1, 2); (3, 4); (5, 6); (7, 8); (1, 3); (5, 7); (1, 5)]%positive.
Definition balanced_forest := UnionFind.of_unions positive_encoding balanced_pairs.
Definition balanced_compressed :=
  snd (UnionFind.find positive_encoding 8%positive balanced_forest).

Example union_find_balanced_rank :
  (UnionFind.max_rank balanced_forest,
    Nat.log2 (length (UnionFind.keys positive_encoding balanced_forest))) = (3, 3).
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_before_compression :
  Map.get positive_encoding 8%positive (UnionFind.parents balanced_forest) = Some 7%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_after_compression :
  Map.get positive_encoding 8%positive (UnionFind.parents balanced_compressed) = Some 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_long_path_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 8%positive balanced_forest) = 45%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_shortened_path_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 8%positive balanced_compressed) = 20%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_unknown_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 16%positive balanced_forest) = 9%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_known_key_budget :
  forallb (fun k =>
    N.leb (Cost.ticks (encode_c positive_encoding k) +
      N.pos (Pos.size (encode positive_encoding k))) 5)
    (UnionFind.keys positive_encoding balanced_forest) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_unknown_query_budget :
  (Cost.ticks (encode_c positive_encoding 16%positive) +
    N.pos (Pos.size (encode positive_encoding 16%positive)))%N = 6%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_compression_cost_bound :
  N.leb (Cost.ticks (UnionFind.find_c positive_encoding 8%positive balanced_forest))
    (UnionFindCost.uf_k * (1 + N.log2 8) * (1 + 5)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition cyclic_forest :=
  UnionFind.Forest
    (Map.set positive_encoding 1%positive 2%positive
      (Map.set positive_encoding 2%positive 1%positive Map.empty))
    Map.empty 0.

Example union_find_raw_cycle_prefix :
  fst (UnionFind.find_fuel positive_encoding 1 1%positive cyclic_forest) = 2%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example union_find_raw_cycle_compression :
  let compressed := snd (UnionFind.find_fuel positive_encoding 2 1%positive cyclic_forest) in
  (Map.get positive_encoding 1%positive (UnionFind.parents compressed),
    Map.get positive_encoding 2%positive (UnionFind.parents compressed)) =
    (Some 1%positive, Some 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.
