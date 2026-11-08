(** * Union-find reference fixtures

    These fixtures observe representative choice, domain order and path compression.
    For example, balanced pair unions create a two-link path that find shortens.
    Builds on: BaseUnionFind, BaseMap, BaseEncoding and CostMonad. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseUnionFind.
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
  Cost.ticks (UnionFind.find_c positive_encoding 1%positive UnionFind.make) = 6%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_exhausted_ticks :
  Cost.ticks (UnionFind.find_fuel_c positive_encoding 0 4%positive uf_sample) = 1%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_singleton_union_ticks :
  Cost.ticks (UnionFind.union_c positive_encoding 1%positive 1%positive UnionFind.make) = 23%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_distinct_union_ticks :
  Cost.ticks (UnionFind.union_c positive_encoding 1%positive 2%positive UnionFind.make) = 35%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_pair_find_ticks :
  Cost.ticks (UnionFind.find_c positive_encoding 2%positive uf_pair) = 18%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** * Symbolic clients for representative transport *)

(** The root-link client passes every invariant and old-root duty to the public equation. *)
Theorem uf_link_rep_equation_client {K} (E : encoding K) (HE : encoding_laws E)
    child root raise uf a :
  UnionFind.wf E uf -> UnionFind.wf E (UnionFind.link E child root raise uf) ->
  child <> root ->
  Map.get E child (UnionFind.parents uf) = None ->
  Map.get E root (UnionFind.parents uf) = None ->
  fst (UnionFind.find E a (UnionFind.link E child root raise uf)) =
    if eqb E (fst (UnionFind.find E a uf)) child then root
    else fst (UnionFind.find E a uf).
Proof.
  exact (UnionFind.link_rep_equation E HE child root raise uf a).
Qed.

(** A member of the old losing class obtains the selected root as its actual new representative. *)
Theorem uf_link_losing_class_client {K} (E : encoding K) (HE : encoding_laws E)
    child root raise uf a :
  UnionFind.wf E uf -> UnionFind.wf E (UnionFind.link E child root raise uf) ->
  child <> root ->
  Map.get E child (UnionFind.parents uf) = None ->
  Map.get E root (UnionFind.parents uf) = None ->
  fst (UnionFind.find E a uf) = child ->
  fst (UnionFind.find E a (UnionFind.link E child root raise uf)) = root.
Proof.
  intros Hwf Hlinked Hne Hchild Hroot Hrep.
  rewrite (UnionFind.link_rep_equation E HE child root raise uf a
    Hwf Hlinked Hne Hchild Hroot), Hrep, eqb_refl. reflexivity.
Qed.

(** Every query outside the losing class retains its old representative after linking roots. *)
Theorem uf_link_unchanged_class_client {K} (E : encoding K) (HE : encoding_laws E)
    child root raise uf a :
  UnionFind.wf E uf -> UnionFind.wf E (UnionFind.link E child root raise uf) ->
  child <> root ->
  Map.get E child (UnionFind.parents uf) = None ->
  Map.get E root (UnionFind.parents uf) = None ->
  fst (UnionFind.find E a uf) <> child ->
  fst (UnionFind.find E a (UnionFind.link E child root raise uf)) =
    fst (UnionFind.find E a uf).
Proof.
  intros Hwf Hlinked Hne Hchild Hroot Hother.
  rewrite (UnionFind.link_rep_equation E HE child root raise uf a
    Hwf Hlinked Hne Hchild Hroot).
  rewrite (proj2 (eqb_false_iff E HE _ _) Hother). reflexivity.
Qed.

(** The union client exposes the actual two finds and the fully selected loser/survivor cases. *)
Theorem uf_union_rep_equation_client {K} (E : encoding K) (HE : encoding_laws E) uf x y a :
  UnionFind.wf E uf ->
  fst (UnionFind.find E a (UnionFind.union E x y uf)) =
  let '(rx, u1) := UnionFind.find E x uf in
  let '(ry, u2) := UnionFind.find E y u1 in
  if eqb E rx ry then fst (UnionFind.find E a uf)
  else
    match Nat.compare (UnionFind.rank_of E u2 rx) (UnionFind.rank_of E u2 ry) with
    | Eq =>
      if eqb E (fst (UnionFind.find E a uf)) ry then rx else fst (UnionFind.find E a uf)
    | Lt =>
      if eqb E (fst (UnionFind.find E a uf)) rx then ry else fst (UnionFind.find E a uf)
    | Gt =>
      if eqb E (fst (UnionFind.find E a uf)) ry then rx else fst (UnionFind.find E a uf)
    end.
Proof.
  exact (UnionFind.union_rep_equation E HE uf x y a).
Qed.

(** Rank selection transports the losing representative from the actual compressed intermediates. *)
Theorem uf_union_lower_rank_rep_client {K} (E : encoding K) (HE : encoding_laws E)
    uf x y a rx u1 ry u2 :
  UnionFind.wf E uf ->
  UnionFind.find E x uf = (rx, u1) -> UnionFind.find E y u1 = (ry, u2) ->
  eqb E rx ry = false ->
  Nat.compare (UnionFind.rank_of E u2 rx) (UnionFind.rank_of E u2 ry) = Lt ->
  fst (UnionFind.find E a uf) = rx ->
  fst (UnionFind.find E a (UnionFind.union E x y uf)) = ry.
Proof.
  intros Hwf Hx Hy Hdistinct Hrank Hrep.
  rewrite (UnionFind.union_rep_equation E HE uf x y a Hwf).
  rewrite Hx, Hy, Hdistinct, Hrank, Hrep, eqb_refl. reflexivity.
Qed.
