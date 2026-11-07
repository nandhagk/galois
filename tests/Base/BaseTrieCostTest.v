(** * Trie cost observations

    These examples separate skipped subtree overhead from arbitrary callback charges.
    For example, intersecting three keys with ten thousand keys visits three shared nodes.
    Builds on: BaseTrie, BaseTrieMerge and BaseTrieCost. *)

From Stdlib Require Import NArith List.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseTrie BaseTrieMerge BaseTrieCost.

Fixpoint keys_from (n : nat) (p : positive) : list positive :=
  match n with
  | O => nil
  | S n => p :: keys_from n (Pos.succ p)
  end.

Definition build n :=
  Cost.value (fold_left_c (fun tr p => Trie.set_c p true tr) (keys_from n 1) Trie.empty).
Definition small := build 3.
Definition large := build (10 * 1000).
Definition zero_callback (_ _ : bool) := Cost.ret true.

Example lookup_thirteen : Cost.ticks (Trie.get_c 13 large) = 4%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example small_large_intersection :
  (TrieMerge.size (Cost.value (TrieMerge.inter_with_c zero_callback small large)),
    Cost.ticks (TrieMerge.inter_with_c zero_callback small large)) = (3%nat, 6%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example large_small_intersection :
  Cost.ticks (TrieMerge.inter_with_c zero_callback large small) = 10%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example same_small_intersection :
  Cost.ticks (TrieMerge.inter_with_c zero_callback small small) = 6%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example three_key_bound :
  N.leb (Cost.ticks (TrieMerge.inter_with_c zero_callback small large))
    (TrieCost.trie_k * 4 * (1 + 2)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example absent_subtree_cost :
  (Cost.ticks (TrieMerge.inter_with_c zero_callback small Trie.empty),
    Cost.ticks (TrieMerge.diff_c small (Trie.empty : Trie.t bool)),
    Cost.ticks (TrieMerge.union_with_c zero_callback small Trie.empty)) = (1%N, 1%N, 1%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example retain_callback_charges :
  Cost.ticks (TrieMerge.inter_with_c
    (fun (_ _ : bool) => Cost.lift (fun _ => 1000%N) (fun _ => true) tt)
    small large) = 3006%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example general_combine_changes_one_side :
  Cost.ticks (TrieMerge.combine_c
    (fun (a : option bool) (_ : option bool) =>
      Cost.lift (fun _ => 1000%N) (fun _ => a) tt) small Trie.empty) = 3007%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example traversal_counts :
  (Cost.ticks (TrieMerge.size_c small), Cost.ticks (TrieMerge.elements_c small),
    TrieCost.key_mass small) = (6%N, 11%N, 5%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example stateful_fold_charges :
  let result := TrieMerge.fold_c
    (fun acc (_ : positive) (_ : bool) =>
      Cost.lift (fun _ => 1000%N) S acc) small 0%nat in
  (Cost.value result, Cost.ticks result) = (3%nat, 3008%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Appending the visited code distinguishes order, and pricing uses the reached accumulator. *)
Definition ordered_accumulator_c (acc : N) (p : positive) (_ : bool) : Cost.t N :=
  Cost.lift (fun current => (current + 1)%N)
    (fun current => (10 * current + N.pos p)%N) acc.

Definition ordered_map : Map.t positive bool :=
  Map.set positive_encoding 1%positive true
    (Map.set positive_encoding 2%positive true
      (Map.set positive_encoding 3%positive true Map.empty)).

Example keyed_fold_uses_reached_accumulator :
  let result := TrieMerge.fold_c ordered_accumulator_c small 0%N in
  (Cost.value result, Cost.ticks result) = (213%N, 34%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example code_free_fold_uses_reached_accumulator :
  let result := Map.fold_c ordered_accumulator_c ordered_map 0%N in
  (Cost.value result, Cost.ticks result) = (213%N, 32%N).
Proof.
  vm_compute. reflexivity.
Qed.

Definition comparison_map : Trie.t N :=
  Trie.set 1 1%N (Trie.set 2 2%N (Trie.set 3 3%N Trie.empty)).
Definition comparison_mismatch := Trie.set 2 9%N comparison_map.

(** Code-three's payload makes a later comparison expensive after the first binding passes. *)
Definition late_comparison_c (v : N) (other : option N) : Cost.t bool :=
  Cost.lift (fun value => if N.eqb value 3 then 1000%N else 0%N)
    (fun value =>
      match other with
      | Some expected => N.eqb value expected
      | None => false
      end) v.

Example comparison_rejection_skips_later_charge :
  let result := TrieMerge.forall2_c late_comparison_c comparison_map comparison_mismatch in
  (Cost.value result, Cost.ticks result) = (false, 3%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example comparison_success_retains_later_charge :
  let result := TrieMerge.forall2_c late_comparison_c comparison_map comparison_map in
  (Cost.value result, Cost.ticks result) = (true, 1006%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_rejection_skips_later_and_reverse_charges :
  let result := TrieMerge.beq_c (fun a b => late_comparison_c a (Some b))
    comparison_map comparison_mismatch in
  (Cost.value result, Cost.ticks result) = (false, 3%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_success_retains_both_comparison_charges :
  let result := TrieMerge.beq_c (fun a b => late_comparison_c a (Some b))
    comparison_map comparison_map in
  (Cost.value result, Cost.ticks result) = (true, 2012%N).
Proof.
  vm_compute. reflexivity.
Qed.

Definition deep_singleton := Trie.set 13 true Trie.empty.
Definition deep_singleton_map := Map.set positive_encoding 13%positive true Map.empty.

Example deep_singleton_distinguishes_size_measures :
  (TrieCost.skeleton_nodes deep_singleton, TrieMerge.size deep_singleton,
    TrieCost.key_mass deep_singleton, Map.size deep_singleton_map) =
    (4%N, 1%nat, 4%N, 1%nat).
Proof.
  vm_compute. reflexivity.
Qed.

Example deep_singleton_keyed_and_code_free_traversals :
  let keyed := TrieMerge.fold_c (fun (_ : positive) p (_ : bool) => Cost.ret p)
    deep_singleton 1%positive in
  let code_free := Map.fold_c (fun (_ : positive) p (_ : bool) => Cost.ret p)
    deep_singleton_map 1%positive in
  ((Cost.value keyed, Cost.ticks keyed), (Cost.value code_free, Cost.ticks code_free)) =
    ((13%positive, 8%N), (13%positive, 5%N)).
Proof.
  vm_compute. reflexivity.
Qed.
