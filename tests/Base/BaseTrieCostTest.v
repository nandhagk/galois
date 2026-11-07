(** * Trie cost observations

    These examples separate skipped subtree overhead from arbitrary callback charges.
    For example, intersecting three keys with ten thousand keys visits three shared nodes.
    Builds on: BaseTrie, BaseTrieMerge and BaseTrieCost. *)

From Stdlib Require Import NArith List.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseTrie BaseTrieMerge BaseTrieCost.

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
