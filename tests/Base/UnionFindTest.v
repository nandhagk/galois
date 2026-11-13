(** * Union-find reference fixtures

    These fixtures observe representatives and path compression.
    For example, a lookup of an unknown key returns that key.
    Builds on: UnionFind and Trie. *)

From Stdlib Require Import List NArith Lia.
From Galois.Base Require Import Trie UnionFind.
Import List.ListNotations.

Definition uf_pairs : list (positive * positive) := [(1, 2); (3, 4); (1, 3)]%positive.
Definition uf_sample := fold_left
  (fun u xy => snd (UnionFindCode.union (fst xy) (snd xy) u)) uf_pairs UnionFindCode.empty.
Definition uf_pair := snd (UnionFindCode.union 1%positive 2%positive UnionFindCode.empty).

Example uf_successful_find : fst (UnionFindCode.find 4%positive uf_sample) = 1%positive.
Proof. vm_compute. reflexivity. Qed.
Example uf_successful_union :
  Pos.eqb (fst (UnionFindCode.find 2%positive uf_sample))
    (fst (UnionFindCode.find 4%positive uf_sample)) = true.
Proof. vm_compute. reflexivity. Qed.
Example uf_unrelated :
  Pos.eqb (fst (UnionFindCode.find 1%positive uf_pair))
    (fst (UnionFindCode.find 3%positive uf_pair)) = false.
Proof. vm_compute. reflexivity. Qed.
Example uf_unknown :
  Pos.eqb (fst (UnionFindCode.find 4%positive uf_sample))
    (fst (UnionFindCode.find 5%positive uf_sample)) = false.
Proof. vm_compute. reflexivity. Qed.
Example uf_unknown_reflexive :
  Pos.eqb (fst (UnionFindCode.find 5%positive uf_sample))
    (fst (UnionFindCode.find 5%positive uf_sample)) = true.
Proof. vm_compute. reflexivity. Qed.
Example uf_unknown_find :
  UnionFindCode.find 5%positive uf_sample = (5%positive, uf_sample).
Proof. vm_compute. reflexivity. Qed.
Example uf_unknown_walk_has_no_path :
  UnionFindCode.walk 5%positive uf_sample = (5%positive, []).
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
Example uf_compression_classes :
  let compressed := snd (UnionFindCode.find 4%positive uf_sample) in
  Pos.eqb (fst (UnionFindCode.find 2%positive compressed))
    (fst (UnionFindCode.find 4%positive compressed)) = true.
Proof. vm_compute. reflexivity. Qed.

Example uf_empty : UnionFind.support UnionFind.empty = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_singleton :
  UnionFind.support (snd (UnionFind.union 1%positive 1%positive UnionFind.empty)) =
  [1%positive].
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_same_class :
  snd (UnionFindCode.union 1%positive 2%positive uf_pair) = uf_pair.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_before_compression : PTrieCode.get 4%positive (parents uf_sample) = Some 3%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_after_compression :
  PTrieCode.get 4%positive (parents (snd (UnionFindCode.find 4%positive uf_sample))) =
  Some 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example uf_key_order : UnionFind.support uf_sample = [4; 2; 1; 3]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** The original link plan permits an absent losing root with an unconstrained rank. *)
Example uf_link_plan_absent_root :
  let u := UnionFind.add 1%positive UnionFind.empty in
  let rk := fun x => if Pos.eqb x 2%positive then 1%nat else 0%nat in
  UnionFind.wf u /\ UnionFind.ranked u rk /\
  UnionFind.is_root u 1%positive /\ UnionFind.is_root u 2%positive /\
  1%positive <> 2%positive /\
  UnionFind.size_of u 2%positive <= UnionFind.size_of u 1%positive /\
  ~ UnionFind.ranked (UnionFind.link 1%positive 2%positive u)
    (fun x => if Pos.eqb x 1%positive
      then Nat.max (rk 1%positive) (S (rk 2%positive)) else rk x).
Proof.
  cbv zeta. set (u := UnionFind.add 1%positive UnionFind.empty).
  set (rk := fun x => if Pos.eqb x 2%positive then 1%nat else 0%nat).
  assert (Hwf : UnionFind.wf u).
  { apply UnionFind.wf_add, UnionFind.wf_empty. }
  assert (Hmember : forall x, UnionFind.mem u x -> x = 1%positive).
  { intros x Hmem. apply UnionFind.support_spec in Hmem.
    change (In x [1%positive]) in Hmem.
    cbn [In] in Hmem. destruct Hmem as [Heq|Hfalse]; [congruence|contradiction]. }
  assert (Hroot1 : UnionFind.is_root u 1%positive) by (vm_compute; reflexivity).
  assert (Hroot2 : UnionFind.is_root u 2%positive) by (vm_compute; reflexivity).
  assert (Hranked : UnionFind.ranked u rk).
  { split.
    - intros x Hmem Hnonroot. apply Hmember in Hmem. subst x. contradiction.
    - intros r Hmem Hroot. apply Hmember in Hmem. subst r. vm_compute. lia. }
  refine (conj Hwf (conj Hranked (conj Hroot1 (conj Hroot2 (conj _ (conj _ _)))))).
  - discriminate.
  - vm_compute. lia.
  - intros [_ Hroots].
    assert (Hmem : UnionFind.mem (UnionFind.link 1%positive 2%positive u) 1%positive).
    { vm_compute. discriminate. }
    assert (Hroot : UnionFind.is_root (UnionFind.link 1%positive 2%positive u) 1%positive).
    { vm_compute. reflexivity. }
    specialize (Hroots 1%positive Hmem Hroot). vm_compute in Hroots. lia.
Qed.

(* BaseUnionFindTest.uf_compression_ranks compares ranks and max_rank. Union by size deletes those
   stored fields. uf_exhausted and uf_exhausted_prefix exercise find_fuel with
   caller budgets 0 and 1 and expect the current key 4 and intermediate key 3.
   find now computes its fuel from the allocation count and exports no budget
   argument. These budget observations retire with find_fuel.
   uf_empty_find_ticks, uf_exhausted_ticks, uf_singleton_union_ticks,
   uf_distinct_union_ticks and uf_pair_find_ticks retire with Cost.ticks.
   The symbolic rank/link transport clients use the replaced by-rank internals. *)
