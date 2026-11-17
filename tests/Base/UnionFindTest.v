(** * Union-find reference fixtures

    These fixtures observe representatives and path compression.
    For example, a lookup of an unknown key returns that key.
    Builds on: UnionFind and Trie.

    Groups:
    - [FindTests] Representatives, unknown keys and path compression.
    - [UnionTests] Which keys share a class after a union, and the roots that a union picks.
    - [SupportTests] The keys that a forest holds, in order.
    - [StaleSizeTests] A stored size that outlives its key, and the add that resets it. *)

From Stdlib Require Import List NArith Lia.
From Galois.Base Require Import Trie UnionFind.
Import List.ListNotations.

(** * Fixtures *)

(** The unions performed on the sample forest, in order. *)
Definition uf_pairs : list (positive * positive) := [(1, 2); (3, 4); (1, 3)]%positive.

(** The forest after the unions of uf_pairs. *)
Definition uf_sample := fold_left
  (fun u xy => snd (UnionFindCode.union (fst xy) (snd xy) u)) uf_pairs UnionFindCode.empty.

(** The forest after the single union of 1 and 2. *)
Definition uf_pair := snd (UnionFindCode.union 1%positive 2%positive UnionFindCode.empty).

(** * Find *)

Module FindTests.

  (** Finding a key in a union returns the root of its class. *)
  Example find_returns_root_of_union :
    fst (UnionFindCode.find 4%positive uf_sample) = 1%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** Keys that were unioned share one representative. *)
  Example union_joins_classes :
    Pos.eqb (fst (UnionFindCode.find 2%positive uf_sample))
      (fst (UnionFindCode.find 4%positive uf_sample)) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Keys that were never unioned keep distinct representatives. *)
  Example unrelated_keys_stay_apart :
    Pos.eqb (fst (UnionFindCode.find 1%positive uf_pair))
      (fst (UnionFindCode.find 3%positive uf_pair)) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** An unknown key has a different representative from a member of the forest. *)
  Example unknown_keys_are_distinct :
    Pos.eqb (fst (UnionFindCode.find 4%positive uf_sample))
      (fst (UnionFindCode.find 5%positive uf_sample)) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** An unknown key is its own representative. *)
  Example unknown_key_is_its_own_class :
    Pos.eqb (fst (UnionFindCode.find 5%positive uf_sample))
      (fst (UnionFindCode.find 5%positive uf_sample)) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Finding an unknown key returns that key and leaves the forest unchanged. *)
  Example find_unknown_returns_key_and_forest :
    UnionFindCode.find 5%positive uf_sample = (5%positive, uf_sample).
  Proof. vm_compute. reflexivity. Qed.

  (** Walking an unknown key gives a path with no steps. *)
  Example walk_unknown_has_no_path :
    UnionFindCode.walk 5%positive uf_sample = (5%positive, []).
  Proof. vm_compute. reflexivity. Qed.

  (** Finding a key in the empty forest returns that key. *)
  Example find_in_empty_returns_key :
    UnionFindCode.find 1%positive UnionFindCode.empty = (1%positive, UnionFindCode.empty).
  Proof. vm_compute. reflexivity. Qed.

  (** Compression keeps the keys of each class together. *)
  Example compression_keeps_classes :
    let compressed := snd (UnionFindCode.find 4%positive uf_sample) in
    Pos.eqb (fst (UnionFindCode.find 2%positive compressed))
      (fst (UnionFindCode.find 4%positive compressed)) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Before compression, the parent of key 4 is key 3. *)
  Example parent_before_compression :
    PTrieCode.get 4%positive (parents uf_sample) = Some 3%positive.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** After a find, the parent of key 4 is the root. *)
  Example compression_points_to_root :
    PTrieCode.get 4%positive (parents (snd (UnionFindCode.find 4%positive uf_sample))) =
    Some 1%positive.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A second find on a compressed path returns the root and the same forest. *)
  Example compressed_path_finds_root_again :
    let u := snd (UnionFindCode.find 4%positive uf_sample) in
    UnionFindCode.find 4%positive u = (1%positive, u).
  Proof.
    vm_compute. reflexivity.
  Qed.

End FindTests.

(** * Union *)

Module UnionTests.

  (** Unioning a key with a key of lower rank keeps the root of the lower-rank side. *)
  Example union_chooses_root_by_rank_left :
    fst (UnionFindCode.find 3%positive (snd (UnionFindCode.union 3%positive 1%positive uf_pair))) =
      1%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** Unioning in the other argument order gives the same root. *)
  Example union_chooses_root_by_rank_right :
    fst (UnionFindCode.find 3%positive (snd (UnionFindCode.union 1%positive 3%positive uf_pair))) =
      1%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** Unioning two keys of one class leaves the forest unchanged. *)
  Example union_of_same_class_changes_nothing :
    snd (UnionFindCode.union 1%positive 2%positive uf_pair) = uf_pair.
  Proof.
    vm_compute. reflexivity.
  Qed.

End UnionTests.

(** * Support *)

Module SupportTests.

  (** The empty forest has no support. *)
  Example empty_forest_has_no_support : UnionFind.support UnionFind.empty = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A forest with one union of a key with itself has that key as its support. *)
  Example singleton_support_is_its_key :
    UnionFind.support (snd (UnionFind.union 1%positive 1%positive UnionFind.empty)) =
    [1%positive].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The support lists the keys of the sample forest in order. *)
  Example support_lists_keys_in_order :
    UnionFind.support uf_sample = [4; 2; 1; 3]%positive.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SupportTests.

(** * Stale size *)

Module StaleSizeTests.

  (** A forest with two singletons, and a stored size for key 3 that is not a member. *)
  Definition uf_two_singletons :=
    UnionFindCode.add 1%positive (UnionFindCode.add 2%positive UnionFindCode.empty).

  (** The two singletons with the stale size 2 stored at the absent key 3. *)
  Definition uf_stale_size :=
    UF (parents uf_two_singletons) (PTrieCode.set 3%positive 2%N (sizes uf_two_singletons))
      (count uf_two_singletons).

  (** This is the proposed T7 body, retained only to check its rejected behavior. *)
  Definition uf_add_without_size_reset (x : positive) (u : uf) : uf :=
    match PTrieCode.get x (parents u) with
    | Some _ => u
    | None => UF (PTrieCode.set x x (parents u)) (sizes u) (N.succ (count u))
    end.

  (** An absent key may carry a bounded stale size under the current forest invariant. *)
  Local Lemma uf_wf_stale_size u r n :
    UnionFind.wf u -> ~ UnionFind.mem u r -> N.to_nat n <= UnionFind.card u ->
    UnionFind.wf (UF (parents u) (PTrieCode.set r n (sizes u)) (count u)).
  Proof.
    intros [Hcard [Hparents [Hroots [Hsizes [rk Hranks]]]]] Hfresh Hbound.
    split; [exact Hcard|]. split; [exact Hparents|]. split.
    - intros q Hmem Hroot.
      assert (Hne : q <> r).
      { intro Heq. subst q. apply Hfresh. exact Hmem. }
      change (N.to_nat
        (match PTrieCode.get q (PTrieCode.set r n (sizes u)) with
         | Some size => size
         | None => 1%N
         end) = UnionFind.size_of u q).
      rewrite PTrie.get_set_other by exact Hne. exact (Hroots q Hmem Hroot).
    - split.
      + intros q m Hget.
        change (PTrieCode.get q (PTrieCode.set r n (sizes u)) = Some m) in Hget.
        destruct (Pos.eq_dec q r) as [Heq|Hne].
        * subst q. rewrite PTrie.get_set_same in Hget. injection Hget as Hvalue.
          subst m. exact Hbound.
        * rewrite PTrie.get_set_other in Hget by exact Hne. exact (Hsizes q m Hget).
      + exists rk. exact Hranks.
  Qed.

  (** Leaving the stale size unchanged breaks well-formedness when its key becomes a member. *)
  Example unchanged_size_breaks_wellformedness :
    UnionFind.wf uf_stale_size /\
    ~ UnionFind.wf (uf_add_without_size_reset 3%positive uf_stale_size).
  Proof.
    split.
    - unfold uf_stale_size. apply uf_wf_stale_size.
      + apply UnionFind.wf_add, UnionFind.wf_add, UnionFind.wf_empty.
      + vm_compute. tauto.
      + vm_compute. lia.
    - intro Hwf.
      assert (Hmem : UnionFind.mem (uf_add_without_size_reset 3%positive uf_stale_size)
        3%positive).
      { vm_compute. discriminate. }
      assert (Hroot : UnionFind.is_root (uf_add_without_size_reset 3%positive uf_stale_size)
        3%positive).
      { vm_compute. reflexivity. }
      pose proof (proj1 (proj2 (proj2 Hwf)) 3%positive Hmem Hroot) as Hsize.
      vm_compute in Hsize. discriminate.
  Qed.

  (** The retained add operation resets that stale size to the singleton default. *)
  Example add_resets_stale_size :
    UnionFindCode.size_at 3%positive (UnionFindCode.add 3%positive uf_stale_size) = 1%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A union-find with the single member 1. Key 2 is absent, so it is its own root. *)
  Definition single_member := UnionFind.add 1%positive UnionFind.empty.

  (** A rank function that gives the absent key 2 the rank one and every other key zero. *)
  Definition deep_rank (x : positive) : nat :=
    if Pos.eqb x 2%positive then 1%nat else 0%nat.

  (** The rank function after linking 2 under 1, where key 1 takes one more than key 2. *)
  Definition linked_rank (x : positive) : nat :=
    if Pos.eqb x 1%positive
    then Nat.max (deep_rank 1%positive) (S (deep_rank 2%positive))
    else deep_rank x.

  (** The original link plan permits an absent losing root with an unconstrained rank. *)
  Example link_can_break_ranking :
    UnionFind.wf single_member /\ UnionFind.ranked single_member deep_rank /\
    UnionFind.is_root single_member 1%positive /\ UnionFind.is_root single_member 2%positive /\
    1%positive <> 2%positive /\
    UnionFind.size_of single_member 2%positive <= UnionFind.size_of single_member 1%positive /\
    ~ UnionFind.ranked (UnionFind.link 1%positive 2%positive single_member) linked_rank.
  Proof.
    set (u := single_member). set (rk := deep_rank).
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

End StaleSizeTests.
