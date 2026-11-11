(** * Growing-registry Memo fixtures

    Recursive misses retain newly allocated IDs and child cache entries.
    For example, looking up a parent after another allocation retains the current registry.
    Builds on: BaseMemoState and BaseIntern. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseMemo BaseIntern BaseMemoState.
Import List.ListNotations Cost.Notations.

Definition root_registry := snd (Intern.intern nat_encoding 10 Intern.empty).

Definition child_miss_c (cache : Memo.t positive nat) (state : Intern.t nat)
    : Cost.t (MemoState.result nat (Intern.t nat)) :=
  let* child := Intern.intern_c nat_encoding 20 state in
  let* stored := Map.set_c positive_encoding (fst child) 7 cache in
  Cost.ret ((9, stored), snd child).

Definition parent_miss := MemoState.run 1 child_miss_c Memo.empty root_registry.

Example parent_and_child_entries_survive :
  Map.get positive_encoding 1%positive (snd (fst (fst parent_miss))) = Some 9 /\
  Map.get positive_encoding 2%positive (snd (fst (fst parent_miss))) = Some 7 /\
  Intern.key_of 2%positive (snd (fst parent_miss)) = Some 20 /\
  snd parent_miss = false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition newer_registry :=
  snd (Intern.intern nat_encoding 30 (snd (fst parent_miss))).

Definition rejected_miss_c (cache : Memo.t positive nat) (state : Intern.t nat) :=
  Cost.step ;; Cost.ret ((0, cache), state).

Example hit_retains_current_registry :
  let hit := MemoState.run 1 rejected_miss_c
    (snd (fst (fst parent_miss))) newer_registry in
  fst (fst (fst hit)) = 9 /\
  Intern.key_of 3%positive (snd (fst hit)) = Some 30 /\
  snd hit = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example absent_id_is_not_a_cached_default :
  Map.get positive_encoding 3%positive (snd (fst (fst parent_miss))) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example initially_unallocated_id_has_no_meaning :
  MemoState.intern_meaning S root_registry 2%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example old_meaning_survives_new_allocation :
  MemoState.extends (MemoState.intern_meaning S)
    root_registry (snd (Intern.intern nat_encoding 20 root_registry)).
Proof.
  apply (MemoState.intern_extends nat_encoding nat_encoding_laws).
  apply Intern.intern_wf; [exact nat_encoding_laws|apply Intern.wf_empty].
Qed.

Example callback_charge_is_retained :
  Cost.ticks (MemoState.run_c 1
    (fun cache state => Cost.tick 2 ;; Cost.ret ((42, cache), state))
    Memo.empty tt) = 9%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example hit_pays_one_lookup :
  Cost.ticks (MemoState.run_c 1 rejected_miss_c
    (snd (fst (fst parent_miss))) newer_registry) = 3%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition optional_reference key := if Nat.eqb key 10 then None else Some key.
Definition optional_meaning := MemoState.intern_meaning optional_reference.
Definition optional_registry := Intern.of_list nat_encoding [10; 20].
Definition optional_cache : Memo.t positive (option nat) :=
  Map.set positive_encoding 2%positive (Some 20) Memo.empty.

Definition optional_miss_c (cache : Memo.t positive (option nat)) (state : Intern.t nat)
    : Cost.t (MemoState.result (option nat) (Intern.t nat)) :=
  let* child := Intern.intern_c nat_encoding 30 state in
  let* stored := Map.set_c positive_encoding (fst child) (Some 30) cache in
  Cost.ret ((None, stored), snd child).

Example optional_initial_cache_valid :
  MemoState.valid optional_meaning optional_registry optional_cache.
Proof.
  apply MemoState.valid_set; [apply MemoState.valid_empty|].
  vm_compute. reflexivity.
Qed.

Example optional_allocated_meaning_and_unallocated_control :
  optional_meaning optional_registry 1%positive = Some None /\
  optional_meaning optional_registry 3%positive = None.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example nonempty_registry_and_cache_agreement :
  MemoState.result_valid optional_meaning (Intern.wf nat_encoding)
    optional_registry None (fst (MemoState.run 1 optional_miss_c optional_cache optional_registry)).
Proof.
  pose proof (Intern.wf_of_list nat_encoding nat_encoding_laws [10; 20]) as Hwf.
  pose proof (MemoState.intern_extends nat_encoding nat_encoding_laws optional_reference
    30 optional_registry Hwf) as Hextends.
  apply MemoState.run_agrees.
  - exact optional_initial_cache_valid.
  - exact Hwf.
  - exact (proj1 optional_allocated_meaning_and_unallocated_control).
  - intro Habsent. unfold optional_miss_c. autorewrite with galois_cost.
    fold (Intern.intern nat_encoding 30 optional_registry).
    fold (Map.set positive_encoding (fst (Intern.intern nat_encoding 30 optional_registry))
      (Some 30) optional_cache).
    split; [reflexivity|]. split.
    + apply MemoState.valid_set.
      * exact (MemoState.valid_transport _ _ _ _ Hextends optional_initial_cache_valid).
      * unfold optional_meaning, MemoState.intern_meaning.
        rewrite (Intern.key_of_intern nat_encoding nat_encoding_laws 30 optional_registry Hwf).
        reflexivity.
    + split.
      * exact (Intern.intern_wf nat_encoding nat_encoding_laws 30 optional_registry Hwf).
      * exact Hextends.
Qed.

Example nonempty_agreement_retains_all_three_results :
  let answer := MemoState.run 1 optional_miss_c optional_cache optional_registry in
  Map.get positive_encoding 1%positive (snd (fst (fst answer))) = Some None /\
  Map.get positive_encoding 2%positive (snd (fst (fst answer))) = Some (Some 20) /\
  Map.get positive_encoding 3%positive (snd (fst (fst answer))) = Some (Some 30).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition unsupported_cache :=
  Map.set positive_encoding 1%positive None optional_cache.

Example hit_agreement_does_not_require_unselected_miss_correctness :
  MemoState.result_valid optional_meaning (Intern.wf nat_encoding) optional_registry None
    (fst (MemoState.run 1
      (fun cache state => Cost.ret ((Some 999, cache), state))
      unsupported_cache optional_registry)).
Proof.
  apply MemoState.run_agrees.
  - apply MemoState.valid_set; [exact optional_initial_cache_valid|].
    exact (proj1 optional_allocated_meaning_and_unallocated_control).
  - apply Intern.wf_of_list, nat_encoding_laws.
  - exact (proj1 optional_allocated_meaning_and_unallocated_control).
  - intro Habsent.
    change (Map.get positive_encoding 1%positive
      (Map.set positive_encoding 1%positive None optional_cache) = None) in Habsent.
    rewrite Map.get_set_same in Habsent by exact (proj1 optional_initial_cache_valid).
    discriminate.
Qed.
