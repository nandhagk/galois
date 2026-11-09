(** * Growing-registry Memo fixtures

    Recursive misses retain newly allocated IDs and child cache entries.
    For example, looking up a parent after another allocation retains the current registry.
    Builds on: BaseMemoState and BaseIntern. *)

From Stdlib Require Import NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseMemo BaseIntern BaseMemoState.
Import Cost.Notations.

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
