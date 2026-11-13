(** * Stored tuple index regressions

    These examples exercise prefix sharing, duplicate insertion and deletion.
    For example, deleting one tuple leaves another tuple with the same first cell live.
    Builds on: Index, Syntax and the operations-only value interface. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Index.

Import List.ListNotations.
Open Scope positive_scope.

Module IndexFixtureValue <: VALUE_OPS.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (_ : positive) (_ : list t) : option t := None.
  Definition merge (_ : positive) := Pos.max.
End IndexFixtureValue.

Module RuntimeIndex := IndexCode IndexFixtureValue.

Definition first_tuple := [Val 2; Val 3]%positive.
Definition second_tuple := [Val 2; Val 5]%positive.
Definition shared_index := RuntimeIndex.insert second_tuple
  (RuntimeIndex.insert first_tuple RuntimeIndex.empty).

(** Both rows share the first node and retain separate terminal children. *)
Example shared_prefix_navigation :
  (RuntimeIndex.child shared_index 1 (Val 2),
   RuntimeIndex.child shared_index 2 (Val 3),
   RuntimeIndex.child shared_index 2 (Val 5),
   RuntimeIndex.degree shared_index 1,
   RuntimeIndex.degree shared_index 2) =
    (Some 2, Some 3, Some 4, 1%N, 2%N)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** Repeated insertion leaves all counters and stored nodes unchanged. *)
Example duplicate_insertion_keeps_state :
  RuntimeIndex.insert first_tuple shared_index = shared_index.
Proof.
  vm_compute. reflexivity.
Qed.

(** Deleting an absent tuple leaves the original state unchanged. *)
Example absent_removal_keeps_state :
  RuntimeIndex.remove [Val 2; Val 9]%positive shared_index = shared_index.
Proof.
  vm_compute. reflexivity.
Qed.

(** Removing one shared tuple leaves its sibling present and the shared edge live. *)
Example remove_one_shared_tuple :
  let ix := RuntimeIndex.remove first_tuple shared_index in
  (RuntimeIndex.contains first_tuple ix, RuntimeIndex.contains second_tuple ix,
   RuntimeIndex.child ix 1 (Val 2)%positive, RuntimeIndex.degree ix 2%positive,
   RuntimeIndex.next ix) = (false, true, Some 2%positive, 1%N, 4%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** Removing the last tuple unlinks the prefix while preserving the allocation counter. *)
Example remove_last_tuple_unlinks_prefix :
  let ix := RuntimeIndex.remove second_tuple (RuntimeIndex.remove first_tuple shared_index) in
  (RuntimeIndex.children ix 1%positive, RuntimeIndex.degree ix 1%positive,
   RuntimeIndex.next ix) = ([], 0%N, 4%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** Reinsertion after pruning allocates fresh nodes and restores tuple membership. *)
Example reinsert_after_pruning :
  let ix := RuntimeIndex.insert first_tuple
    (RuntimeIndex.remove second_tuple (RuntimeIndex.remove first_tuple shared_index)) in
  (RuntimeIndex.contains first_tuple ix, RuntimeIndex.child ix 1 (Val 2)%positive,
   RuntimeIndex.next ix) = (true, Some 5%positive, 6%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** Identifier and value cells remain distinct even when their payloads agree. *)
Example mixed_cell_edges :
  let ix := RuntimeIndex.insert [Id 2; Val 3]%positive
    (RuntimeIndex.insert [Val 2; Id 3]%positive RuntimeIndex.empty) in
  (RuntimeIndex.contains [Id 2; Val 3]%positive ix,
   RuntimeIndex.contains [Val 2; Id 3]%positive ix,
   RuntimeIndex.contains [Id 2; Id 3]%positive ix,
   RuntimeIndex.degree ix 1%positive) = (true, true, false, 2%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Empty tuples use the root terminal marker without allocating child nodes. *)
Example empty_tuple_terminal :
  let ix := RuntimeIndex.insert [] RuntimeIndex.empty in
  (RuntimeIndex.contains [] ix, RuntimeIndex.contains [] (RuntimeIndex.remove [] ix),
   RuntimeIndex.children ix 1%positive, RuntimeIndex.next ix) =
    (true, false, [], 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** Node identifiers beyond the counter are rejected by every navigation observation. *)
Example unallocated_node_queries :
  (RuntimeIndex.child shared_index 4096 (Val 2)%positive,
   RuntimeIndex.children shared_index 4096%positive,
   RuntimeIndex.degree shared_index 4096%positive) = (None, [], 0%N).
Proof.
  vm_compute. reflexivity.
Qed.
