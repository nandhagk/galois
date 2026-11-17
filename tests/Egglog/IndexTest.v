(** * Stored tuple index regressions

    These examples exercise prefix sharing, duplicate insertion and deletion.
    For example, deleting one tuple leaves another tuple with the same first cell live.
    Builds on: Index, Syntax and the operations-only value interface. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
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

(** Inserting a second triple follows the shared prefix and allocates only its fresh suffix. *)
Example insert_shared_prefix_fresh_suffix :
  let first := [Val 2; Val 3; Val 7]%positive in
  let second := [Val 2; Val 5; Val 11]%positive in
  let ix := RuntimeIndex.insert second (RuntimeIndex.insert first RuntimeIndex.empty) in
  (RuntimeIndex.contains first ix, RuntimeIndex.contains second ix,
   RuntimeIndex.child ix 1 (Val 2)%positive,
   RuntimeIndex.child ix 2 (Val 5)%positive,
   RuntimeIndex.child ix 5 (Val 11)%positive, RuntimeIndex.next ix) =
    (true, true, Some 2%positive, Some 5%positive, Some 6%positive, 6%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** A missing middle cell makes removal retain the entire original triple index. *)
Example absent_removal_after_shared_prefix :
  let ix := RuntimeIndex.insert [Val 2; Val 3; Val 7]%positive RuntimeIndex.empty in
  RuntimeIndex.remove [Val 2; Val 5; Val 11]%positive ix = ix.
Proof.
  vm_compute. reflexivity.
Qed.

(** Removing shared tuples drops their empty nodes while preserving the allocation counter. *)
Example removing_shared_tuples_drops_empty_nodes :
  let one := RuntimeIndex.remove first_tuple shared_index in
  let none := RuntimeIndex.remove second_tuple one in
  (length (PTrieCode.elements (index_nodes shared_index)),
   length (PTrieCode.elements (index_nodes one)),
   length (PTrieCode.elements (index_nodes none)), RuntimeIndex.next none) =
    (4%nat, 3%nat, 0%nat, 4%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** A nonzero cached degree prevents an edgeless node from being discarded. *)
Example empty_edges_with_degree_survive_write :
  let nd : index_node (cell IndexFixtureValue.t) := IndexNode PTrieCode.empty 5%N false in
  RuntimeIndex.read_node
    (RuntimeIndex.write_node RuntimeIndex.empty 1%positive nd 1%positive) 1%positive = nd.
Proof.
  vm_compute. reflexivity.
Qed.

(** Clearing the last root terminal removes its table entry. *)
Example empty_tuple_terminal_prunes_table :
  let present := RuntimeIndex.insert [] RuntimeIndex.empty in
  let absent := RuntimeIndex.remove [] present in
  (length (PTrieCode.elements (index_nodes present)),
   length (PTrieCode.elements (index_nodes absent)),
   RuntimeIndex.contains [] present, RuntimeIndex.contains [] absent) =
    (1%nat, 0%nat, true, false).
Proof.
  vm_compute. reflexivity.
Qed.

(** A fresh two-cell suffix preserves the entire state produced by the specified step walk. *)
Example fresh_insertion_matches_step_reference :
  let first := [Val 2; Val 3; Val 7]%positive in
  let second := [Val 2; Val 5; Val 11]%positive in
  let ix := RuntimeIndex.insert first RuntimeIndex.empty in
  RuntimeIndex.insert second ix =
    RuntimeIndex.insert_finish second ix
      (fold_left RuntimeIndex.insert_step_st second (RuntimeIndex.start ix)).
Proof.
  vm_compute. reflexivity.
Qed.
