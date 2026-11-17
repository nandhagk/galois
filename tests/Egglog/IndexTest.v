(** * Stored tuple index regressions

    These examples exercise prefix sharing, duplicate insertion and deletion.
    For example, deleting one tuple leaves another tuple with the same first cell live.
    Builds on: Index, Syntax and the operations-only value interface.

    Groups:
    - NavigationTests: child and degree observations of a shared prefix.
    - InsertTests: insertion of duplicate, shared-prefix and fresh suffixes.
    - RemoveTests: removal of tuples, and pruning of empty nodes and table entries.
    - TerminalTests: the empty tuple and the mixed cell kinds.
    - NodeTests: node identifiers and cached degrees. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import ValueSig Syntax Index.

Import List.ListNotations.

(** * Fixtures *)

(** A value type of positive numbers, with no primitive operations. *)
Module IndexFixtureValue <: VALUE_OPS.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (_ : positive) (_ : list t) : option t := None.
  Definition merge (_ : positive) := Pos.max.
End IndexFixtureValue.

Module RuntimeIndex := IndexCode IndexFixtureValue.

(** The first of two tuples that share their first cell. *)
Definition first_tuple := [Val 2; Val 3]%positive.

(** The second tuple, which shares the first cell with the first tuple. *)
Definition second_tuple := [Val 2; Val 5]%positive.

(** An index that holds both tuples. *)
Definition shared_index := RuntimeIndex.insert second_tuple
  (RuntimeIndex.insert first_tuple RuntimeIndex.empty).

(** The index after the first tuple is removed from the shared index. *)
Definition shared_without_first := RuntimeIndex.remove first_tuple shared_index.

Module NavigationTests.

  Local Open Scope positive_scope.

  (** The shared first cell leads from the root to node two. *)
  Example shared_first_cell_leads_to_node_two :
    RuntimeIndex.child shared_index 1 (Val 2) = Some 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The cell three under node two leads to node three. *)
  Example first_terminal_cell_leads_to_three :
    RuntimeIndex.child shared_index 2 (Val 3) = Some 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The cell five under node two leads to its own node four. *)
  Example second_terminal_cell_leads_to_four :
    RuntimeIndex.child shared_index 2 (Val 5) = Some 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The root of the shared prefix has one edge. *)
  Example prefix_node_has_one_edge :
    RuntimeIndex.degree shared_index 1 = 1%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The node that the shared cell reaches has two edges. *)
  Example shared_node_has_two_edges :
    RuntimeIndex.degree shared_index 2 = 2%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

End NavigationTests.

Module InsertTests.

  Local Open Scope positive_scope.

  (** Repeated insertion leaves all counters and stored nodes unchanged. *)
  Example duplicate_insertion_keeps_state :
    RuntimeIndex.insert first_tuple shared_index = shared_index.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The two triples that share a prefix, and the index that holds both. *)
  Definition triple_first := [Val 2; Val 3; Val 7].
  Definition triple_second := [Val 2; Val 5; Val 11].
  Definition triple_index :=
    RuntimeIndex.insert triple_second (RuntimeIndex.insert triple_first RuntimeIndex.empty).

  (** The first triple is a member of the index after both insertions. *)
  Example first_triple_is_member :
    RuntimeIndex.contains triple_first triple_index = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The second triple is a member of the index after both insertions. *)
  Example second_triple_is_member :
    RuntimeIndex.contains triple_second triple_index = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The shared first cell is reused and leads to node two. *)
  Example shared_prefix_is_reused :
    RuntimeIndex.child triple_index 1 (Val 2) = Some 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The second triple's middle cell leads to node five. *)
  Example second_middle_cell_leads_to_five :
    RuntimeIndex.child triple_index 2 (Val 5) = Some 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The fresh last cell is allocated as node six. *)
  Example fresh_suffix_leads_to_six :
    RuntimeIndex.child triple_index 5 (Val 11) = Some 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Only the fresh suffix allocates identifiers, so the counter ends at six. *)
  Example insertion_counter_ends_at_six :
    RuntimeIndex.next triple_index = 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Reinsertion after pruning restores the first tuple as a member. *)
  Definition reinserted_index :=
    RuntimeIndex.insert first_tuple
      (RuntimeIndex.remove second_tuple (RuntimeIndex.remove first_tuple shared_index)).

  (** A reinserted tuple is a member again. *)
  Example reinserted_tuple_is_member :
    RuntimeIndex.contains first_tuple reinserted_index = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A reinserted prefix leads to a freshly allocated node five. *)
  Example reinserted_prefix_leads_to_five :
    RuntimeIndex.child reinserted_index 1 (Val 2) = Some 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Reinsertion after pruning allocates fresh nodes, so the counter moves on to six. *)
  Example reinsertion_counter_moves_on :
    RuntimeIndex.next reinserted_index = 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The fresh two-cell suffix gives the same state as the step-by-step walk. *)
  Example fresh_suffix_matches_step_reference :
    RuntimeIndex.insert triple_second (RuntimeIndex.insert triple_first RuntimeIndex.empty) =
      RuntimeIndex.insert_finish triple_second
        (RuntimeIndex.insert triple_first RuntimeIndex.empty)
        (fold_left RuntimeIndex.insert_step_st triple_second
          (RuntimeIndex.start (RuntimeIndex.insert triple_first RuntimeIndex.empty))).
  Proof.
    vm_compute. reflexivity.
  Qed.

End InsertTests.

Module RemoveTests.

  Local Open Scope positive_scope.

  (** Deleting an absent tuple leaves the original state unchanged. *)
  Example absent_removal_keeps_state :
    RuntimeIndex.remove [Val 2; Val 9] shared_index = shared_index.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The removed tuple is no longer a member. *)
  Example removed_tuple_is_absent :
    RuntimeIndex.contains first_tuple shared_without_first = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The sibling tuple that shares the removed tuple's prefix stays a member. *)
  Example sibling_tuple_stays_member :
    RuntimeIndex.contains second_tuple shared_without_first = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The shared first edge stays live after one of its tuples is removed. *)
  Example shared_edge_survives_removal :
    RuntimeIndex.child shared_without_first 1 (Val 2) = Some 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The remaining node of the shared prefix has one edge. *)
  Example remaining_node_has_one_edge :
    RuntimeIndex.degree shared_without_first 2 = 1%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Removing a tuple keeps the allocation counter at four. *)
  Example removal_keeps_counter :
    RuntimeIndex.next shared_without_first = 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The index after the second tuple is removed as well. *)
  Definition shared_empty :=
    RuntimeIndex.remove second_tuple shared_without_first.

  (** The unlinked prefix has no children. *)
  Example unlinked_prefix_has_no_children :
    RuntimeIndex.children shared_empty 1 = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unlinked prefix has no edges. *)
  Example unlinked_prefix_has_no_edges :
    RuntimeIndex.degree shared_empty 1 = 0%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Removing the last tuple keeps the allocation counter at four. *)
  Example last_removal_keeps_counter :
    RuntimeIndex.next shared_empty = 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An index that holds the first triple alone. *)
  Definition triple_only := RuntimeIndex.insert [Val 2; Val 3; Val 7] RuntimeIndex.empty.

  (** A missing middle cell makes removal keep the entire original triple index. *)
  Example absent_removal_after_shared_prefix :
    RuntimeIndex.remove [Val 2; Val 5; Val 11] triple_only = triple_only.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The shared index holds four nodes. *)
  Example shared_index_has_four_nodes :
    length (PTrieCode.elements (index_nodes shared_index)) = 4%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Removing the first tuple drops its empty node and leaves three nodes. *)
  Example removing_first_tuple_drops_empty_node :
    length (PTrieCode.elements (index_nodes shared_without_first)) = 3%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Removing both tuples drops every node. *)
  Example removing_shared_tuples_drops_all_nodes :
    length (PTrieCode.elements (index_nodes shared_empty)) = 0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An index that holds only the empty tuple, and the same index after its removal. *)
  Definition empty_present := RuntimeIndex.insert [] RuntimeIndex.empty.
  Definition empty_absent := RuntimeIndex.remove [] empty_present.

  (** The table of the index that holds the empty tuple has one entry. *)
  Example present_table_has_one_entry :
    length (PTrieCode.elements (index_nodes empty_present)) = 1%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Clearing the last root terminal removes its table entry. *)
  Example absent_table_has_no_entries :
    length (PTrieCode.elements (index_nodes empty_absent)) = 0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RemoveTests.

Module TerminalTests.

  Local Open Scope positive_scope.

  (** The empty tuple is a member of the index that holds it. *)
  Example empty_tuple_is_member :
    RuntimeIndex.contains [] (RuntimeIndex.insert [] RuntimeIndex.empty) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The empty tuple is no longer a member after its removal. *)
  Example empty_tuple_removed :
    RuntimeIndex.contains [] (RuntimeIndex.remove [] (RuntimeIndex.insert [] RuntimeIndex.empty))
      = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The empty tuple uses the root terminal marker without allocating child nodes. *)
  Example empty_tuple_adds_no_children :
    RuntimeIndex.children (RuntimeIndex.insert [] RuntimeIndex.empty) 1 = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The counter stays at one after the empty tuple is inserted. *)
  Example empty_tuple_keeps_counter :
    RuntimeIndex.next (RuntimeIndex.insert [] RuntimeIndex.empty) = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Identifier and value cells remain distinct even when their payloads agree. *)
  Definition mixed_index :=
    RuntimeIndex.insert [Id 2; Val 3]
      (RuntimeIndex.insert [Val 2; Id 3] RuntimeIndex.empty).

  (** A tuple of identifier then value is a member. *)
  Example id_then_value_is_member :
    RuntimeIndex.contains [Id 2; Val 3] mixed_index = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A tuple of value then identifier is a member. *)
  Example value_then_id_is_member :
    RuntimeIndex.contains [Val 2; Id 3] mixed_index = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A tuple of two identifiers is not a member. *)
  Example two_ids_is_absent :
    RuntimeIndex.contains [Id 2; Id 3] mixed_index = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The root has two edges, one for each cell kind. *)
  Example root_has_two_cell_edges :
    RuntimeIndex.degree mixed_index 1 = 2%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

End TerminalTests.

Module NodeTests.

  Local Open Scope positive_scope.

  (** Node identifiers beyond the counter give no child. *)
  Example unallocated_child_is_none :
    RuntimeIndex.child shared_index 4096 (Val 2) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Node identifiers beyond the counter have no children. *)
  Example unallocated_node_has_no_children :
    RuntimeIndex.children shared_index 4096 = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Node identifiers beyond the counter have no edges. *)
  Example unallocated_node_has_no_edges :
    RuntimeIndex.degree shared_index 4096 = 0%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A node with no edges but a nonzero cached degree is kept by a write. *)
  Definition degree_only_node : index_node (cell IndexFixtureValue.t) :=
    IndexNode PTrieCode.empty 5%N false.

  (** Writing and reading back the node with a nonzero cached degree gives the node. *)
  Example cached_degree_keeps_empty_node :
    RuntimeIndex.read_node
      (RuntimeIndex.write_node RuntimeIndex.empty 1 degree_only_node 1) 1 = degree_only_node.
  Proof.
    vm_compute. reflexivity.
  Qed.

End NodeTests.
