(** * Hand-written dominator certificates

    Every parent map is tested independently of a dominator producer.
    For example, the two-entry join has no immediate dominator.
    Builds on: GraphFixtures and GraphCheckDom. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphFixtures GraphCheckDom.
Import List.ListNotations.
Open Scope positive_scope.

Example accepts_line : Dom.check Fixtures.Line.prepared Fixtures.Line.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_diamond : Dom.check Fixtures.Diamond.prepared Fixtures.Diamond.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_join_loop : Dom.check Fixtures.JoinLoop.prepared Fixtures.JoinLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_nested_loop :
  Dom.check Fixtures.NestedLoop.prepared Fixtures.NestedLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_two_entries : Dom.check Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_self_loop : Dom.check Fixtures.SelfLoop.prepared Fixtures.SelfLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_irreducible :
  Dom.check Fixtures.Irreducible.prepared Fixtures.Irreducible.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_empty : Dom.check Fixtures.Empty.prepared Fixtures.Empty.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_singleton : Dom.check Fixtures.Singleton.prepared Fixtures.Singleton.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_unreachable :
  Dom.check Fixtures.Unreachable.prepared Fixtures.Unreachable.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_line_parent :
  Dom.check Fixtures.Line.prepared (Fixtures.parents [(2, 1); (3, 1); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_diamond_parent :
  Dom.check Fixtures.Diamond.prepared (Fixtures.parents [(2, 1); (3, 1); (4, 2)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_join_loop_parent :
  Dom.check Fixtures.JoinLoop.prepared (Fixtures.parents [(2, 1); (3, 1); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_nested_loop_parent :
  Dom.check Fixtures.NestedLoop.prepared (Fixtures.parents [(2, 1); (3, 2); (4, 2)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_parent_at_two_entry_join :
  Dom.check Fixtures.TwoEntry.prepared (Fixtures.parents [(3, 1); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_parent_at_self_loop_root :
  Dom.check Fixtures.SelfLoop.prepared (Fixtures.parents [(1, 1)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_irreducible_parent :
  Dom.check Fixtures.Irreducible.prepared (Fixtures.parents [(2, 3); (3, 1)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_binding_on_empty :
  Dom.check Fixtures.Empty.prepared (Fixtures.parents [(1, 1)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_singleton_parent :
  Dom.check Fixtures.Singleton.prepared (Fixtures.parents [(1, 1)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_parent_cycle :
  Dom.check Fixtures.Line.prepared (Fixtures.parents [(2, 3); (3, 2); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_missing_binding :
  Dom.check Fixtures.Line.prepared (Fixtures.parents [(2, 1); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unreachable_binding :
  Dom.check Fixtures.Unreachable.prepared
    (Map.set positive_encoding 5 1 Fixtures.Unreachable.parents) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unknown_child :
  Dom.check Fixtures.Line.prepared (Map.set positive_encoding 9 1 Fixtures.Line.parents) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unknown_parent :
  Dom.check Fixtures.Line.prepared (Map.set positive_encoding 2 9 Fixtures.Line.parents) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example ancestor_walks :
  (Dom.ancestor_b Fixtures.Line.parents 1 4, Dom.ancestor_b Fixtures.Line.parents 2 4,
    Dom.ancestor_b Fixtures.Line.parents 4 1, Dom.ancestor_b Fixtures.Line.parents 9 4) =
  (true, true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example cyclic_chain_does_not_end :
  Dom.ends 4 (Fixtures.parents [(2, 3); (3, 2)]) 2 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example missing_parent_ends_chain :
  Dom.ends 1 Fixtures.Empty.parents 9 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example exhausted_chain_budget :
  Dom.ends 0 Fixtures.Singleton.parents 1 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example preserves_parent_map :
  Dom.idom (Dom.of_parents Fixtures.Line.prepared Fixtures.Line.parents) = Fixtures.Line.parents.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_intervals :
  let t := Dom.of_parents Fixtures.Line.prepared Fixtures.Line.parents in
  (Dom.dominates_b t 1 4, Dom.dominates_b t 2 4, Dom.dominates_b t 4 1) = (true, true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_interval_rejects_arm :
  let t := Dom.of_parents Fixtures.Diamond.prepared Fixtures.Diamond.parents in
  (Dom.dominates_b t 1 4, Dom.dominates_b t 2 4) = (true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_intervals :
  let t := Dom.of_parents Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents in
  (Dom.dominates_b t 1 3, Dom.dominates_b t 2 3, Dom.dominates_b t 3 4) =
  (false, false, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_interval_rejected :
  Dom.dominates_b (Dom.of_parents Fixtures.Line.prepared Fixtures.Line.parents) 9 9 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example unreachable_interval_rejected :
  Dom.dominates_b (Dom.of_parents Fixtures.Unreachable.prepared Fixtures.Unreachable.parents) 5 5 =
  false.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_interval_rejected :
  Dom.dominates_b (Dom.of_parents Fixtures.Empty.prepared Fixtures.Empty.parents) 1 1 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example certifies_hand_written_line :
  Dom.exact Fixtures.Line.prepared
    (Dom.of_parents Fixtures.Line.prepared Fixtures.Line.parents).
Proof.
  apply Dom.check_sound; [exact Fixtures.Line.fixture_ready|exact Fixtures.Line.parents_wf|].
  vm_compute. reflexivity.
Qed.

Example accepts_exact_two_entry_witness :
  Dom.check Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents = true.
Proof.
  apply Dom.check_complete; [exact Fixtures.TwoEntry.fixture_ready|].
  exists Fixtures.TwoEntry.tree. split; [exact Fixtures.TwoEntry.tree_exact|].
  apply Dom.of_parents_idom.
Qed.
