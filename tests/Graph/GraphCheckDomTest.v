(** * Hand-written dominator certificates

    Every parent map is tested independently of a dominator producer.
    For example, the two-entry join has no immediate dominator.
    Builds on: GraphFixtures and GraphCheckDom. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphDomSpec GraphFixtures GraphCheckDom.
Import List.ListNotations.
Open Scope positive_scope.

Example accepts_line : DomCheck.check Fixtures.Line.prepared Fixtures.Line.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_diamond : DomCheck.check Fixtures.Diamond.prepared Fixtures.Diamond.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_join_loop :
  DomCheck.check Fixtures.JoinLoop.prepared Fixtures.JoinLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_nested_loop :
  DomCheck.check Fixtures.NestedLoop.prepared Fixtures.NestedLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_two_entries :
  DomCheck.check Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_self_loop :
  DomCheck.check Fixtures.SelfLoop.prepared Fixtures.SelfLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_irreducible :
  DomCheck.check Fixtures.Irreducible.prepared Fixtures.Irreducible.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_empty : DomCheck.check Fixtures.Empty.prepared Fixtures.Empty.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_singleton :
  DomCheck.check Fixtures.Singleton.prepared Fixtures.Singleton.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_unreachable :
  DomCheck.check Fixtures.Unreachable.prepared Fixtures.Unreachable.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_line_parent :
  DomCheck.check Fixtures.Line.prepared (Fixtures.parents [(2, 1); (3, 1); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_diamond_parent :
  DomCheck.check Fixtures.Diamond.prepared (Fixtures.parents [(2, 1); (3, 1); (4, 2)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_join_loop_parent :
  DomCheck.check Fixtures.JoinLoop.prepared (Fixtures.parents [(2, 1); (3, 1); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_nested_loop_parent :
  DomCheck.check Fixtures.NestedLoop.prepared (Fixtures.parents [(2, 1); (3, 2); (4, 2)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_parent_at_two_entry_join :
  DomCheck.check Fixtures.TwoEntry.prepared (Fixtures.parents [(3, 1); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_parent_at_self_loop_root :
  DomCheck.check Fixtures.SelfLoop.prepared (Fixtures.parents [(1, 1)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_irreducible_parent :
  DomCheck.check Fixtures.Irreducible.prepared (Fixtures.parents [(2, 3); (3, 1)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_binding_on_empty :
  DomCheck.check Fixtures.Empty.prepared (Fixtures.parents [(1, 1)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_singleton_parent :
  DomCheck.check Fixtures.Singleton.prepared (Fixtures.parents [(1, 1)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_parent_cycle :
  DomCheck.check Fixtures.Line.prepared (Fixtures.parents [(2, 3); (3, 2); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_missing_binding :
  DomCheck.check Fixtures.Line.prepared (Fixtures.parents [(2, 1); (4, 3)]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unreachable_binding :
  DomCheck.check Fixtures.Unreachable.prepared
    (Map.set positive_encoding 5 1 Fixtures.Unreachable.parents) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unknown_child :
  DomCheck.check Fixtures.Line.prepared
    (Map.set positive_encoding 9 1 Fixtures.Line.parents) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unknown_parent :
  DomCheck.check Fixtures.Line.prepared
    (Map.set positive_encoding 2 9 Fixtures.Line.parents) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example ancestor_walks :
  (DomCheck.ancestor_b Fixtures.Line.parents 1 4, DomCheck.ancestor_b Fixtures.Line.parents 2 4,
    DomCheck.ancestor_b Fixtures.Line.parents 4 1, DomCheck.ancestor_b Fixtures.Line.parents 9 4) =
  (true, true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example cyclic_chain_does_not_end :
  DomCheck.ends 4 (Fixtures.parents [(2, 3); (3, 2)]) 2 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example missing_parent_ends_chain :
  DomCheck.ends 1 Fixtures.Empty.parents 9 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example exhausted_chain_budget :
  DomCheck.ends 0 Fixtures.Singleton.parents 1 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example preserves_parent_map :
  Dom.idom (DomCheck.of_parents Fixtures.Line.prepared Fixtures.Line.parents) =
  Fixtures.Line.parents.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_intervals :
  let t := DomCheck.of_parents Fixtures.Line.prepared Fixtures.Line.parents in
  (DomCheck.dominates_b t 1 4, DomCheck.dominates_b t 2 4, DomCheck.dominates_b t 4 1) =
  (true, true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_interval_rejects_arm :
  let t := DomCheck.of_parents Fixtures.Diamond.prepared Fixtures.Diamond.parents in
  (DomCheck.dominates_b t 1 4, DomCheck.dominates_b t 2 4) = (true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_intervals :
  let t := DomCheck.of_parents Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents in
  (DomCheck.dominates_b t 1 3, DomCheck.dominates_b t 2 3, DomCheck.dominates_b t 3 4) =
  (false, false, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_interval_rejected :
  DomCheck.dominates_b
    (DomCheck.of_parents Fixtures.Line.prepared Fixtures.Line.parents) 9 9 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example unreachable_interval_rejected :
  DomCheck.dominates_b
    (DomCheck.of_parents Fixtures.Unreachable.prepared Fixtures.Unreachable.parents) 5 5 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_interval_rejected :
  DomCheck.dominates_b
    (DomCheck.of_parents Fixtures.Empty.prepared Fixtures.Empty.parents) 1 1 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example certifies_hand_written_line :
  Dom.exact Fixtures.Line.prepared
    (DomCheck.of_parents Fixtures.Line.prepared Fixtures.Line.parents).
Proof.
  apply DomCheck.check_sound; [exact Fixtures.Line.fixture_ready|exact Fixtures.Line.parents_wf|].
  vm_compute. reflexivity.
Qed.

Example accepts_exact_two_entry_witness :
  DomCheck.check Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents = true.
Proof.
  apply DomCheck.check_complete; [exact Fixtures.TwoEntry.fixture_ready|].
  exists Fixtures.TwoEntry.tree. split; [exact Fixtures.TwoEntry.tree_exact|].
  apply DomCheck.of_parents_idom.
Qed.
