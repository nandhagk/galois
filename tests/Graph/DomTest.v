(** * Dominator certificate observations

    These cases retain parent-map observations and supply independent low-high orders.
    For example, the diamond places its join between its two incoming branches.
    Builds on: graph fixtures, preparation and the dominator code tower. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Dom.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition parent_map (pairs : list (positive * positive)) : ptrie positive :=
  fold_right (fun pair acc => PTrieCode.set (fst pair) (snd pair) acc) Empty pairs.

Example accepts_line :
  DomCode.check (DigraphCode.prepare Line.graph) 1 (parent_map Line.parents) [1; 2; 3; 4] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_diamond :
  DomCode.check (DigraphCode.prepare Diamond.graph) 1
    (parent_map Diamond.parents) [1; 2; 4; 3] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_line_parent :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map [(2, 1); (3, 1); (4, 3)]) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_parent_cycle :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map [(2, 3); (3, 2); (4, 3)]) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_missing_binding :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map [(2, 1); (4, 3)]) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unknown_child :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (PTrieCode.set 9 1 (parent_map Line.parents)) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_order_without_high_witness :
  DomCode.check (DigraphCode.prepare Diamond.graph) 1
    (parent_map Diamond.parents) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_duplicate_order_entry :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map Line.parents) [1; 2; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example ancestor_queries :
  let t := DomCode.tree (DigraphCode.prepare Line.graph) 1
    (parent_map Line.parents) [1; 2; 3; 4] in
  (DomCode.dominates_b t 1 4, DomCode.dominates_b t 2 4,
    DomCode.dominates_b t 4 1, DomCode.dominates_b t 9 4) =
    (true, true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.
