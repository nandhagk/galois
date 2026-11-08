(** * Witnessed component-entry clients

    These clients discharge entry-index duties on the actual Tarjan partition.
    For example, the irreducible component uses the real edge from entry 1 to header 2.
    Builds on: GraphHierEntries and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSccSpec GraphHierSpec
  GraphHier GraphHierEntries GraphTarjan GraphTarjanExact GraphFixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition unrestricted := Scope.Make FinSet.empty None.
Definition irreducible_components :=
  Tarjan.compute Fixtures.Irreducible.prepared unrestricted [1].

Example actual_irreducible_entry_row :
  Map.get positive_encoding 1
    (HierRun.entries Fixtures.Irreducible.prepared [1] irreducible_components) = Some 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_irreducible_header_is_entry :
  Hier.entry Fixtures.Irreducible.prepared unrestricted [1] [3; 2] 2.
Proof.
  pose proof (HierEntries.entries_correct Fixtures.Irreducible.prepared unrestricted [1]
    irreducible_components Fixtures.Irreducible.fixture_ready
    (TarjanExact.compute_exact _ _ _ Fixtures.Irreducible.fixture_ready)) as Hindex.
  pose proof (HierEntries.rows _ _ _ _ _ Hindex 1 2 actual_irreducible_entry_row) as Hcandidate.
  apply (proj2 Hcandidate [3; 2]). vm_compute. reflexivity.
Qed.

Example actual_nested_root_entry_row :
  let r := Tarjan.compute Fixtures.NestedLoop.prepared unrestricted [1] in
  Map.get positive_encoding 1 (HierRun.entries Fixtures.NestedLoop.prepared [1] r) = Some 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example preferred_header_selection :
  exists body, HierRun.select (Some 2) [3; 2] = Some (2, body).
Proof.
  apply HierRun.select_preferred. right. now left.
Qed.

Example actual_irreducible_selection_client :
  exists i h body,
    Map.get positive_encoding 3 (Scc.comp_of irreducible_components) = Some i /\
    Map.get positive_encoding i
      (HierRun.entries Fixtures.Irreducible.prepared [1] irreducible_components) = Some h /\
    HierRun.select (Some h) [3; 2] = Some (h, body) /\
    Hier.entry Fixtures.Irreducible.prepared unrestricted [1] [3; 2] h.
Proof.
  apply (HierEntries.selection_entry Fixtures.Irreducible.prepared unrestricted [1]
    irreducible_components [3; 2] 3 Fixtures.Irreducible.fixture_ready
    (TarjanExact.compute_exact _ _ _ Fixtures.Irreducible.fixture_ready)).
  - vm_compute. now left.
  - now left.
Qed.
