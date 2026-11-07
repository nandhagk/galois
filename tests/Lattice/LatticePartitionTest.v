(** * Equality partition fixtures

    Four-key fixtures distinguish unreachable states, discrete partitions and equality intersection.
    For example, intersecting [1 = 2 = 3] with [1 = 2] loses [2 = 3].
    Builds on: LatticePartition and BaseUnionFind. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseUnionFind.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticePartition.
Import List.ListNotations.
Open Scope positive_scope.

Definition partition_fixture (xs : list (positive * positive)) : partition_t positive_encoding :=
  Some (exist _ (UnionFind.of_unions positive_encoding xs)
    (UnionFind.of_unions_wf positive_encoding positive_encoding_laws xs)).

Definition partition_observe (p : partition_t positive_encoding) a b :=
  match p with
  | None => true
  | Some u => fst (UnionFind.equivb positive_encoding a b (proj1_sig u))
  end.

Definition partition_discrete := top_value (partition_top positive_encoding positive_encoding_laws).
Definition partition_three := partition_fixture [(1, 2); (2, 3)].
Definition partition_two := partition_fixture [(1, 2)].
Definition partition_other := partition_fixture [(2, 3); (3, 4)].
Definition partition_fixture_lattice := partition_lattice positive_encoding positive_encoding_laws.

(** The concrete encoding instantiates every total partition weak law. *)
Theorem partition_fixture_laws : lattice_laws partition_fixture_lattice.
Proof.
  apply partition_laws.
Qed.

(** The concrete encoding also instantiates least joins and monotone assignment meanings. *)
Theorem partition_fixture_lub : lub_laws partition_fixture_lattice.
Proof.
  apply partition_lub.
Qed.

(** Assignment meanings are monotone for the four-key fixtures and all other positive keys. *)
Theorem partition_fixture_gamma :
  concretisation_laws partition_fixture_lattice (@partition_gamma positive positive_encoding nat).
Proof.
  apply partition_gamma_laws.
Qed.

(** The concrete partition meaning has empty bottom and full discrete top. *)
Theorem partition_fixture_extremes :
  bottom_empty partition_fixture_lattice (@partition_gamma positive positive_encoding nat) /\
  top_full (partition_top positive_encoding positive_encoding_laws)
    (@partition_gamma positive positive_encoding nat).
Proof.
  split; [apply partition_bot_empty|apply partition_top_full].
Qed.

Example partition_discrete_observations :
  (partition_observe partition_discrete 1 1,
    partition_observe partition_discrete 1 2,
    partition_observe partition_discrete 99 99,
    partition_observe partition_discrete 99 100) = (true, false, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_bottom_cases :
  (leb partition_fixture_lattice None partition_three,
    leb partition_fixture_lattice partition_three None,
    partition_observe (join partition_fixture_lattice None partition_three) 1 3) =
    (true, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_join_loses_equality :
  let joined := join partition_fixture_lattice partition_three partition_two in
  (partition_observe joined 1 2, partition_observe joined 2 3,
    partition_observe joined 3 4) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_join_overlapping_classes :
  let joined := join partition_fixture_lattice partition_three partition_other in
  (partition_observe joined 2 3, partition_observe joined 1 2,
    partition_observe joined 3 4) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_reverse_order :
  (leb partition_fixture_lattice partition_three partition_two,
    leb partition_fixture_lattice partition_two partition_three,
    leb partition_fixture_lattice partition_three partition_discrete) = (true, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_empty_join :
  (partition_observe (join partition_fixture_lattice partition_discrete partition_three) 1 2,
    partition_observe (join partition_fixture_lattice partition_three partition_discrete) 1 2) =
    (false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_empty_cost :
  (Cost.ticks (partition_leb_c positive_encoding None partition_three),
    Cost.ticks (partition_join_c positive_encoding positive_encoding_laws None partition_three),
    Cost.ticks (partition_leb_c positive_encoding partition_discrete partition_discrete)) =
    (1%N, 1%N, 2%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_scan_traversal_ticks :
  Cost.ticks (partition_scan_c positive_encoding [1; 2] UnionFind.make UnionFind.make) = 40%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example partition_reached_universal_is_not_bottom :
  leb (partition_lattice unit_encoding unit_encoding_laws)
    (top_value (partition_top unit_encoding unit_encoding_laws)) None = false.
Proof.
  vm_compute; reflexivity.
Qed.
