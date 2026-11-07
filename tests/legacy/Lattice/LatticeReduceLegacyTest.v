(** * Differential reduced products and equality partitions

    New and legacy observations agree on boolean pairs and sampled four-key partitions.
    For example, forgetting a middle key retains the equality of its former classmates.
    Builds on: LatticeReduced, LatticePartitionOps, OrderReduced and DomainsEquality. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseUnionFind.
From Galois.Lattice Require Import LatticeCore LatticeKit LatticeSimple LatticeReduced
  LatticePartition LatticePartitionOps.
From GaloisLegacy.Collections Require CollectionsEncoding CollectionsUnionFind.
From GaloisLegacy.Order Require OrderLattice OrderBasic OrderReduced.
From GaloisLegacy.Domains Require DomainsEquality.
Import List.ListNotations.
Open Scope positive_scope.

Definition legacy_partition_samples : list (option (list (positive * positive))) :=
  [None; Some []; Some [(1, 2)]; Some [(2, 3)]; Some [(1, 2); (2, 3)];
    Some [(1, 2); (3, 4)]; Some [(2, 3); (3, 4)]; Some [(1, 2); (2, 3); (3, 4)]]%positive.

Definition new_partition_sample (xs : option (list (positive * positive))) :=
  option_map (fun pairs => exist _
    (UnionFind.of_unions positive_encoding pairs)
    (UnionFind.of_unions_wf positive_encoding positive_encoding_laws pairs)) xs.

Definition old_partition_sample (xs : option (list (positive * positive))) :=
  option_map (fun pairs => exist _
    (CollectionsUnionFind.UnionFind.of_unions CollectionsEncoding.positive_encoding pairs)
    (CollectionsUnionFind.UnionFind.of_unions_wf CollectionsEncoding.positive_encoding pairs)) xs.

Definition legacy_partition_keys := [1; 2; 3; 4; 99]%positive.

Definition new_partition_observations p :=
  flat_map (fun a => map (fun b =>
    fst (partition_test positive_encoding positive_encoding_laws a b p)) legacy_partition_keys)
    legacy_partition_keys.

Definition old_partition_observations p :=
  flat_map (fun a => map (fun b =>
    fst (DomainsEquality.partition_test CollectionsEncoding.positive_encoding a b p))
    legacy_partition_keys) legacy_partition_keys.

Definition new_partition_updates xs :=
  let p := new_partition_sample xs in
  (new_partition_observations p,
    new_partition_observations (partition_union positive_encoding positive_encoding_laws 1 4 p),
    map (fun x => new_partition_observations
      (partition_forget positive_encoding positive_encoding_laws x p)) legacy_partition_keys).

Definition old_partition_updates xs :=
  let p := old_partition_sample xs in
  (old_partition_observations p,
    old_partition_observations
      (DomainsEquality.partition_union CollectionsEncoding.positive_encoding 1 4 p),
    map (fun x => old_partition_observations
      (DomainsEquality.partition_forget CollectionsEncoding.positive_encoding x p))
      legacy_partition_keys).

Example partition_updates_legacy :
  map new_partition_updates legacy_partition_samples =
    map old_partition_updates legacy_partition_samples.
Proof.
  vm_compute; reflexivity.
Qed.

Definition new_partition_pair xs ys :=
  let p := new_partition_sample xs in
  let q := new_partition_sample ys in
  let L := partition_lattice positive_encoding positive_encoding_laws in
  (leb L p q, new_partition_observations (join L p q),
    new_partition_observations (widen L p q), new_partition_observations (narrow L p q)).

Definition old_partition_pair xs ys :=
  let p := old_partition_sample xs in
  let q := old_partition_sample ys in
  let L := DomainsEquality.partition_lattice CollectionsEncoding.positive_encoding in
  (OrderLattice.leb L p q, old_partition_observations (OrderLattice.join L p q),
    old_partition_observations (OrderLattice.widen L p q),
    old_partition_observations (OrderLattice.narrow L p q)).

Example partition_lattice_legacy :
  map (fun xs => map (new_partition_pair xs) legacy_partition_samples) legacy_partition_samples =
    map (fun xs => map (old_partition_pair xs) legacy_partition_samples) legacy_partition_samples.
Proof.
  vm_compute; reflexivity.
Qed.

Close Scope positive_scope.

Definition legacy_reduce_pair : lattice (bool * bool) :=
  simple (fun x y => implb (fst x) (fst y) && implb (snd x) (snd y))
    (false, false) (fun x y => (fst x || fst y, snd x || snd y)).

(** The differential fixture passes exact slots of its plain local product. *)
Theorem legacy_reduce_slots :
  slots2 legacy_reduce_pair bool_lattice bool_lattice fst snd.
Proof.
  constructor.
  - intros [a b] [c d]; destruct a, b, c, d; vm_compute; tauto.
  - split; reflexivity.
  - intros; split; reflexivity.
  - intros; split; reflexivity.
  - intros; split; reflexivity.
Qed.

Definition legacy_reducer : reducer bool bool :=
  {| step_c := fun a b => Cost.ret (a, a && b); rounds_c := fun _ => Cost.ret 1 |}.

Definition new_reduced := reduced legacy_reduce_pair legacy_reduce_slots legacy_reducer.
Definition old_reduced :=
  OrderReduced.reduced_lattice OrderBasic.bool_lattice OrderBasic.bool_lattice
    (fun x => (fst x, fst x && snd x)).
Definition legacy_reduce_values := [(false, false); (false, true); (true, false); (true, true)].

Definition new_reduced_observations x y :=
  (leb new_reduced x y, join new_reduced x y,
    widen new_reduced x y, narrow new_reduced x y).
Definition old_reduced_observations x y :=
  (OrderLattice.leb old_reduced x y, OrderLattice.join old_reduced x y,
    OrderLattice.widen old_reduced x y, OrderLattice.narrow old_reduced x y).

Example reducer_operations_legacy :
  map (fun x => map (new_reduced_observations x) legacy_reduce_values) legacy_reduce_values =
    map (fun x => map (old_reduced_observations x) legacy_reduce_values) legacy_reduce_values.
Proof.
  vm_compute; reflexivity.
Qed.
