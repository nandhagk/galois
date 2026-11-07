(** * Collection differential fixtures

    Valid new collections preserve the legacy observations on the same finite samples.
    For example, every pair of the eight three-key sets is compared in both orders.
    Builds on: LatticeSet, LatticeEnv, OrderPowerset and OrderPointwise. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseSet BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeSet LatticeEnv LatticeSimple.
From GaloisLegacy.Collections Require CollectionsEncoding CollectionsFinSet CollectionsMap.
From GaloisLegacy.Order Require OrderLattice OrderBasic OrderPowerset OrderPointwise.
Import List.ListNotations.

Definition matrix {X Y} (f : X -> X -> Y) xs :=
  List.map (fun x => List.map (f x) xs) xs.

Definition set_samples : list (list positive) :=
  [[]; [1]; [2]; [3]; [1; 2]; [1; 3]; [2; 3]; [1; 2; 3]]%positive.

Definition new_set_observe xs ys :=
  let L := may positive_encoding in
  let a := set_of_list positive_encoding xs in
  let b := set_of_list positive_encoding ys in
  (leb L a b, FinSet.elements (set_raw (join L a b)),
    FinSet.elements (set_raw (widen L a b)), FinSet.elements (set_raw (narrow L a b))).

Definition old_set_observe xs ys :=
  let E := CollectionsEncoding.positive_encoding in
  let L := OrderPowerset.powerset_lattice E in
  let a := CollectionsFinSet.FinSet.of_list E xs in
  let b := CollectionsFinSet.FinSet.of_list E ys in
  (OrderLattice.leb L a b, CollectionsFinSet.FinSet.elements (OrderLattice.join L a b),
    CollectionsFinSet.FinSet.elements (OrderLattice.widen L a b),
    CollectionsFinSet.FinSet.elements (OrderLattice.narrow L a b)).

Example may_all_sampled_pairs :
  matrix new_set_observe set_samples = matrix old_set_observe set_samples.
Proof.
  vm_compute. reflexivity.
Qed.

Definition must_samples := None :: List.map (@Some (list positive)) set_samples.
Definition new_must_value xs :=
  match xs with
  | None => All
  | Some xs => Only (set_of_list positive_encoding xs)
  end.
Definition old_must_value xs :=
  match xs with
  | None => OrderPowerset.All
  | Some xs => OrderPowerset.Only
      (CollectionsFinSet.FinSet.of_list CollectionsEncoding.positive_encoding xs)
  end.
Definition new_must_keys (s : must_t positive_encoding) :=
  match s with
  | All => None
  | Only s => Some (FinSet.elements (set_raw s))
  end.
Definition old_must_keys (s : OrderPowerset.must positive) :=
  match s with
  | OrderPowerset.All => None
  | OrderPowerset.Only s => Some (CollectionsFinSet.FinSet.elements s)
  end.
Definition new_must_observe xs ys :=
  let L := must positive_encoding in
  let a := new_must_value xs in let b := new_must_value ys in
  (leb L a b, new_must_keys (join L a b), new_must_keys (widen L a b),
    new_must_keys (narrow L a b)).
Definition old_must_observe xs ys :=
  let L := OrderPowerset.must_lattice CollectionsEncoding.positive_encoding in
  let a := old_must_value xs in let b := old_must_value ys in
  (OrderLattice.leb L a b, old_must_keys (OrderLattice.join L a b),
    old_must_keys (OrderLattice.widen L a b), old_must_keys (OrderLattice.narrow L a b)).

Example must_all_sampled_pairs :
  matrix new_must_observe must_samples = matrix old_must_observe must_samples.
Proof.
  vm_compute. reflexivity.
Qed.

Definition map_samples : list (list (positive * bool)) :=
  [[]; [(1, true)]; [(1, false)]; [(2, true)]; [(3, false)];
    [(1, true); (2, false)]; [(1, false); (2, true); (3, false)]]%positive.
Definition new_env_observe xs ys :=
  let L := env Bottom_default positive_encoding bool_lattice bool_top in
  let a := env_of_list positive_encoding xs in let b := env_of_list positive_encoding ys in
  (leb L a b, Map.elements (env_raw (join L a b)),
    Map.elements (env_raw (widen L a b)), Map.elements (env_raw (narrow L a b))).
Definition old_env_observe xs ys :=
  let E := CollectionsEncoding.positive_encoding in
  let L := OrderPointwise.pointwise_lattice E OrderBasic.bool_lattice in
  let a := CollectionsMap.Map.of_list E xs in let b := CollectionsMap.Map.of_list E ys in
  (OrderLattice.leb L a b, CollectionsMap.Map.elements (OrderLattice.join L a b),
    CollectionsMap.Map.elements (OrderLattice.widen L a b),
    CollectionsMap.Map.elements (OrderLattice.narrow L a b)).

Example bottom_default_all_sampled_pairs :
  matrix new_env_observe map_samples = matrix old_env_observe map_samples.
Proof.
  vm_compute. reflexivity.
Qed.

Definition top_samples := None :: List.map (@Some (list (positive * bool))) map_samples.
Definition new_top_observe xs ys :=
  let L := env Top_default positive_encoding bool_lattice bool_top in
  let a := option_map (env_of_list positive_encoding) xs in
  let b := option_map (env_of_list positive_encoding) ys in
  let keys := option_map (fun m => Map.elements (env_raw m)) in
  (leb L a b, keys (join L a b), keys (widen L a b), keys (narrow L a b)).
Definition old_top_observe xs ys :=
  let E := CollectionsEncoding.positive_encoding in
  let L := OrderPointwise.pointwise_top_lattice E OrderBasic.bool_lattice OrderBasic.bool_top in
  let a := option_map (CollectionsMap.Map.of_list E) xs in
  let b := option_map (CollectionsMap.Map.of_list E) ys in
  let keys := option_map (@CollectionsMap.Map.elements positive bool) in
  (OrderLattice.leb L a b, keys (OrderLattice.join L a b), keys (OrderLattice.widen L a b),
    keys (OrderLattice.narrow L a b)).

Example top_default_all_sampled_pairs :
  matrix new_top_observe top_samples = matrix old_top_observe top_samples.
Proof.
  vm_compute. reflexivity.
Qed.
