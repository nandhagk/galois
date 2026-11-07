(** * Map and set differential fixtures

    New and legacy containers consume identical bindings and probe keys.
    For example, repeated keys retain the final supplied value in both implementations.
    Builds on: BaseMap, BaseSet and legacy CollectionsMap and CollectionsFinSet. *)

From Stdlib Require Import List NArith.
From GaloisLegacy.Collections Require CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
Import List.ListNotations.

Definition bindings := [(3%positive, 30); (2%positive, 20); (1%positive, 10);
  (2%positive, 21)].
Definition keys := [3; 2; 1; 2]%positive.
Definition probes := [1; 2; 3; 4]%positive.
Definition new_map := Map.of_list positive_encoding bindings.
Definition old_map :=
  CollectionsMap.Map.of_list CollectionsEncoding.positive_encoding bindings.
Definition new_set := FinSet.of_list positive_encoding keys.
Definition old_set :=
  CollectionsFinSet.FinSet.of_list CollectionsEncoding.positive_encoding keys.

Example map_probe_agreement :
  List.map (fun k => Map.get positive_encoding k new_map) probes =
  List.map (fun k =>
    CollectionsMap.Map.get CollectionsEncoding.positive_encoding k old_map) probes.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_order_agreement :
  List.map fst (Map.elements new_map) =
  List.map fst (CollectionsMap.Map.elements old_map).
Proof.
  vm_compute. reflexivity.
Qed.

Example set_probe_agreement :
  List.map (fun k => FinSet.mem positive_encoding k new_set) probes =
  List.map (fun k =>
    CollectionsFinSet.FinSet.mem CollectionsEncoding.positive_encoding k old_set) probes.
Proof.
  vm_compute. reflexivity.
Qed.

Example set_order_agreement :
  FinSet.elements new_set = CollectionsFinSet.FinSet.elements old_set.
Proof.
  vm_compute. reflexivity.
Qed.
