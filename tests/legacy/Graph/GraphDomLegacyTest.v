(** * Dominator parent migration comparisons

    Both ranked finishers are compared with the legacy dominator producer through node names.
    For example, the multi-entry join has no parent in either producer.
    Builds on: GraphDomBackend and legacy GraphDominators. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphFixtures GraphDomBackend.
From GaloisLegacy.Collections Require CollectionsEncoding CollectionsMap.
From GaloisLegacy.Graph Require GraphCore GraphPrepare GraphDominators.
Import List.ListNotations.

Definition old_graph roots nodes (edges : list (nat * nat)) :=
  GraphCore.Graph.Make roots nodes (fun v => filter (fun e => Nat.eqb (fst e) v) edges)
    fst snd.

Definition old_parents roots nodes edges :=
  GraphDominators.idom
    (GraphDominators.dominator_tree
      (GraphPrepare.prepare CollectionsEncoding.nat_encoding (old_graph roots nodes edges))).

Definition named_parents b (p : Prepared.t nat (nat * nat)) nodes :=
  let parents := DomBackend.parents b p in
  map (fun n =>
    match Prepared.id_of p n with
    | None => None
    | Some v =>
      match Map.get positive_encoding v parents with
      | None => None
      | Some u => Prepared.name_of p u
      end
    end) nodes.

Definition new_pair roots nodes edges :=
  let p := Fixtures.prepare roots nodes edges in
  (named_parents DomBackend.lt p nodes, named_parents DomBackend.semi_nca p nodes).

Definition old_pair roots nodes edges :=
  let observations :=
    map (fun n => CollectionsMap.Map.get CollectionsEncoding.nat_encoding n
      (old_parents roots nodes edges)) nodes in
  (observations, observations).

Example line_legacy_idom :
  new_pair [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)] =
    old_pair [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_legacy_idom :
  new_pair [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)] =
    old_pair [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_legacy_idom :
  new_pair [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4); (4, 4)] =
    old_pair [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4); (4, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example multiple_entry_legacy_idom :
  new_pair [1; 2] [1; 2; 3; 4] [(1, 3); (2, 3); (3, 4)] =
    old_pair [1; 2] [1; 2; 3; 4] [(1, 3); (2, 3); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_legacy_idom : new_pair [] [] [] = old_pair [] [] [].
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_legacy_idom : new_pair [7] [7] [] = old_pair [7] [7] [].
Proof.
  vm_compute. reflexivity.
Qed.

Example unreachable_legacy_idom :
  new_pair [1] [1; 2; 3; 4; 5] [(1, 2); (2, 3); (3, 4); (5, 5)] =
    old_pair [1] [1; 2; 3; 4; 5] [(1, 2); (2, 3); (3, 4); (5, 5)].
Proof.
  vm_compute. reflexivity.
Qed.

Example nonnumeric_order_and_repeated_entries :
  new_pair [40; 40] [40; 10; 70] [(40, 10); (10, 70)] =
    old_pair [40; 40] [40; 10; 70] [(40, 10); (10, 70)].
Proof.
  vm_compute. reflexivity.
Qed.
