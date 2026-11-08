(** * Tarjan differential observations

    New components, member order and one-based owners are compared with the legacy producer.
    For example, nested cycles retain the legacy maximal component rather than a hierarchy.
    Builds on: GraphTarjan and the legacy GraphScc. *)

From Stdlib Require Import List Bool Arith PArith.
From GaloisLegacy.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From GaloisLegacy.Graph Require Import GraphCore GraphPrepare GraphScc.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSccSpec GraphTarjan.
Import List.ListNotations.

Module TarjanDifferential.
Local Open Scope nat_scope.

Definition new_graph nodes (edges : list (nat * nat)) :=
  GraphModel.Graph.of_pure nodes nodes
    (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition old_graph nodes (edges : list (nat * nat)) :=
  GraphCore.Graph.Make nodes nodes
    (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition agrees nodes edges :=
  let p := Prepared.prepare BaseEncoding.nat_encoding (new_graph nodes edges) in
  let oldp := GraphPrepare.prepare CollectionsEncoding.nat_encoding (old_graph nodes edges) in
  let old := GraphScc.scc oldp in
  let fresh := Tarjan.compute p (Scope.Make BaseSet.FinSet.empty None) (Prepared.entry_ids p) in
  (map (Prepared.present (Prepared.name_of p)) (Scc.components fresh),
    map (fun v =>
      match Prepared.id_of p v with
      | None => None
      | Some i => BaseMap.Map.get BaseEncoding.positive_encoding i (Scc.comp_of fresh)
      end) nodes) =
  (GraphScc.components old,
    map (fun v => CollectionsMap.Map.get CollectionsEncoding.nat_encoding v
      (GraphScc.comp_of old)) nodes).

Example legacy_empty : agrees [] [].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_self_loop : agrees [1] [(1, 1)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_line : agrees [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_diamond : agrees [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_nested : agrees [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_irreducible : agrees [1; 2; 3] [(1, 2); (1, 3); (2, 3); (3, 2)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_distinct : agrees [1; 2; 3; 4] [(1, 2); (2, 1); (2, 3); (3, 4); (4, 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_nonidentity_interning :
  agrees [40; 10; 90] [(40, 10); (10, 90); (90, 10)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_cross_to_finished_pending_sibling :
  agrees [1; 2; 3] [(1, 2); (1, 3); (2, 1); (3, 2)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition agrees_within nodes edges region :=
  let p := Prepared.prepare BaseEncoding.nat_encoding (new_graph nodes edges) in
  let oldp := GraphPrepare.prepare CollectionsEncoding.nat_encoding (old_graph nodes edges) in
  let old := GraphScc.scc_within oldp region in
  let ids := Prepared.present (Prepared.id_of p) region in
  let fresh := Tarjan.compute p
    (Scope.Make BaseSet.FinSet.empty (Some (BaseSet.FinSet.of_list
      BaseEncoding.positive_encoding ids))) ids in
  (map (Prepared.present (Prepared.name_of p)) (Scc.components fresh),
    map (fun v => match Prepared.id_of p v with
      | None => None
      | Some i => BaseMap.Map.get BaseEncoding.positive_encoding i (Scc.comp_of fresh)
      end) nodes) =
  (GraphScc.components old,
    map (fun v => CollectionsMap.Map.get CollectionsEncoding.nat_encoding v
      (GraphScc.comp_of old)) nodes).

Example legacy_scoped_nested :
  agrees_within [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)] [2; 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_scoped_distinct :
  agrees_within [1; 2; 3; 4] [(1, 2); (2, 1); (2, 3); (3, 4); (4, 3)] [3; 4].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_scoped_nonidentity :
  agrees_within [40; 10; 90] [(40, 10); (10, 90); (90, 10)] [10; 90].
Proof.
  vm_compute. reflexivity.
Qed.

End TarjanDifferential.
