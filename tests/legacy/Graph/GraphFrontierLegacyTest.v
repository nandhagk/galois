(** * Frontier migration comparisons

    The same labelled graphs exercise new supplied-tree consumers and legacy producers.
    For example, the two-entry fixture compares both virtual-root branches.
    Builds on: the new frontier family and legacy frontier, IDF and control dependence. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphFixtures GraphCheckDom
  GraphFrontierSweep GraphFrontierIdf GraphFrontierControl.
From GaloisLegacy.Collections Require CollectionsEncoding CollectionsMap CollectionsFinSet.
From GaloisLegacy.Graph Require GraphCore GraphPrepare GraphDominators GraphFrontier GraphIdf
  GraphPostDominators GraphControlDependence.
Import List.ListNotations.

Definition legacy_graph roots nodes (edges : list (nat * nat)) :=
  GraphCore.Graph.Make roots nodes (fun v => filter (fun e => Nat.eqb (fst e) v) edges)
    fst snd.

Definition legacy_prepared roots nodes edges :=
  GraphPrepare.prepare CollectionsEncoding.nat_encoding (legacy_graph roots nodes edges).

Definition edge_eq (a b : nat * nat) := Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

Definition new_observations (p : Prepared.t nat (nat * nat)) tree post edges :=
  let df := FrontierSweep.dominance_frontier p tree in
  let idf := FrontierIdf.idf p tree [2] in
  let control := FrontierControl.control_deps p [4]%positive post in
  map (fun n =>
    (map (fun x => FinSet.mem positive_encoding (Pos.of_nat x)
      (Map.find_or positive_encoding FinSet.empty (Pos.of_nat n) df)) [1; 2; 3; 4],
     FinSet.mem positive_encoding (Pos.of_nat n) idf,
     map (fun e => existsb (edge_eq e)
       (Map.find_or positive_encoding [] (Pos.of_nat n) control)) edges)) [1; 2; 3; 4].

Definition old_observations roots edges :=
  let p := legacy_prepared roots [1; 2; 3; 4] edges in
  let tree := GraphDominators.dominator_tree p in
  let post := GraphPostDominators.post_dominator_tree p [4] in
  let df := GraphFrontier.dominance_frontier p tree in
  let idf := GraphIdf.direct_idf p tree [2] in
  let control := GraphControlDependence.control_deps p [4] post in
  map (fun n =>
    (map (fun x => CollectionsFinSet.FinSet.mem CollectionsEncoding.nat_encoding x
      (match CollectionsMap.Map.get CollectionsEncoding.nat_encoding n df with
       | Some row => row
       | None => CollectionsFinSet.FinSet.empty
       end)) [1; 2; 3; 4],
     CollectionsFinSet.FinSet.mem CollectionsEncoding.nat_encoding n idf,
     map (fun e => existsb (edge_eq e)
       (match CollectionsMap.Map.get CollectionsEncoding.nat_encoding n control with
        | Some row => row
        | None => []
        end)) edges)) [1; 2; 3; 4].

Definition line_post_parents := Fixtures.parents [(1, 2); (2, 3); (3, 4)]%positive.
Definition line_post :=
  DomCheck.of_parents (Prepared.reverse Fixtures.Line.prepared [4]%positive) line_post_parents.

Example line_certificates :
  (DomCheck.check Fixtures.Line.prepared Fixtures.Line.parents,
   DomCheck.check (Prepared.reverse Fixtures.Line.prepared [4]%positive) line_post_parents) =
    (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example line_legacy :
  new_observations Fixtures.Line.prepared Fixtures.Line.tree line_post [(1, 2); (2, 3); (3, 4)] =
    old_observations [1] [(1, 2); (2, 3); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition diamond_post_parents := Fixtures.parents [(1, 4); (2, 4); (3, 4)]%positive.
Definition diamond_post :=
  DomCheck.of_parents (Prepared.reverse Fixtures.Diamond.prepared [4]%positive)
    diamond_post_parents.

Example diamond_certificates :
  (DomCheck.check Fixtures.Diamond.prepared Fixtures.Diamond.parents,
   DomCheck.check (Prepared.reverse Fixtures.Diamond.prepared [4]%positive)
     diamond_post_parents) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_legacy :
  new_observations Fixtures.Diamond.prepared Fixtures.Diamond.tree diamond_post
    [(1, 2); (1, 3); (2, 4); (3, 4)] =
    old_observations [1] [(1, 2); (1, 3); (2, 4); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition join_post :=
  DomCheck.of_parents (Prepared.reverse Fixtures.JoinLoop.prepared [4]%positive)
    diamond_post_parents.

Example join_certificates :
  (DomCheck.check Fixtures.JoinLoop.prepared Fixtures.JoinLoop.parents,
   DomCheck.check (Prepared.reverse Fixtures.JoinLoop.prepared [4]%positive)
     diamond_post_parents) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example join_legacy :
  new_observations Fixtures.JoinLoop.prepared Fixtures.JoinLoop.tree join_post
    [(1, 2); (1, 3); (2, 4); (3, 4); (4, 4)] =
    old_observations [1] [(1, 2); (1, 3); (2, 4); (3, 4); (4, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition nested_post :=
  DomCheck.of_parents (Prepared.reverse Fixtures.NestedLoop.prepared [4]%positive)
    line_post_parents.

Example nested_certificates :
  (DomCheck.check Fixtures.NestedLoop.prepared Fixtures.NestedLoop.parents,
   DomCheck.check (Prepared.reverse Fixtures.NestedLoop.prepared [4]%positive)
     line_post_parents) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_legacy :
  new_observations Fixtures.NestedLoop.prepared Fixtures.NestedLoop.tree nested_post
    [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)] =
    old_observations [1] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition two_post_parents := Fixtures.parents [(1, 3); (2, 3); (3, 4)]%positive.
Definition two_post :=
  DomCheck.of_parents (Prepared.reverse Fixtures.TwoEntry.prepared [4]%positive) two_post_parents.

Example two_entry_certificates :
  (DomCheck.check Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents,
   DomCheck.check (Prepared.reverse Fixtures.TwoEntry.prepared [4]%positive) two_post_parents) =
    (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_legacy :
  new_observations Fixtures.TwoEntry.prepared Fixtures.TwoEntry.tree two_post
    [(1, 3); (2, 3); (3, 4)] = old_observations [1; 2] [(1, 3); (2, 3); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.
