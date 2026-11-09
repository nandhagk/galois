(** * Hierarchy projection differential observations

    Actual weak-order tokens and loop table queries are compared with both legacy producers.
    For example, the nested fixture uses the same outer and inner headers in all three projections.
    Builds on: GraphWeakOrder, GraphLoopForest and legacy GraphWto and GraphLoops. *)

From Stdlib Require Import List Arith PArith.
From GaloisLegacy.Collections Require Import CollectionsEncoding CollectionsMap.
From GaloisLegacy.Graph Require Import GraphCore GraphPrepare GraphWto GraphLoops.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphHierSpec GraphWeakOrder
  GraphLoopForest.
Import List.ListNotations.
Local Open Scope nat_scope.

Module HierDifferential.

Definition new_graph roots nodes (edges : list (nat * nat)) :=
  GraphModel.Graph.of_pure roots nodes
    (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition old_graph roots nodes (edges : list (nat * nat)) :=
  GraphCore.Graph.Make roots nodes
    (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition new_token (p : Prepared.t nat (nat * nat)) token : GraphWto.wto_token (option nat) :=
  match token with
  | Wto.WVertex v => GraphWto.WVertex (Prepared.name_of p v)
  | Wto.WOpen h => GraphWto.WOpen (Prepared.name_of p h)
  | Wto.WClose => GraphWto.WClose
  end.

Definition old_token token : GraphWto.wto_token (option nat) :=
  match token with
  | GraphWto.WVertex v => GraphWto.WVertex (Some v)
  | GraphWto.WOpen h => GraphWto.WOpen (Some h)
  | GraphWto.WClose => GraphWto.WClose
  end.

Definition query (p : Prepared.t nat (nat * nat)) (m : BaseMap.Map.t positive positive) v :=
  match Prepared.id_of p v with
  | None => None
  | Some i =>
    match BaseMap.Map.get BaseEncoding.positive_encoding i m with
    | None => None
    | Some h => Prepared.name_of p h
    end
  end.

Definition agrees roots nodes edges :=
  let p := Prepared.prepare BaseEncoding.nat_encoding (new_graph roots nodes edges) in
  let oldp := GraphPrepare.prepare CollectionsEncoding.nat_encoding (old_graph roots nodes edges) in
  let loops := LoopForest.compute p (Prepared.entry_ids p) in
  let oldloops := GraphLoops.loop_forest_of oldp in
  (map (new_token p) (WeakOrder.compute p (Prepared.entry_ids p)),
    map (Prepared.name_of p) (Loops.headers loops),
    map (query p (Loops.loop_parent loops)) nodes,
    map (query p (Loops.innermost loops)) nodes) =
  (map old_token (GraphWto.wto_of oldp),
    map Some (GraphLoops.loop_headers oldloops),
    map (fun v => CollectionsMap.Map.get CollectionsEncoding.nat_encoding v
      (GraphLoops.loop_parent oldloops)) nodes,
    map (fun v => CollectionsMap.Map.get CollectionsEncoding.nat_encoding v
      (GraphLoops.loop_of oldloops)) nodes).

Example legacy_empty : agrees [] [] [].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_self_loop : agrees [1] [1] [(1, 1)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_line : agrees [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_diamond :
  agrees [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_nested :
  agrees [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_irreducible :
  agrees [1] [1; 2; 3] [(1, 2); (1, 3); (2, 3); (3, 2)].
Proof.
  vm_compute. reflexivity.
Qed.

Example separate_component_header_order :
  let roots := [1] in
  let nodes := [1; 2; 3; 4] in
  let edges := [(1, 2); (2, 1); (2, 3); (3, 4); (4, 3)] in
  let p := Prepared.prepare BaseEncoding.nat_encoding (new_graph roots nodes edges) in
  let oldp := GraphPrepare.prepare CollectionsEncoding.nat_encoding (old_graph roots nodes edges) in
  (map (Prepared.name_of p) (Loops.headers (LoopForest.compute p (Prepared.entry_ids p))),
    GraphLoops.loop_headers (GraphLoops.loop_forest_of oldp)) = ([Some 1; Some 3], [3; 1]).
Proof.
  vm_compute. reflexivity.
Qed.

End HierDifferential.
