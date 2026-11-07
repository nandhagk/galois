(** * Search differential fixtures

    New search orders and entry ranks are compared with the legacy explicit-stack DFS.
    For example, the thirty-node chain exercises more than a small binary fuel block.
    Builds on: GraphSearch and the legacy GraphDfs. *)

From Stdlib Require Import List Bool Arith PArith.
From GaloisLegacy.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From GaloisLegacy.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch.
Import List.ListNotations.
Local Open Scope nat_scope.

Module SearchDifferential.

Definition new_graph roots nodes (edges : list (nat * nat)) :=
  GraphModel.Graph.of_pure roots nodes
    (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition old_graph roots nodes (edges : list (nat * nat)) :=
  GraphCore.Graph.Make roots nodes
    (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition agrees roots nodes edges :=
  let p := Prepared.prepare BaseEncoding.nat_encoding (new_graph roots nodes edges) in
  let oldp := GraphPrepare.prepare CollectionsEncoding.nat_encoding (old_graph roots nodes edges) in
  let old := GraphDfs.dfs oldp CollectionsFinSet.FinSet.empty roots in
  let fresh := SearchRun.dfs p (Scope.Make BaseSet.FinSet.empty None) (Prepared.entry_ids p) in
  (Prepared.present (Prepared.name_of p) (Search.preorder fresh),
    Prepared.present (Prepared.name_of p) (Search.postorder fresh),
    map (fun v =>
      match Prepared.id_of p v with
      | None => None
      | Some i => BaseMap.Map.get BaseEncoding.positive_encoding i (Search.pre_num fresh)
      end) nodes) =
  (GraphDfs.preorder old, GraphDfs.postorder old,
    map (fun v => CollectionsMap.Map.get CollectionsEncoding.nat_encoding v
      (GraphDfs.pre_num old)) nodes).

Example legacy_single : agrees [1] [1] [].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_self_loop : agrees [1] [1] [(1, 1)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_diamond : agrees [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_two_roots : agrees [3; 1; 3] [1; 2; 3; 4] [(1, 2); (3, 4)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_cycle : agrees [1] [1; 2; 3] [(1, 2); (2, 3); (3, 1)].
Proof.
  vm_compute. reflexivity.
Qed.

Example legacy_thirty_nodes :
  agrees [1] (seq 1 30) (map (fun n => (n, S n)) (seq 1 29)).
Proof.
  vm_compute. reflexivity.
Qed.

End SearchDifferential.
