(** * Prepared graph observations

    The reference preparer materialises both directions and dense entry IDs.
    For example, the empty graph still has positive fuel two.
    Builds on: GraphPrepared and GraphModelTest. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared.
From Galois.Tests.Graph Require Import GraphModelTest.
Import List.ListNotations.
Open Scope positive_scope.

Definition prepared_diamond := Prepared.prepare positive_encoding diamond.
Definition prepared_loop := Prepared.prepare positive_encoding self_loop.
Definition prepared_two := Prepared.prepare positive_encoding two_entry.
Definition prepared_empty := Prepared.prepare positive_encoding empty.

Example diamond_succ :
  Prepared.succ_edges prepared_diamond 1 = [((1, 2), 2); ((1, 3), 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_pred :
  Prepared.pred_edges prepared_diamond 4 = [((2, 4), 2); ((3, 4), 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_fuel : Prepared.fuel prepared_diamond = 14.
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_indexes :
  (Prepared.succ_edges prepared_loop 1, Prepared.pred_edges prepared_loop 1,
    Prepared.fuel prepared_loop) = ([((1, 1), 1)], [((1, 1), 1)], 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entries :
  (Prepared.entry_ids prepared_two, Prepared.succ_edges prepared_two 3,
    Prepared.pred_edges prepared_two 3, Prepared.fuel prepared_two) =
  ([1; 3], [((3, 4), 4)], [((1, 3), 1)], 14).
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_indexes :
  (Prepared.succ_edges prepared_empty 1, Prepared.pred_edges prepared_empty 1,
    Prepared.fuel prepared_empty) = ([], [], 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example absent_name : Prepared.id_of prepared_diamond 9 = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example absent_id :
  (Prepared.name_of prepared_diamond 9, Prepared.succ_edges prepared_diamond 9) = (None, []).
Proof.
  vm_compute. reflexivity.
Qed.

Example non_dense_client_names :
  let p := Prepared.prepare positive_encoding (fixture [40] [40; 10] [(40, 10)]) in
  (Prepared.id_of p 10, Prepared.name_of p 1, Prepared.succ_edges p 1, Prepared.fuel p) =
    (Some 2, Some 40, [((40, 10), 2)], 7).
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_ready : Prepared.ready prepared_diamond.
Proof.
  apply Prepared.prepare_ready; [exact positive_encoding_laws|exact diamond_wf|].
  exact diamond_out_nodup.
Qed.

Example reversed_indexes :
  Prepared.succ_edges (Prepared.reverse prepared_diamond [4]) 4 =
    [((2, 4), 2); ((3, 4), 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example reversed_endpoints :
  (Graph.entries (Prepared.graph (Prepared.reverse prepared_diamond [4])),
    Graph.source (Prepared.graph (Prepared.reverse prepared_diamond [4])) (2, 4),
    Graph.target (Prepared.graph (Prepared.reverse prepared_diamond [4])) (2, 4),
    Prepared.fuel (Prepared.reverse prepared_diamond [4])) = ([4], 4, 2, 14).
Proof.
  vm_compute. reflexivity.
Qed.

Example reversed_missing_exit :
  Graph.entries (Prepared.graph (Prepared.reverse prepared_diamond [9])) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example reversed_ready : Prepared.ready (Prepared.reverse prepared_diamond [4]).
Proof.
  apply Prepared.reverse_ready; [exact diamond_ready|].
  intros i [<-|Hfalse]; [|contradiction].
  exists 4. split; vm_compute; auto.
Qed.
