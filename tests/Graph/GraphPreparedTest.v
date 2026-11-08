(** * Prepared graph observations

    The reference preparer materialises both directions and dense entry IDs.
    For example, the empty graph still has positive fuel two.
    Builds on: GraphPrepared and GraphModelTest. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
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

(** Successful charged option results retain their actual input witnesses. *)
Example present_membership_client {A B} (f : A -> Cost.t (option B)) xs y :
  In y (Cost.value (Prepared.present_c f xs)) <->
    exists x, In x xs /\ Cost.value (f x) = Some y.
Proof.
  rewrite Prepared.present_c_value.
  apply Prepared.present_spec.
Qed.

Example present_duplicates_and_missing :
  Cost.value (Prepared.present_c
    (fun x : positive => Cost.ret (if Pos.eqb x 2 then None else Some x)) [1; 2; 1]) =
    [1; 1].
Proof.
  vm_compute. reflexivity.
Qed.

(** Charged option maps depend only on pointwise callback values through the public owner laws. *)
Example present_ext_client {A B} (f g : A -> Cost.t (option B)) xs :
  (forall x, Cost.value (f x) = Cost.value (g x)) ->
  Cost.value (Prepared.present_c f xs) = Cost.value (Prepared.present_c g xs).
Proof.
  intro Hvalues. rewrite !Prepared.present_c_value.
  now apply Prepared.present_ext.
Qed.

(** The public owner bounds charged option-map output length without exposing its recursion. *)
Example present_length_client {A B} (f : A -> Cost.t (option B)) xs :
  (length (Cost.value (Prepared.present_c f xs)) <= length xs)%nat.
Proof.
  rewrite Prepared.present_c_value. apply Prepared.present_length.
Qed.

Example present_reject_all :
  Prepared.present (fun _ : positive => @None positive) [1; 2; 1] = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example present_empty :
  Prepared.present (fun x : positive => Some x) [] = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_reverse_lookup_client {V E} (p : Prepared.t V E) exits v :
  Prepared.id_of (Prepared.reverse p exits) v = Prepared.id_of p v.
Proof.
  apply Prepared.reverse_id_of.
Qed.

Example raw_reverse_valid_client {V E} (p : Prepared.t V E) exits i :
  Prepared.valid_id (Prepared.reverse p exits) i <-> Prepared.valid_id p i.
Proof.
  apply Prepared.reverse_valid_id.
Qed.

Example reverse_arc_client :
  Prepared.arc (Prepared.reverse prepared_diamond [99; 99]) 4 (2, 4) 2.
Proof.
  apply (proj2 (Prepared.reverse_arc prepared_diamond [99; 99] 2 (2, 4) 4 diamond_ready)).
  exists 2, 4. repeat split; vm_compute; auto.
Qed.

Example unknown_exits_do_not_change_validity :
  Prepared.valid_id (Prepared.reverse prepared_diamond [99; 99]) 4.
Proof.
  apply Prepared.reverse_valid_id. exists 4. split; vm_compute; auto.
Qed.
