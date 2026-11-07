(** * Reference reachability observations

    These tests use hand-written graphs without a search or dominator producer.
    For example, deleting either diamond arm leaves the join reachable.
    Builds on: GraphReach, GraphModelTest and GraphPreparedTest. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphReach.
From Galois.Tests.Graph Require Import GraphModelTest GraphPreparedTest.
Import List.ListNotations.
Open Scope positive_scope.

Example diamond_live :
  map (fun v => FinSet.mem positive_encoding v
    (Reach.set prepared_diamond Reach.unrestricted [1])) [1; 2; 3; 4; 9] =
  [true; true; true; true; false].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_arm_avoiding :
  FinSet.mem positive_encoding 4 (Reach.set prepared_diamond (Reach.blocked 2) [1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_entry_avoiding :
  FinSet.elements (Reach.set prepared_diamond (Reach.blocked 1) [1]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example within_blocks_paths :
  let scope := Scope.Make FinSet.empty
    (Some (FinSet.of_list positive_encoding [1; 4])) in
  map (fun v => FinSet.mem positive_encoding v (Reach.set prepared_diamond scope [1]))
    [1; 2; 3; 4] = [true; false; false; false].
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_roots :
  FinSet.elements (Reach.set prepared_diamond Reach.unrestricted [9]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_roots :
  Reach.set prepared_diamond Reach.unrestricted [1; 1; 1; 1; 1; 1; 1; 1; 1; 1] =
  Reach.set prepared_diamond Reach.unrestricted [1].
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entries_after_deletion :
  map (fun v => FinSet.mem positive_encoding v
    (Reach.set prepared_two (Reach.blocked 1) (Prepared.entry_ids prepared_two))) [1; 2; 3; 4] =
  [false; false; true; true].
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_terminates :
  FinSet.elements (Reach.set prepared_loop Reach.unrestricted [1]) = [1].
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_deleted :
  FinSet.elements (Reach.set prepared_loop (Reach.blocked 1) [1]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_boundary :
  FinSet.elements (Reach.set prepared_empty Reach.unrestricted [1]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_boundary :
  let p := Prepared.prepare positive_encoding (fixture [40] [40] []) in
  (FinSet.elements (Reach.set p Reach.unrestricted [1]),
    Prepared.name_of p 1) = ([1], Some 40).
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_budget :
  let next := Reach.successors prepared_diamond Reach.unrestricted in
  let all := Reach.universe prepared_diamond in
  (Reach.credit next all +
    length (Reach.roots_in prepared_diamond Reach.unrestricted [1]%positive))%nat = 9%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example exhausted_stack_is_visible :
  fst (Reach.loop (fun _ => []) 0 [1] [1] []) = [1].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_stack_empties :
  let next := Reach.successors prepared_diamond Reach.unrestricted in
  fst (Reach.loop next 9 [1] (Reach.universe prepared_diamond) []) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Module ParallelLabels.

(** Distinct labels let two outgoing edges share their target without becoming duplicates. *)
Inductive edge :=
  | First
  | Second
  | Back.

Definition source (e : edge) : positive :=
  match e with
  | First => 1
  | Second => 1
  | Back => 2
  end.

Definition target (e : edge) : positive :=
  match e with
  | First => 2
  | Second => 2
  | Back => 1
  end.

Definition edges := [First; Second; Back].

(** First and Second label 1 -> 2, while Back labels 2 -> 1. *)
Definition graph :=
  Graph.of_pure [1] [1; 2] (fun v => filter (fun e => Pos.eqb (source e) v) edges)
    source target.

Definition prepared := Prepared.prepare positive_encoding graph.

Example ready : Prepared.ready prepared.
Proof.
  apply Prepared.prepare_ready; [exact positive_encoding_laws| |].
  - constructor.
    + change (NoDup [1; 2]).
      repeat (apply NoDup_cons; [cbn; intuition discriminate|]). apply NoDup_nil.
    + intros v Hv. change (In v [1]) in Hv. change (In v [1; 2]).
      cbn in Hv |- *. intuition congruence.
    + intros v e Hin.
      change (In e (filter (fun a => Pos.eqb (source a) v) edges)) in Hin.
      apply filter_In in Hin. destruct Hin as [_ Hsame].
      change (source e = v). now apply Pos.eqb_eq in Hsame.
    + intros v e Hv He. change (In (target e) [1; 2]).
      destruct e.
      * right. left. reflexivity.
      * right. left. reflexivity.
      * left. reflexivity.
  - intro v.
    change (NoDup (filter (fun e => Pos.eqb (source e) v) edges)).
    apply NoDup_filter. change (NoDup [First; Second; Back]).
    repeat (apply NoDup_cons; [cbn; intuition discriminate|]). apply NoDup_nil.
Qed.

Example retains_parallel_successors :
  (Prepared.succ_edges prepared 1, Prepared.succ_edges prepared 2) =
  ([(First, 2); (Second, 2)], [(Back, 1)]).
Proof.
  vm_compute. reflexivity.
Qed.

Example reaches_both_nodes :
  map (fun v => FinSet.mem positive_encoding v (Reach.set prepared Reach.unrestricted [1]))
    [1; 2; 9] = [true; true; false].
Proof.
  vm_compute. reflexivity.
Qed.

Example exhausts_actual_pending_work :
  let next := Reach.successors prepared Reach.unrestricted in
  let all := Reach.universe prepared in
  let initial := Reach.roots_in prepared Reach.unrestricted [1] in
  let fuel := (Reach.credit next all + length initial)%nat in
  Reach.loop next fuel initial all [] = ([], [2; 1]).
Proof.
  vm_compute. reflexivity.
Qed.

Example blocking_target_leaves_entry :
  FinSet.elements (Reach.set prepared (Reach.blocked 2) [1]) = [1].
Proof.
  vm_compute. reflexivity.
Qed.

End ParallelLabels.
