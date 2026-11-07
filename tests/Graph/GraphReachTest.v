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
