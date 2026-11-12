(** * Prepared database projections

    Slot preparation records sorted positions and restores the requested projection order.
    For example, positions [2; 0; 1] project [10; 20; 30] to [30; 10; 20].
    Builds on: Database and the code towers of ValueSig and Index. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Index Database DatabaseSig.

Import List.ListNotations.

Module FixtureValue <: VALUE_OPS.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (_ : positive) (_ : list t) : option t := None.
  Definition merge (_ : positive) := Pos.max.
End FixtureValue.

Module FixtureIndex := IndexCode FixtureValue.
Module FixtureDatabase := DatabaseCode FixtureValue FixtureIndex.

(** Preparation retains the original ranks after sorting absolute positions. *)
Example slot_sorted_positions :
  ranked_positions (prepare_slot_layout [2; 0; 1]) =
    [(0, 2%positive); (1, 3%positive); (2, 1%positive)].
Proof.
  vm_compute. reflexivity.
Qed.

(** Stored gaps advance relative to the last selected position. *)
Example slot_prepared_gaps :
  projection_steps (prepare_slot_layout [5; 1; 3]) =
    [(1, 2%positive); (2, 3%positive); (2, 1%positive)].
Proof.
  vm_compute. reflexivity.
Qed.

(** Rank lookup restores the requested order after the tuple scan. *)
Example slot_projection_order :
  project_slot_layout (prepare_slot_layout [2; 0; 1]) [10; 20; 30] = [30; 10; 20].
Proof.
  vm_compute. reflexivity.
Qed.

(** Five original ranks are restored independently of the trie's enumeration order. *)
Example slot_projection_mixed_ranks :
  project_slot_layout (prepare_slot_layout [4; 1; 3; 0; 2]) [10; 20; 30; 40; 50] =
    [50; 20; 40; 10; 30].
Proof.
  vm_compute. reflexivity.
Qed.

(** Empty and out-of-range projections contribute no cells. *)
Example slot_projection_boundaries :
  (project_slot_layout (prepare_slot_layout []) [10; 20],
   project_slot_layout (prepare_slot_layout [7; 1]) [10; 20]) = ([], [20]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Repeated positions keep distinct original ranks even on malformed permutations. *)
Example slot_projection_duplicates :
  project_slot_layout (prepare_slot_layout [1; 0; 1]) [10; 20] = [20; 10; 20].
Proof.
  vm_compute. reflexivity.
Qed.

(** Initialization stores one prepared layout for each supplied slot. *)
Example init_stores_prepared_slots :
  prepared_slots _ (db_slot_store (FixtureDatabase.init [] [(1%positive, [2; 0; 1])])) =
    [(1%positive, prepare_slot_layout [2; 0; 1])].
Proof.
  vm_compute. reflexivity.
Qed.

(** The layout budget reads the large unary positions from the review example. *)
Example layout_work_large_positions :
  layout_work [(1%positive, [101; 100])] = 618.
Proof.
  vm_compute. reflexivity.
Qed.
