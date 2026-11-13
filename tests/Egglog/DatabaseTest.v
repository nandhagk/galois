(** * Database initialization and prepared projections

    Slot preparation records sorted positions and restores the requested projection order.
    For example, positions [2; 0; 1] project [10; 20; 30] to [30; 10; 20].
    Initialization also retains the empty index's positive counter.
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

(** Even without slots, the empty index's next counter must be retained. *)
Example init_empty_index_counter :
  db_index_counters (FixtureDatabase.init [] []) = [1%positive].
Proof.
  vm_compute. reflexivity.
Qed.

(** The empty database's watermark includes that positive counter. *)
Example init_empty_watermark :
  db_wmark (FixtureDatabase.init [] []) = 1%N.
Proof.
  vm_compute. reflexivity.
Qed.

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

(** Both an empty layout and missing positions project an empty tuple to an empty tuple. *)
Example slot_projection_empty_tuple :
  (project_slot_layout (prepare_slot_layout []) ([] : list nat),
   project_slot_layout (prepare_slot_layout [0; 2]) ([] : list nat)) = ([], []).
Proof.
  vm_compute. reflexivity.
Qed.

(** Identifier and value cells retain their constructors, order and repeated positions. *)
Example slot_projection_mixed_cells :
  project_slot_layout (prepare_slot_layout [3; 0; 2; 1; 0])
    ([Id 1%positive; Val 5%positive; Id 3%positive; Val 8%positive] : list (cell positive)) =
      [Val 8%positive; Id 1%positive; Id 3%positive; Val 5%positive; Id 1%positive].
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
