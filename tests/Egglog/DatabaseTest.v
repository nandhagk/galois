(** * Database initialization and prepared projections

    Slot preparation records sorted positions and restores the requested projection order.
    For example, positions [2; 0; 1] project [10; 20; 30] to [30; 10; 20].
    Initialization also retains the empty index's positive counter.
    Builds on: Database and the code towers of ValueSig and Index. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
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

(** Constructor allocation reuses an existing key and allocates once for each new key. *)
Example make_reuses_constructor :
  let db := FixtureDatabase.init [Decl 2%positive [SVal] OId] [] in
  let first := FixtureDatabase.make 2%positive [Val 3%positive] db in
  let again := FixtureDatabase.make 2%positive [Val 3%positive] (snd first) in
  let next := FixtureDatabase.make 2%positive [Val 4%positive] (snd again) in
  (fst first, fst again, fst next, FixtureDatabase.ids (snd next)) =
    (1%positive, 1%positive, 2%positive, 2%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** An undeclared make still returns an allocated identifier without adding a row. *)
Example make_undeclared_allocates :
  let result := FixtureDatabase.make 9%positive [] (FixtureDatabase.init [] []) in
  (fst result, FixtureDatabase.ids (snd result), FixtureDatabase.changed (snd result),
   FixtureDatabase.row_get 9%positive [] (snd result)) =
    (1%positive, 1%N, true, None).
Proof.
  vm_compute. reflexivity.
Qed.

(** Lattice writes retain the join and leave a redundant insertion quiet. *)
Example put_lattice_join :
  let db := FixtureDatabase.init [Decl 3%positive [SVal] (OLat 1%positive)] [] in
  let first := FixtureDatabase.put 3%positive [Val 2%positive] (Some (Val 4%positive)) db in
  let quiet := FixtureDatabase.put 3%positive [Val 2%positive] (Some (Val 1%positive))
    (FixtureDatabase.advance first) in
  let next := FixtureDatabase.put 3%positive [Val 2%positive] (Some (Val 8%positive)) quiet in
  (FixtureDatabase.row_get 3%positive [Val 2%positive] quiet,
   FixtureDatabase.changed quiet,
   FixtureDatabase.row_get 3%positive [Val 2%positive] next,
   FixtureDatabase.changed next) =
    (Some (Some (Val 4%positive)), false, Some (Some (Val 8%positive)), true).
Proof.
  vm_compute. reflexivity.
Qed.

(** Constructor output conflicts queue a loser and preserve allocation and stored keys. *)
Example put_constructor_conflict :
  let db := FixtureDatabase.init [Decl 2%positive [SVal] OId] [] in
  let first := FixtureDatabase.make 2%positive [Val 3%positive] db in
  let second := FixtureDatabase.make 2%positive [Val 4%positive] (snd first) in
  let result := FixtureDatabase.put 2%positive [Val 3%positive] (Some (Id (fst second)))
    (FixtureDatabase.advance (snd second)) in
  (FixtureDatabase.ids result, FixtureDatabase.changed result, db_npending result,
   fst (FixtureDatabase.find (fst second) result),
   FixtureDatabase.row_get 2%positive [Val 3%positive] result) =
    (2%N, true, 1%N, 1%positive, Some (Some (Id 1%positive))).
Proof.
  vm_compute. reflexivity.
Qed.

(** Shared projections retain both contributions when one row's output changes. *)
Example put_projection_multiplicity :
  let db := FixtureDatabase.init
    [Decl 3%positive [SVal; SVal] (OLat 1%positive)] [(3%positive, [0])] in
  let first := FixtureDatabase.put 3%positive [Val 2%positive; Val 3%positive]
    (Some (Val 4%positive)) db in
  let second := FixtureDatabase.put 3%positive [Val 2%positive; Val 5%positive]
    (Some (Val 6%positive)) first in
  let result := FixtureDatabase.put 3%positive [Val 2%positive; Val 3%positive]
    (Some (Val 8%positive)) second in
  let table := FixtureDatabase.projection_table_get 1%positive
    (runtime_projection_counts (db_runtime result)) in
  PTrieCode.get (FixtureDatabase.db_tuple_code [Val 2%positive]) table =
    Some ([Val 2%positive], 2%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Initialization retains declared output kinds and gives the first declaration priority. *)
Example init_declared_kinds :
  let db := FixtureDatabase.init
    [Decl 1%positive [SId] OId; Decl 1%positive [SVal] ORel] [] in
  (FixtureDatabase.kind_get 1%positive db, FixtureDatabase.kind_get 2%positive db) =
    (Some OId, None).
Proof.
  vm_compute. reflexivity.
Qed.

(** Union records arbitrary requested equalities without allocating identifiers. *)
Example union_unallocated_identifiers :
  let db := FixtureDatabase.union 7%positive 9%positive (FixtureDatabase.init [] []) in
  (FixtureDatabase.ids db, FixtureDatabase.changed db, db_npending db,
   fst (FixtureDatabase.find 7%positive db), fst (FixtureDatabase.find 9%positive db)) =
    (0%N, true, 1%N, 7%positive, 7%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** Advancing clears the flag while preserving pending equality work and representatives. *)
Example advance_keeps_equality_work :
  let db := FixtureDatabase.advance
    (FixtureDatabase.union 7%positive 9%positive (FixtureDatabase.init [] [])) in
  (FixtureDatabase.changed db, db_npending db, fst (FixtureDatabase.find 9%positive db)) =
    (false, 1%N, 7%positive).
Proof.
  vm_compute. reflexivity.
Qed.

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

(** Rebuild repairs identifier occurrences and joins lattice rows whose keys become equal. *)
Example rebuild_moves_keys_and_joins_values :
  let db := FixtureDatabase.init
    [Decl 1%positive [SVal] OId; Decl 2%positive [SId] ORel;
     Decl 3%positive [SId] (OLat 1%positive)]
    [(2%positive, [0]); (3%positive, [0])] in
  let first := FixtureDatabase.make 1%positive [Val 1%positive] db in
  let second := FixtureDatabase.make 1%positive [Val 2%positive] (snd first) in
  let relation := FixtureDatabase.put 2%positive [Id (fst second)] None (snd second) in
  let left := FixtureDatabase.put 3%positive [Id (fst first)] (Some (Val 4%positive)) relation in
  let right := FixtureDatabase.put 3%positive [Id (fst second)] (Some (Val 8%positive)) left in
  let result := FixtureDatabase.rebuild
    (FixtureDatabase.union (fst first) (fst second) (FixtureDatabase.advance right)) in
  (FixtureDatabase.row_get 2%positive [Id 1%positive] result,
   FixtureDatabase.row_get 2%positive [Id 2%positive] result,
   FixtureDatabase.row_get 3%positive [Id 1%positive] result,
   FixtureDatabase.row_get 3%positive [Id 2%positive] result,
   FixtureDatabase.row_get 1%positive [Val 2%positive] result,
   runtime_queue (db_runtime result), db_npending result, FixtureDatabase.changed result) =
    (Some None, None, Some (Some (Val 8%positive)), None,
     Some (Some (Id 1%positive)), [], 0%N, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** A database with no queued work is returned byte-for-byte by the loop. *)
Example rebuild_empty_queue_identity :
  let db := FixtureDatabase.put 3%positive [Val 2%positive] (Some (Val 4%positive))
    (FixtureDatabase.init [Decl 3%positive [SVal] (OLat 1%positive)] [(3%positive, [0])]) in
  FixtureDatabase.rebuild db = db.
Proof.
  vm_compute. reflexivity.
Qed.
