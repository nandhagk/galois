(** * Database initialization and prepared projections

    Slot preparation records sorted positions and restores the requested projection order.
    For example, positions [2; 0; 1] project [10; 20; 30] to [30; 10; 20].
    Initialization also retains the empty index's positive counter.
    Builds on: Database and the code towers of ValueSig and Index. *)

From Stdlib Require Import List PArith NArith Relations.Relation_Operators.
From Galois.Base Require Import Trie UnionFind.
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

(** A one-element value type exposes the public well-formedness laws in this test. *)
Module UnitValue <: VALUE.
  Definition t := unit.
  Definition eqb (_ _ : t) := true.
  Definition encode (_ : t) := 1%positive.
  Definition prim (_ : positive) (_ : list t) : option t := None.
  Definition merge (_ : positive) (_ _ : t) : t := tt.
  Definition bits (v : t) := Pos.size_nat (encode v).
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. intros [] []; reflexivity. Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. intros [] []; constructor; reflexivity. Qed.
  Lemma merge_comm : forall m a b, merge m a b = merge m b a.
  Proof. intros m [] []; reflexivity. Qed.
  Lemma merge_assoc : forall m a b c, merge m a (merge m b c) = merge m (merge m a b) c.
  Proof. intros m [] [] []; reflexivity. Qed.
  Lemma merge_idem : forall m a, merge m a a = a.
  Proof. intros m []; reflexivity. Qed.
End UnitValue.

Module UnitIndex := Index UnitValue.
Module UnitDatabase := Database UnitValue UnitIndex.

(** This raw state tests a missing self-history entry; its active invariant is unproved. *)
Definition alias_base :=
  let empty := UnitDatabase.init [Decl 2%positive [SId] ORel] [] in
  let first := UnitDatabase.allocate_id 1%positive empty in
  let second := UnitDatabase.allocate_id 2%positive first in
  let third := UnitDatabase.allocate_id 3%positive second in
  let row := UnitDatabase.put 2%positive [Id 2%positive] None third in
  UnitDatabase.union 1%positive 3%positive
    (UnitDatabase.union 1%positive 2%positive row).

Definition alias_candidate :=
  let db := alias_base in
  let store := db_row_store db in
  let original := UnitDatabase.db_row_code 2%positive [Id 2%positive] in
  let alias := UnitDatabase.db_row_code 2%positive [Id 3%positive] in
  match PTrieCode.get original (row_history store) with
  | None => db
  | Some (_, id) =>
    let history := PTrieCode.set alias ((2%positive, [Id 3%positive]), id)
      (PTrieCode.remove original (row_history store)) in
    let uses := DatabaseUses.add 3%positive (2%positive, [Id 3%positive])
      (DatabaseUseMap.remove 2%positive (row_uses store)) in
    let updated := {|
      row_history := history;
      row_links := row_links store;
      row_weights := row_weights store;
      row_keys := row_keys store;
      row_fresh := row_fresh store;
      row_uses := uses
    |} in
    DatabaseState (db_forest db) (db_nuses db) (db_npending db) (db_wmark db)
      (Id 3%positive :: db_written_cells db) (db_index_counters db)
      updated (db_slot_store db) (db_runtime db) (db_cache_updates db)
  end.

Example alias_candidate_observation :
  (UnitDatabase.row_get 2%positive [Id 2%positive] alias_candidate,
   UnitDatabase.db_locate 2%positive [Id 3%positive] alias_candidate,
   PTrieCode.get (UnitDatabase.db_row_code 2%positive [Id 2%positive])
     (row_history (db_row_store alias_candidate)),
   UnitDatabase.repr alias_candidate 2%positive,
   UnitDatabase.repr alias_candidate 3%positive) =
  (Some None, Some [Id 2%positive], None, 1%positive, 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example alias_candidate_repair_observation :
  let repaired := UnitDatabase.db_repair_entry
    2%positive [Id 3%positive] alias_candidate in
  (UnitDatabase.row_get 2%positive [Id 2%positive] repaired,
   UnitDatabase.row_get 2%positive [Id 1%positive] repaired,
   UnitDatabase.db_locate 2%positive [Id 3%positive] repaired) =
  (None, Some None, Some [Id 2%positive]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Clearing the occurrence store loses well-formedness and its recorded use. *)
Definition missing_use_initial := UnitDatabase.init [Decl 1%positive [] OId] [].
Definition missing_use_row := snd (UnitDatabase.make 1%positive [] missing_use_initial).
Definition missing_use_db :=
  database_set_row_store (db_row_store missing_use_initial) missing_use_row.

Example missing_use_db_not_wf : ~ UnitDatabase.wf missing_use_db.
Proof.
  intro Hwf.
  pose proof (UnitDatabase.database_public_idle missing_use_db (proj1 Hwf)) as Hidle.
  pose proof (UnitDatabase.database_idle_coverage missing_use_db Hidle
    1%positive [] (Some (Id 1%positive)) 1%positive) as Hcover.
  assert (Hrow : Model.row (UnitDatabase.view missing_use_db)
    1%positive [] (Some (Id 1%positive))) by (vm_compute; reflexivity).
  assert (Hid : UnitDatabase.row_ids [] (Some (Id 1%positive)) 1%positive)
    by (unfold UnitDatabase.row_ids; cbn; auto).
  specialize (Hcover Hrow Hid).
  destruct Hcover as [x [k0 [_ [Huse _]]]].
  vm_compute in Huse. contradiction.
Qed.

Example missing_use_db_observation :
  (UnitDatabase.row_get 1%positive [] missing_use_db,
    UnitDatabase.db_get_uses 1%positive missing_use_db,
    UnitDatabase.locate 1%positive [] missing_use_db) =
    (Some (Some (Id 1%positive)), [], None).
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty row history permits a parent link whose default sizes do not double. *)
Definition bad_row_link_db :=
  let db := UnitDatabase.init [] [] in
  let store := db_row_store db in
  database_set_row_store
    {| row_history := row_history store;
       row_links := PTrieCode.set 2%positive 1%positive (row_links store);
       row_weights := row_weights store;
       row_keys := row_keys store;
       row_fresh := row_fresh store;
       row_uses := row_uses store |} db.

Example bad_row_link_observation :
  let store := db_row_store bad_row_link_db in
  let parent r := match PTrieCode.get r (row_links store) with
    | Some p => p | None => r end in
  let size r := match PTrieCode.get r (row_weights store) with
    | Some n => n | None => 1%N end in
  (parent 2%positive, size 2%positive, size 1%positive,
    row_history store, row_uses store) =
    (1%positive, 1%N, 1%N, PTrieCode.empty, DatabaseUseMap.empty).
Proof.
  vm_compute. reflexivity.
Qed.

(** An occurrence can remain registered after the separate write history is erased. *)
Definition missing_written_history_db :=
  let db := missing_use_row in
  DatabaseState (db_forest db) (db_nuses db) (db_npending db) (db_wmark db)
    [] (db_index_counters db) (db_row_store db) (db_slot_store db) (db_runtime db)
    (db_cache_updates db).

Example missing_written_history_observation :
  (UnitDatabase.row_get 1%positive [] missing_written_history_db,
    UnitDatabase.db_get_uses 1%positive missing_written_history_db,
    UnitDatabase.locate 1%positive [] missing_written_history_db,
    db_written_cells missing_written_history_db) =
    (Some (Some (Id 1%positive)), [(1%positive, [])], Some [], []).
Proof.
  vm_compute. reflexivity.
Qed.

(** One active repair consumes its entry while retaining the historical occurrence count. *)
Definition one_repair_queued :=
  let empty := FixtureDatabase.init [Decl 2%positive [SId] ORel] [] in
  let first := snd (FixtureDatabase.make 9%positive [] empty) in
  let second := snd (FixtureDatabase.make 9%positive [] first) in
  let stored := FixtureDatabase.put 2%positive [Id 2%positive] None second in
  FixtureDatabase.union 1%positive 2%positive stored.

Example one_repair_inventory_stable :
  match FixtureDatabase.db_rstep (one_repair_queued, []) with
  | inr _ => False
  | inl (popped, work) =>
    match FixtureDatabase.db_rstep (popped, work) with
    | inr _ => False
    | inl (repaired, rest) =>
      (db_npending popped, length work, db_nuses popped,
        FixtureDatabase.row_get 2%positive [Id 2%positive] popped,
        UnionFind.repr (db_forest popped) 2%positive,
        db_npending repaired, length rest, db_nuses repaired,
        UnionFind.size_of (db_forest popped) 1%positive,
        UnionFind.size_of (db_forest repaired) 1%positive,
        FixtureDatabase.row_get 2%positive [Id 1%positive] repaired) =
      (0%N, 1, 1%N, Some None, 1%positive,
        0%N, 0, 1%N, 2, 2, Some None)
    end
  end.
Proof.
  vm_compute. reflexivity.
Qed.

(** Replacing the same row twice registers two historical identifier occurrences. *)
Example repeated_row_replacement_occurrences :
  let empty := FixtureDatabase.init [] [] in
  let first := FixtureDatabase.row_replace 1%positive [Id 1%positive] None None empty in
  let second := FixtureDatabase.row_replace 1%positive [Id 1%positive] (Some None)
    None first in
  (db_nuses first, db_nuses second,
    FixtureDatabase.row_get 1%positive [Id 1%positive] second) =
    (1%N, 2%N, Some None).
Proof.
  vm_compute. reflexivity.
Qed.

(** The losing identifier occurs in a row when a key or output contains it. *)
Definition affected_by_two (db : FixtureDatabase.t) : nat :=
  length (filter
    (fun stored => existsb (fun c =>
      match c with
      | Id i => Pos.eqb i 2%positive
      | Val _ => false
      end) (snd (fst stored) ++ option_list (snd stored)))
    (map snd (PTrieCode.elements (runtime_rows (db_runtime db))))).

(** Seven queued rows fit the occurrence budget and all lose identifier two. *)
Example rebuild_repairs_seven_affected_rows :
  let empty := FixtureDatabase.init
    [Decl 1%positive [SVal] OId; Decl 2%positive [SId; SVal] ORel] [] in
  let first := FixtureDatabase.make 1%positive [Val 1%positive] empty in
  let second := FixtureDatabase.make 1%positive [Val 2%positive] (snd first) in
  let rows := fold_left (fun db v =>
    FixtureDatabase.put 2%positive [Id 2%positive; Val v] None db)
    [1%positive; 2%positive; 3%positive; 4%positive; 5%positive; 6%positive]
    (snd second) in
  let queued := FixtureDatabase.union 1%positive 2%positive rows in
  let rebuilt := FixtureDatabase.rebuild queued in
  (FixtureDatabase.db_rebuild_fuel queued,
    affected_by_two queued, affected_by_two rebuilt,
    fst (FixtureDatabase.find 2%positive rebuilt)) =
    (38%N, 7, 0, 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** A write records its cells and cache-call count even when the function has no slots. *)
Example cache_history_without_slots :
  let db := FixtureDatabase.init [Decl 3%positive [SVal] ORel] [] in
  let written := FixtureDatabase.put 3%positive [Val 7%positive] None db in
  (db_written_cells written, db_cache_updates written,
   FixtureDatabase.row_get 3%positive [Val 7%positive] written) =
    ([Val 7%positive; Val 7%positive], 1%N, Some None).
Proof.
  vm_compute. reflexivity.
Qed.

(** Deleting a row extends its history while removing the actual stored binding. *)
Example cache_history_on_deletion :
  let db := FixtureDatabase.init [Decl 3%positive [SVal] ORel] [] in
  let written := FixtureDatabase.put 3%positive [Val 7%positive] None db in
  let removed := FixtureDatabase.row_delete 3%positive [Val 7%positive] written in
  (db_written_cells removed, db_cache_updates removed,
   FixtureDatabase.row_get 3%positive [Val 7%positive] removed) =
    ([Val 7%positive; Val 7%positive; Val 7%positive], 2%N, None).
Proof.
  vm_compute. reflexivity.
Qed.

(** Normalization leaves an unallocated identifier unchanged even when its query code is large. *)
Example normalize_unallocated_identifier :
  FixtureDatabase.normal_cell (FixtureDatabase.init [] []) (Id 1048576%positive) =
    Id 1048576%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** The allocation guard preserves representative lookup and mixed value/identifier keys. *)
Example normalize_allocated_and_unallocated :
  let first := snd (FixtureDatabase.make 9%positive [] (FixtureDatabase.init [] [])) in
  let second := snd (FixtureDatabase.make 9%positive [] first) in
  let db := FixtureDatabase.union 1%positive 2%positive second in
  FixtureDatabase.normal_key db [Id 2%positive; Val 3%positive; Id 1024%positive] =
    [Id 1%positive; Val 3%positive; Id 1024%positive].
Proof.
  vm_compute. reflexivity.
Qed.

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
(** The complete-history invariant excludes the earlier raw alias candidate. *)
Example alias_candidate_not_history_complete :
  ~ UnitDatabase.database_history_complete alias_candidate.
Proof.
  intro Hcomplete.
  assert (Hentry :
    PTrieCode.get (UnitDatabase.db_row_code 2%positive [Id 3%positive])
      (row_history (db_row_store alias_candidate)) =
      Some ((2%positive, [Id 3%positive]), 1%positive)).
  { vm_compute. reflexivity. }
  assert (Hconnected :
    UnitDatabase.database_history_connected alias_candidate 1%positive 1%positive).
  { apply rst_refl. }
  assert (Hfixed :
    (match PTrieCode.get 1%positive (row_links (db_row_store alias_candidate)) with
     | Some parent => parent | None => 1%positive end) = 1%positive).
  { vm_compute. reflexivity. }
  destruct (Hcomplete 2%positive [Id 3%positive] (2%positive, [Id 3%positive])
    1%positive 1%positive Hentry Hconnected Hfixed)
    as [current [s [Hkey [Hself _]]]].
  change (Some [Id 2%positive] = Some current) in Hkey.
  injection Hkey as <-.
  change (None = Some ((2%positive, [@Id UnitValue.t 2%positive]), s)) in Hself.
  discriminate Hself.
Qed.
(** A historical use follows its row through two successive key normalizations. *)
Definition successive_alias_source :=
  let empty := FixtureDatabase.init [Decl 2%positive [SId] ORel] [] in
  let first := snd (FixtureDatabase.make 9%positive [] empty) in
  let second := snd (FixtureDatabase.make 9%positive [] first) in
  let third := snd (FixtureDatabase.make 9%positive [] second) in
  let fourth := snd (FixtureDatabase.make 9%positive [] third) in
  let stored := FixtureDatabase.put 2%positive [Id 3%positive] None fourth in
  FixtureDatabase.union 2%positive 3%positive
    (FixtureDatabase.union 1%positive 4%positive stored).

Example repair_follows_successive_aliases :
  match FixtureDatabase.db_rstep (successive_alias_source, []) with
  | inr _ => False
  | inl active =>
    match FixtureDatabase.db_rstep active with
    | inr _ => False
    | inl (first, _) =>
      let queued := FixtureDatabase.union 1%positive 2%positive first in
      match FixtureDatabase.db_rstep (queued, []) with
      | inr _ => False
      | inl active =>
        match FixtureDatabase.db_rstep active with
        | inr _ => False
        | inl (second, rest) =>
          (FixtureDatabase.db_locate 2%positive [Id 3%positive] first,
            FixtureDatabase.db_locate 2%positive [Id 3%positive] second,
            FixtureDatabase.db_locate 2%positive [Id 2%positive] second,
            FixtureDatabase.row_get 2%positive [Id 2%positive] second,
            FixtureDatabase.row_get 2%positive [Id 1%positive] second,
            rest) =
          (Some [Id 2%positive], Some [Id 1%positive], Some [Id 1%positive],
            None, Some None, [])
        end
      end
    end
  end.
Proof.
  vm_compute. reflexivity.
Qed.

(** A queued one-entry bucket has enough measure to activate and consume its repair. *)
Definition measured_one_bucket :=
  let empty := UnitDatabase.init [Decl 2%positive [SId] ORel] [] in
  let first := snd (UnitDatabase.make 9%positive [] empty) in
  let second := snd (UnitDatabase.make 9%positive [] first) in
  UnitDatabase.union 1%positive 2%positive
    (UnitDatabase.put 2%positive [Id 2%positive] None second).

Lemma measured_one_bucket_wf : UnitDatabase.wf measured_one_bucket.
Proof.
  unfold measured_one_bucket.
  apply UnitDatabase.wf_union.
  - apply UnitDatabase.wf_put.
    + apply UnitDatabase.wf_make.
      * apply UnitDatabase.wf_make.
        -- apply UnitDatabase.wf_init.
        -- intros j Hin. contradiction.
        -- intros perm Hin. vm_compute in Hin. contradiction.
      * intros j Hin. contradiction.
      * intros perm Hin. vm_compute in Hin. contradiction.
    + split.
      * intros i Hin. cbn [app option_list In] in Hin.
        destruct Hin as [Hin | Hin]; [injection Hin as Hi; subst i | contradiction].
        vm_compute. easy.
      * split.
        -- intros perm Hin. vm_compute in Hin. contradiction.
        -- vm_compute. exact I.
  - vm_compute. easy.
  - vm_compute. easy.
Qed.

Example pop_measure_spends_one :
  match UnitDatabase.rstep (measured_one_bucket, []) with
  | inr _ => False
  | inl state =>
    (UnitDatabase.rebuild_measure (measured_one_bucket, []),
      UnitDatabase.rebuild_measure state, length (snd state)) = (3, 2, 1)
  end.
Proof.
  vm_compute. reflexivity.
Qed.

Example repair_measure_spends_one :
  match UnitDatabase.rstep (measured_one_bucket, []) with
  | inr _ => False
  | inl active =>
    match UnitDatabase.rstep active with
    | inr _ => False
    | inl repaired =>
      (UnitDatabase.rebuild_measure active, UnitDatabase.rebuild_measure repaired,
        length (snd repaired)) = (2, 1, 0)
    end
  end.
Proof.
  vm_compute. reflexivity.
Qed.

(** A redundant insertion records a consumed output even when the stored output is retained. *)
Example redundant_put_records_discarded_input :
  let first := FixtureDatabase.put 3%positive [] None
    (FixtureDatabase.init [Decl 3%positive [] ORel] []) in
  let result := FixtureDatabase.put 3%positive [] (Some (Val 1048576%positive)) first in
  (FixtureDatabase.row_get 3%positive [] result,
    db_written_cells result, db_cache_updates result) =
    (Some None, [Val 1048576%positive], 1%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** An undeclared fresh make records the actual function and key that its query consumed. *)
Example make_undeclared_records_input :
  let result := snd (FixtureDatabase.make 1048576%positive [Val 2097152%positive]
    (FixtureDatabase.init [] [])) in
  (db_written_cells result, db_index_counters result, FixtureDatabase.ids result) =
    ([Val 2097152%positive], [1048576%positive; 1%positive], 1%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Constructor reuse retains exactly the existing state, including its input history. *)
Example make_reuse_preserves_recorded_state :
  let first := snd (FixtureDatabase.make 2%positive [Val 3%positive]
    (FixtureDatabase.init [Decl 2%positive [SVal] OId] [])) in
  snd (FixtureDatabase.make 2%positive [Val 3%positive] first) = first.
Proof.
  vm_compute. reflexivity.
Qed.

(** Lookup follows a two-edge identifier path and preserves the database it returns. *)
Example lookup_stale_identifier_keeps_state :
  let stored := FixtureDatabase.put 2%positive [Id 1%positive] None
    successive_alias_source in
  let queued := FixtureDatabase.union 1%positive 2%positive stored in
  FixtureDatabase.lookup 2%positive [Id 3%positive] queued = (Some None, queued).
Proof.
  vm_compute. reflexivity.
Qed.

(** A stale input key inserts its canonical row without rewriting historical rows. *)
Example put_stale_identifier_uses_root :
  let queued := FixtureDatabase.union 1%positive 2%positive successive_alias_source in
  let result := FixtureDatabase.put 2%positive [Id 3%positive] None queued in
  (FixtureDatabase.row_get 2%positive [Id 1%positive] result,
   FixtureDatabase.row_get 2%positive [Id 2%positive] result,
   FixtureDatabase.row_get 2%positive [Id 3%positive] result) =
    (Some None, None, Some None).
Proof.
  vm_compute. reflexivity.
Qed.

(** Reusing a constructor follows its stale output while preserving the stored state. *)
Example make_stale_output_keeps_state :
  let initial := FixtureDatabase.init [Decl 1%positive [SVal] OId] [] in
  let stored := fold_left
    (fun db value => snd (FixtureDatabase.make 1%positive [Val value] db))
    [1%positive; 2%positive; 3%positive; 4%positive] initial in
  let paired := FixtureDatabase.union 1%positive 2%positive
    (FixtureDatabase.union 3%positive 4%positive stored) in
  let queued := FixtureDatabase.union 1%positive 3%positive paired in
  FixtureDatabase.make 1%positive [Val 4%positive] queued = (1%positive, queued).
Proof.
  vm_compute. reflexivity.
Qed.

(** Rebuilding consumes stale losers through a two-edge path and retains their relation. *)
Example rebuild_stale_losers_preserves_row :
  let queued := FixtureDatabase.union 1%positive 2%positive successive_alias_source in
  let result := FixtureDatabase.rebuild queued in
  (FixtureDatabase.row_get 2%positive [Id 1%positive] result,
   FixtureDatabase.row_get 2%positive [Id 3%positive] result,
   fst (FixtureDatabase.find 3%positive result), runtime_queue (db_runtime result),
   db_npending result) = (Some None, None, 1%positive, [], 0%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Value-only insertion preserves row and index results without allocating row identity. *)
Example put_value_only_row_skips_identity :
  let initial := FixtureDatabase.init [Decl 2%positive [SVal; SVal; SVal] ORel]
    [(2%positive, [0; 1; 2]); (2%positive, [1; 2; 0]);
     (2%positive, [2; 0; 1]); (2%positive, [2; 1; 0])] in
  let key := [Val 5%positive; Val 7%positive; Val 9%positive] in
  let result := FixtureDatabase.put 2%positive key None initial in
  let index := FixtureDatabase.index 0%N false result in
  let fresh := FixtureDatabase.index 1%N true result in
  (FixtureDatabase.row_get 2%positive key result,
   FixtureIndex.children index (FixtureIndex.root index),
   FixtureIndex.children fresh (FixtureIndex.root fresh),
   row_fresh (db_row_store result), row_history (db_row_store result),
   db_nuses result) =
    (Some None, [Val 5%positive], [Val 7%positive], 1%positive, PTrieCode.empty, 0%N).
Proof.
  vm_compute. reflexivity.
Qed.
