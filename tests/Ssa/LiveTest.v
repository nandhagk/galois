(** * Indexed liveness examples

    Reverse searches distinguish uses, kills and cyclic paths before grouping block entries.
    For example, a read of a variable in its own assignment stays live before that assignment.
    Builds on: Ssa.Live and Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key Trie.
From Galois.Program Require Import CfgSig.
From Galois.Ssa Require Import Lang LiveSig Present Live.
Import List.ListNotations.
Local Open Scope positive_scope.

Module Ops <: OPS.
  Definition K := unit.
  Definition G := unit.
  Definition C := unit.
  Definition eval (_ : unit) (_ : list unit) : option unit := None.
  Definition test (_ : unit) (_ : list unit) : option bool := None.
  Definition mov := tt.
End Ops.
Module Source.
  Definition t := func positive unit unit.
End Source.
Module View := PresentT Ops UnitKeyT UnitKeyT.
Module L := LiveCode Ops Source View.Q View.R BlockEdge PointEdge PointKey
  View.BC View.C View.U View.SP.

Definition straight : Source.t :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [] [(2, tt, [9])] (Return [2]))].

Example follows_use_and_stops_at_definition : L.live_in straight = [(1, [9])].
Proof. vm_compute. reflexivity. Qed.

Definition same_variable : Source.t :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [] [(9, tt, [9; 9])] (Return [9]))].

Example use_before_definition_and_duplicate_use : L.live_in same_variable = [(1, [9])].
Proof. vm_compute. reflexivity. Qed.

Definition parameter : Source.t :=
  Func positive unit unit 1 [] [(1, Block positive unit unit [9] [] (Return [9]))].

Example parameter_binding_kills_at_entry : L.live_in parameter = [(1, [])].
Proof. vm_compute. reflexivity. Qed.

Definition cyclic : Source.t :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [] [] (Jump 2 []));
     (2, Block positive unit unit [] [(7, tt, [9])] (Branch tt [7] 2 [] 3 []));
     (3, Block positive unit unit [] [] (Return [7]))].

Example loop_terminates_with_live_predecessors :
  L.live_in cyclic = [(1, [9]); (2, [9]); (3, [7])].
Proof. vm_compute. reflexivity. Qed.

Definition unused_cycle : Source.t :=
  Func positive unit unit 1 [] [(1, Block positive unit unit [] [] (Jump 1 []))].

Example unused_cycle_has_empty_live_row : L.live_in unused_cycle = [(1, [])].
Proof. vm_compute. reflexivity. Qed.

Example one_non_killing_parallel_edge_allows_propagation :
  live_killed (live_kill_add 1 2 [] (live_kill_add 1 2 [9] Empty)) 1 2 9 = false.
Proof. vm_compute. reflexivity. Qed.

Example all_parallel_edges_kill :
  live_killed (live_kill_add 1 2 [9; 8] (live_kill_add 1 2 [9] Empty)) 1 2 9 = true.
Proof. vm_compute. reflexivity. Qed.

Definition entry_and_inside : Source.t :=
  Func positive unit unit 1 [9; 10]
    [(1, Block positive unit unit [] [(2, tt, [9])] (Jump 2 []));
     (2, Block positive unit unit [] [(3, tt, [9]); (4, tt, [3; 10])] (Return [4]))].

Example cached_grouping_preserves_live_rows :
  L.live_in entry_and_inside = L.live_in_spec entry_and_inside.
Proof. vm_compute. reflexivity. Qed.

Example cache_distinguishes_block_entries_and_internal_points :
  let q := View.R.prepare entry_and_inside in
  let entries := L.entry_table q (View.BC.nodes q) in
  (trie_get (PointKey.encode (1, 0%N)) entries,
   trie_get (PointKey.encode (2, 0%N)) entries,
   trie_get (PointKey.encode (2, 1%N)) entries) = (Some 1, Some 2, None).
Proof. vm_compute. reflexivity. Qed.

Example grouping_records_an_entry_and_skips_an_internal_point :
  let q := View.R.prepare entry_and_inside in
  let entries := L.entry_table q (View.BC.nodes q) in
  L.group_entry entries 10 (2, 1%N) (L.group_entry entries 9 (2, 0%N) Empty) =
    PTrieCode.set 2 [9] Empty.
Proof. vm_compute. reflexivity. Qed.

Example seed_reuses_its_point_encoding :
  live_seed PointKey.encode (2, 3%N) 9 Empty =
    live_seed_spec PointKey.encode (2, 3%N) 9 Empty.
Proof. vm_compute. reflexivity. Qed.

Example discovery_reuses_its_point_encoding :
  let st := {| live_seen := @Empty unit; live_todo := []; live_done := [] |} in
  live_discover PointKey.encode (2, 3%N) st =
    live_discover_spec PointKey.encode (2, 3%N) st.
Proof. vm_compute. reflexivity. Qed.

Example predecessors_reuse_point_encodings :
  let q := View.R.prepare entry_and_inside in
  let n := (2, 2%N) in
  let st := {| live_seen := @Empty unit; live_todo := []; live_done := [] |} in
  L.add_predecessors q (L.reverse_kills q) 9 n (View.C.inc q n) st =
    L.add_predecessors_spec q (L.reverse_kills q) 9 n (View.C.inc q n) st.
Proof. vm_compute. reflexivity. Qed.

Example cached_search_preserves_loop_rows : L.live_in cyclic = L.live_in_spec cyclic.
Proof. vm_compute. reflexivity. Qed.

Example cached_search_preserves_empty_cycle_rows :
  L.live_in unused_cycle = L.live_in_spec unused_cycle.
Proof. vm_compute. reflexivity. Qed.

Example one_cached_parallel_edge_can_propagate :
  let n := (1, 0%N) in
  let killing := LiveEdge n (PointKey.encode n) (PTrieCode.set 9 tt Empty) in
  let clear := LiveEdge n (PointKey.encode n) Empty in
  live_done (L.cached_predecessors
    (PTrieCode.set (PointKey.encode (2, 0%N)) [killing; clear] Empty) 9 (2, 0%N)
    {| live_seen := Empty; live_todo := []; live_done := [] |}) = [n].
Proof. vm_compute. reflexivity. Qed.

Example all_cached_parallel_edges_stop_propagation :
  let n := (1, 0%N) in
  let first := LiveEdge n (PointKey.encode n) (PTrieCode.set 9 tt Empty) in
  let second := LiveEdge n (PointKey.encode n) (PTrieCode.set 9 tt (PTrieCode.set 8 tt Empty)) in
  live_done (L.cached_predecessors
    (PTrieCode.set (PointKey.encode (2, 0%N)) [first; second] Empty) 9 (2, 0%N)
    {| live_seen := Empty; live_todo := []; live_done := [] |}) = [].
Proof. vm_compute. reflexivity. Qed.

Example cached_parallel_predecessors_are_discovered_once :
  let n := (1, 0%N) in
  let clear := LiveEdge n (PointKey.encode n) Empty in
  live_done (L.cached_predecessors
    (PTrieCode.set (PointKey.encode (2, 0%N)) [clear; clear] Empty) 9 (2, 0%N)
    {| live_seen := Empty; live_todo := []; live_done := [] |}) = [n].
Proof. vm_compute. reflexivity. Qed.

Example cache_retains_the_presented_predecessors :
  let q := View.R.prepare cyclic in
  map live_pred (index_row (L.incoming_table q) (PointKey.encode (2, 0%N))) =
    map (View.C.src q) (View.C.inc q (2, 0%N)).
Proof. vm_compute. reflexivity. Qed.

Definition parallel_blocks : Source.t :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [] [] (Branch tt [9] 2 [] 2 []));
     (2, Block positive unit unit [] [(7, tt, [9])] (Return [7]))].

Example cached_search_preserves_parallel_block_rows :
  L.live_in parallel_blocks = L.live_in_spec parallel_blocks.
Proof. vm_compute. reflexivity. Qed.

Module DuplicateEdges <: CFG_INDEXED_OPS View.Q PointKey PointEdge.
  Definition entries := View.C.entries.
  Definition edges (q : View.Q.t) := View.C.edges q ++ View.C.edges q.
  Definition src := View.C.src.
  Definition dst := View.C.dst.
  Definition nodes := View.C.nodes.
  Definition out := View.C.out.
  Definition inc := View.C.inc.
End DuplicateEdges.

Module DuplicateLive := LiveCode Ops Source View.Q View.R BlockEdge PointEdge PointKey
  View.BC DuplicateEdges View.U View.SP.

Example incoming_cache_deduplicates_repeated_edge_inventory :
  DuplicateLive.incoming_table (View.R.prepare cyclic) =
    L.incoming_table (View.R.prepare cyclic).
Proof. vm_compute. reflexivity. Qed.
