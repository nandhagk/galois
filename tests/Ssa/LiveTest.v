(** * Indexed liveness examples

    Reverse searches distinguish uses, kills and cyclic paths before grouping block entries.
    For example, a read of a variable in its own assignment stays live before that assignment.

    Groups:
    - [LiveRowTests] The live rows of small functions.
    - [KillTests] Whether the parallel edges between two points kill a variable.
    - [EntryTableTests] The entry table that groups block entries.
    - [EncodingReuseTests] The search helpers reuse the point encodings they are given.
    - [CachedPredecessorTests] Predecessors that come from the cached incoming table.
    - [CachedSearchTests] Cached search agrees with its specification.
    - [DuplicateEdgeTests] A repeated edge inventory.

    Builds on: Ssa.Live and Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key Trie.
From Galois.Program Require Import CfgSig.
From Galois.Ssa Require Import Lang LiveSig Present Live.
Import List.ListNotations.
Local Open Scope positive_scope.

(** * Fixtures *)

(** The test operations, whose values are units. *)
Module Ops <: OPS.
  Definition K := unit.
  Definition G := unit.
  Definition C := unit.
  Definition eval (_ : unit) (_ : list unit) : option unit := None.
  Definition test (_ : unit) (_ : list unit) : option bool := None.
  Definition mov := tt.
End Ops.

(** A search that has seen nothing, has nothing to visit and has found nothing. *)
Definition fresh_search : live_state (positive * N)%type :=
  {| live_seen := @Empty unit; live_todo := []; live_done := [] |}.

(** The source functions of the examples. *)
Module Source.
  Definition t := func positive unit unit.
End Source.

(** The presentation of the source functions. *)
Module View := PresentT Ops UnitKeyT UnitKeyT.

(** The liveness module of the presentation. *)
Module L := LiveCode Ops Source View.Q View.R BlockEdge PointEdge PointKey
  View.BC View.C View.U View.SP.

(** A loop on block 2 that reads variable 9 and returns the variable 7. *)
Definition cyclic : Source.t :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [] [] (Jump 2 []));
     (2, Block positive unit unit [] [(7, tt, [9])] (Branch tt [7] 2 [] 3 []));
     (3, Block positive unit unit [] [] (Return [7]))].

(** A block that only jumps to itself, so its live row is empty. *)
Definition unused_cycle : Source.t :=
  Func positive unit unit 1 [] [(1, Block positive unit unit [] [] (Jump 1 []))].

(** A function with two parameters, whose block 2 reads the variables 9, 3 and 10. *)
Definition entry_and_inside : Source.t :=
  Func positive unit unit 1 [9; 10]
    [(1, Block positive unit unit [] [(2, tt, [9])] (Jump 2 []));
     (2, Block positive unit unit [] [(3, tt, [9]); (4, tt, [3; 10])] (Return [4]))].

(** * Live rows *)

Module LiveRowTests.

  (** A use of variable 9 in a block that does not define it is live on entry. *)
  Definition straight : Source.t :=
    Func positive unit unit 1 [9]
      [(1, Block positive unit unit [] [(2, tt, [9])] (Return [2]))].

  Example use_is_live_until_its_definition :
    L.live_in straight = [(1, [9])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A variable read in its own assignment is live on entry, even when it is read twice. *)
  Definition same_variable : Source.t :=
    Func positive unit unit 1 [9]
      [(1, Block positive unit unit [] [(9, tt, [9; 9])] (Return [9]))].

  Example read_in_own_assignment_is_live_on_entry :
    L.live_in same_variable = [(1, [9])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A block parameter is bound at entry, so it is not live on entry. *)
  Definition parameter : Source.t :=
    Func positive unit unit 1 []
      [(1, Block positive unit unit [9] [] (Return [9]))].

  Example parameter_binding_is_not_live_on_entry :
    L.live_in parameter = [(1, [])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The loop terminates, and each block has the variables that are live at its entry. *)
  Example loop_block_has_its_live_variables :
    L.live_in cyclic = [(1, [9]); (2, [9]); (3, [7])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  Example unused_cycle_has_empty_row :
    L.live_in unused_cycle = [(1, [])].
  Proof.
    vm_compute. reflexivity.
  Qed.

End LiveRowTests.

(** * Kills *)

Module KillTests.

  (** A parallel edge that does not kill the variable lets it propagate. *)
  Example non_killing_parallel_edge_lets_value_propagate :
    live_killed (live_kill_add 1 2 [] (live_kill_add 1 2 [9] Empty)) 1 2 9 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** When every parallel edge kills the variable, the kill holds. *)
  Example all_parallel_edges_kill_the_value :
    live_killed (live_kill_add 1 2 [9; 8] (live_kill_add 1 2 [9] Empty)) 1 2 9 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End KillTests.

(** * Entry table *)

Module EntryTableTests.

  (** The entry table of entry_and_inside, which records the entry point of each block. *)
  Definition entry_query := View.R.prepare entry_and_inside.

  Definition entry_entries := L.entry_table entry_query (View.BC.nodes entry_query).

  (** The entry point of block 1 is recorded for block 1. *)
  Example block_one_entry_is_recorded :
    trie_get (PointKey.encode (1, 0%N)) entry_entries = Some 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The entry point of block 2 is recorded for block 2. *)
  Example block_two_entry_is_recorded :
    trie_get (PointKey.encode (2, 0%N)) entry_entries = Some 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An internal point of block 2 is not recorded as an entry. *)
  Example internal_point_is_not_an_entry :
    trie_get (PointKey.encode (2, 1%N)) entry_entries = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Grouping an internal point adds nothing to the row of its block. *)
  Example group_entry_skips_internal_point :
    L.group_entry entry_entries 10 (2, 1%N) (L.group_entry entry_entries 9 (2, 0%N) Empty) =
      PTrieCode.set 2 [9] Empty.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EntryTableTests.

(** * Encoding reuse *)

Module EncodingReuseTests.

  (** Seeding the search reuses the point encoding that it is given. *)
  Example seed_reuses_point_encoding :
    live_seed PointKey.encode (2, 3%N) 9 Empty =
      live_seed_spec PointKey.encode (2, 3%N) 9 Empty.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Discovery reuses the point encoding that it is given. *)
  Example discovery_reuses_point_encoding :
    live_discover PointKey.encode (2, 3%N) fresh_search =
      live_discover_spec PointKey.encode (2, 3%N) fresh_search.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The prepared function whose predecessors are added, and the point that they lead to. *)
  Definition inside_query := View.R.prepare entry_and_inside.

  Definition inside_point := (2, 2%N).

  (** Adding predecessors reuses the point encodings that the presentation gives. *)
  Example predecessors_reuse_point_encodings :
    L.add_predecessors inside_query (L.reverse_kills inside_query) 9 inside_point
      (View.C.inc inside_query inside_point) fresh_search =
    L.add_predecessors_spec inside_query (L.reverse_kills inside_query) 9 inside_point
      (View.C.inc inside_query inside_point) fresh_search.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EncodingReuseTests.

(** * Cached predecessors *)

Module CachedPredecessorTests.

  (** The point of block 1 that the cached edges come from. *)
  Definition cached_source := (1, 0%N).

  (** A cached edge from the source whose kill set holds variable 9. *)
  Definition killing_nine :=
    LiveEdge cached_source (PointKey.encode cached_source) (PTrieCode.set 9 tt Empty).

  (** A cached edge from the source whose kill set holds variables 9 and 8. *)
  Definition killing_nine_and_eight :=
    LiveEdge cached_source (PointKey.encode cached_source)
      (PTrieCode.set 9 tt (PTrieCode.set 8 tt Empty)).

  (** A cached edge from the source that kills nothing. *)
  Definition clear_edge := LiveEdge cached_source (PointKey.encode cached_source) Empty.

  (** The predecessors found for variable 9 at point (2, 0) when the cache holds these edges. *)
  Definition cached_found (edges : list (live_edge (positive * N)%type)) :=
    live_done (L.cached_predecessors
      (PTrieCode.set (PointKey.encode (2, 0%N)) edges Empty) 9 (2, 0%N) fresh_search).

  (** One cached edge that does not kill the variable lets it propagate to block 1. *)
  Example one_clear_cached_edge_propagates :
    cached_found [killing_nine; clear_edge] = [cached_source].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Cached parallel edges that all kill the variable stop its propagation. *)
  Example cached_killing_edges_stop_propagation :
    cached_found [killing_nine; killing_nine_and_eight] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A predecessor reached by two equal cached edges is found once. *)
  Example cached_repeated_predecessor_is_found_once :
    cached_found [clear_edge; clear_edge] = [cached_source].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The cached incoming table keeps the predecessors that the presentation gives. *)
  Example cache_keeps_presented_predecessors :
    let q := View.R.prepare cyclic in
    map live_pred (index_row (L.incoming_table q) (PointKey.encode (2, 0%N))) =
      map (View.C.src q) (View.C.inc q (2, 0%N)).
  Proof.
    vm_compute. reflexivity.
  Qed.

End CachedPredecessorTests.

(** * Cached search *)

Module CachedSearchTests.

  (** Two blocks that both branch to block 2 on a live variable. *)
  Definition parallel_blocks : Source.t :=
    Func positive unit unit 1 [9]
      [(1, Block positive unit unit [] [] (Branch tt [9] 2 [] 2 []));
       (2, Block positive unit unit [] [(7, tt, [9])] (Return [7]))].

  (** Cached grouping gives the live rows of its specification. *)
  Example cached_grouping_matches_spec :
    L.live_in entry_and_inside = L.live_in_spec entry_and_inside.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Cached search gives the live rows of its specification on the loop. *)
  Example cached_search_matches_spec_on_loop :
    L.live_in cyclic = L.live_in_spec cyclic.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Cached search gives the live rows of its specification on an empty cycle. *)
  Example cached_search_matches_spec_on_empty_cycle :
    L.live_in unused_cycle = L.live_in_spec unused_cycle.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Cached search gives the live rows of its specification on parallel blocks. *)
  Example cached_search_matches_spec_on_parallel_blocks :
    L.live_in parallel_blocks = L.live_in_spec parallel_blocks.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CachedSearchTests.

(** * Duplicate edges *)

Module DuplicateEdgeTests.

  (** The view whose every edge is listed twice. *)
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

  (** A repeated edge inventory gives the same incoming table as the original. *)
  Example repeated_edge_inventory_gives_same_incoming_table :
    DuplicateLive.incoming_table (View.R.prepare cyclic) =
      L.incoming_table (View.R.prepare cyclic).
  Proof.
    vm_compute. reflexivity.
  Qed.

End DuplicateEdgeTests.
