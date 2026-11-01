(** * Whole indexed memory search examples

    These examples observe preparation and search on small memory graphs.
    For example, an unvisited phi still causes both operand calls during indexing.
    Builds on: the complete counted clobber-search model. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryRawNext AnalysesAuditMemoryIndex AnalysesAuditMemorySearch
  AnalysesAuditMemoryWalkIndex
  AnalysesAuditMemoryClobbersSource.
Import List.ListNotations.

(** * Search fixtures *)

Definition audit_whole_graph : Graph.t bool unit :=
  Graph.Make [false] [false; true] (fun node => if node then [] else [tt])
    (fun _ => false) (fun _ => true).

Definition audit_whole_node (node : bool) := (encode bool_encoding node, [tt]).

Definition audit_whole_edge (_ : unit) := (encode unit_encoding tt, [tt]).

Definition audit_whole_effects (_ : unit) := ([@MemoryRead unit (MemoryRegions [])], [tt]).

Definition audit_whole_out (node : bool) := (Graph.out audit_whole_graph node, [tt]).

Definition audit_whole_target (_ : unit) := (true, [tt]).

Definition audit_whole_operand (_ : bool) (_ : option unit) :=
  (Some (@MemoryLive bool unit), [tt]).

Definition audit_whole_before (_ : unit) (_ : nat) := (Some (@MemoryLive bool unit), [tt]).

Definition audit_whole_memory : memory_graph bool unit :=
  MemoryGraph [true] [MemoryLive; MemoryPhi true] (fun _ => MemoryLive)
    (fun _ _ => Some MemoryLive) (fun _ => MemoryLive) (fun _ _ => Some MemoryLive).

Definition audit_whole_clobber :=
  audit_memory_clobbers_source_counted bool_encoding audit_whole_node audit_whole_edge
    audit_whole_edge audit_whole_out audit_whole_target audit_whole_effects audit_whole_operand
    audit_whole_before audit_whole_graph audit_whole_memory (MemoryRegions []) MemoryLive
    2%positive.

Fixpoint audit_whole_operand_count {N E T CE SE IE OE BE}
    (events : list (audit_raw_next_event N E T CE SE IE OE BE)) : nat :=
  match events with
  | [] => 0
  | AuditRawOperand _ _ _ _ :: rest => S (audit_whole_operand_count rest)
  | _ :: rest => audit_whole_operand_count rest
  end.

Fixpoint audit_whole_index_operand_count {N E T CN CE SE PE BE}
    (events : list (audit_walk_index_event N E T CN CE SE PE BE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoryIndexNil :: rest => audit_whole_index_operand_count rest
  | AuditMemoryIndexPut _ _ _ _ body _ :: rest => audit_whole_operand_count body +
    audit_whole_index_operand_count rest
  end.

(** Two rows include the unvisited phi and both of its operand calls. *)
Example audit_whole_unvisited_phi_materialized :
  clobber_roots (audit_clobbers_source_result audit_whole_clobber) = [MemoryLive] /\
  length (audit_walk_index_rows (audit_clobbers_source_index audit_whole_clobber)) = 3 /\
  audit_whole_index_operand_count
    (audit_walk_index_rows (audit_clobbers_source_index audit_whole_clobber)) = 2.
Proof.
  vm_compute.
  repeat split; reflexivity.
Qed.

Definition audit_whole_unlisted_memory : memory_graph bool unit :=
  MemoryGraph [true] [] (fun _ => MemoryLive) (fun _ _ => Some MemoryLive)
    (fun _ => MemoryLive) (fun _ _ => Some MemoryLive).

(** An unlisted phi is an indexed terminal even though its raw adapter has operands. *)
Example audit_whole_unlisted_phi_is_terminal :
  let run := audit_memory_clobbers_source_counted bool_encoding audit_whole_node audit_whole_edge
    audit_whole_edge audit_whole_out audit_whole_target audit_whole_effects audit_whole_operand
    audit_whole_before audit_whole_graph audit_whole_unlisted_memory (MemoryRegions [])
    (MemoryPhi true) 2%positive in
  clobber_roots (audit_clobbers_source_result run) = [MemoryPhi true].
Proof.
  vm_compute.
  reflexivity.
Qed.

(** A repeated successor is retained as a cut and marks the search incomplete. *)
Example audit_search_duplicate_successor_is_cut :
  let enc := fun p : positive => (p, @nil unit) in
  let next := fun p : positive => (if Pos.eqb p 1%positive then [2%positive; 2%positive] else [],
    @nil unit) in
  let state := fst (audit_memory_search_run enc next 4%positive (memory_search_start 1%positive)) in
  memory_search_complete state = false /\ memory_search_todo state = [].
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** With one unit of fuel, an unprocessed successor remains in the worklist. *)
Example audit_search_one_step_leaves_successor :
  let enc := fun p : positive => (p, @nil unit) in
  let next := fun _ : positive => ([2%positive], @nil unit) in
  let state := fst (audit_memory_search_run enc next 1%positive (memory_search_start 1%positive)) in
  memory_search_todo state = [2%positive].
Proof.
  vm_compute.
  reflexivity.
Qed.

(** An empty worklist takes no transition even with positive fuel. *)
Example audit_search_empty_has_no_steps :
  let enc := fun p : positive => (p, @nil unit) in
  let next := fun _ : positive => ([], @nil unit) in
  audit_memory_search_steps (snd (audit_memory_search_run enc next 8%positive
    (MemorySearchState [] CollectionsMap.Map.empty 0 CollectionsFinSet.FinSet.empty true))) = 0.
Proof.
  reflexivity.
Qed.

(** A duplicate successor produces three steps and records its actual nested source work. *)
Example audit_search_duplicate_source_work :
  let enc := fun p : positive => (p, @nil unit) in
  let next := fun p : positive => (if Pos.eqb p 1%positive then [2%positive; 2%positive] else [],
    @nil unit) in
  let events := snd (audit_memory_search_run enc next 4%positive
    (memory_search_start 1%positive)) in
  (audit_memory_search_steps events,
    audit_memory_search_source_work (@length unit) (@length unit) events,
    audit_memory_search_primitive_work (@length unit) (@length unit) events) = (3, 160, 136).
Proof.
  vm_compute.
  reflexivity.
Qed.
