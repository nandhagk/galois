(** * Dominator certificate observations

    These cases retain parent-map observations and supply independent low-high orders.
    For example, the diamond places its join between its two incoming branches.
    Builds on: graph fixtures, preparation and the dominator code tower. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph DomSig DomProducer Dom.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.
Open Scope positive_scope.

Definition parent_map (pairs : list (positive * positive)) : ptrie positive :=
  fold_right (fun pair acc => PTrieCode.set (fst pair) (snd pair) acc) Empty pairs.

Example accepts_line :
  DomCode.check (DigraphCode.prepare Line.graph) 1 (parent_map Line.parents) [1; 2; 3; 4] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_diamond :
  DomCode.check (DigraphCode.prepare Diamond.graph) 1
    (parent_map Diamond.parents) [1; 2; 4; 3] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition dense_join_graph := fixture_graph [1; 2; 3; 4; 5; 6; 7]
  [(1, 2); (1, 3); (1, 4); (2, 5); (2, 6); (3, 5); (3, 6); (4, 5); (4, 6);
    (5, 7); (6, 7)].

Example accepts_dense_join_edges :
  DomCode.check (DigraphCode.prepare dense_join_graph) 1
    (parent_map [(2, 1); (3, 1); (4, 1); (5, 1); (6, 1); (7, 1)])
    [1; 2; 5; 7; 6; 3; 4] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example accepts_order_omitting_unreachable_source :
  DomCode.check (DigraphCode.prepare Unreachable.graph) 1
    (parent_map Unreachable.parents) [1; 2; 3; 4] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_row_without_source_keeps_flags :
  dom_edges_from_fast (DigraphCode.prepare Unreachable.graph) 1
    (parent_map Unreachable.parents) (dom_positions [1; 2; 3; 4]) Empty (Some Empty) 5 =
    Some Empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example nonempty_row_without_source_rejects :
  dom_edges_from_fast (DigraphCode.prepare Unreachable.graph) 1
    (parent_map Unreachable.parents) Empty Empty (Some Empty) 1 = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejected_edge_row_stays_rejected :
  dom_edges_from_fast (DigraphCode.prepare Diamond.graph) 1
    (parent_map Diamond.parents) (dom_positions [1; 2; 4; 3]) Empty None 1 = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_wrong_line_parent :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map [(2, 1); (3, 1); (4, 3)]) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_parent_cycle :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map [(2, 3); (3, 2); (4, 3)]) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_missing_binding :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map [(2, 1); (4, 3)]) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_unknown_child :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (PTrieCode.set 9 1 (parent_map Line.parents)) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_order_without_high_witness :
  DomCode.check (DigraphCode.prepare Diamond.graph) 1
    (parent_map Diamond.parents) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_duplicate_order_entry :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map Line.parents) [1; 2; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** The reused read rejects a repeated vertex before rebuilding the parent map. *)
Example rejects_repeated_vertex_within_budget :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (parent_map Line.parents) [1; 2; 2; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** A valid order still reaches and rejects an invalid parent map. *)
Example rejects_root_parent_after_valid_read :
  DomCode.check (DigraphCode.prepare Line.graph) 1
    (PTrieCode.set 1 4 (parent_map Line.parents)) [1; 2; 3; 4] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example ancestor_queries :
  let t := DomCode.tree (DigraphCode.prepare Line.graph) 1
    (parent_map Line.parents) [1; 2; 3; 4] in
  (DomCode.dominates_b t 1 4, DomCode.dominates_b t 2 4,
    DomCode.dominates_b t 4 1, DomCode.dominates_b t 9 4) =
    (true, true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example simple_lt_line_parents :
  dom_lt_parents (DigraphCode.prepare Line.graph) 1 = parent_map Line.parents.
Proof.
  vm_compute. reflexivity.
Qed.

Example simple_lt_diamond_parents :
  dom_lt_parents (DigraphCode.prepare Diamond.graph) 1 = parent_map Diamond.parents.
Proof.
  vm_compute. reflexivity.
Qed.

Example producer_certificates_accept :
  forallb (fun g =>
    let p := DigraphCode.prepare g in
    let '(m, o) := DomCode.build p 1 in DomCode.check p 1 m o)
    [Line.graph; Diamond.graph; JoinLoop.graph; NestedLoop.graph; SelfLoop.graph;
      Irreducible.graph; Singleton.graph; Unreachable.graph] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition derived_sources_graph := fixture_graph [1; 2; 3; 4; 5; 6; 7]
  [(1, 2); (1, 3); (2, 4); (3, 5); (4, 6); (5, 6); (6, 7)].

Example producer_derives_sources_from_sibling_subtrees :
  let p := DigraphCode.prepare derived_sources_graph in
  let '(m, o) := DomCode.build p 1 in DomCode.check p 1 m o = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The backedge evaluates a linked chain during reverse semidominator settlement. *)
Definition compression_loop_graph := fixture_graph [1; 2; 3; 4; 5; 6; 7; 8]
  [(1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 7); (7, 8); (8, 2)].

Example producer_compresses_long_backedge_path :
  DomCode.build (DigraphCode.prepare compression_loop_graph) 1 =
    (parent_map [(2, 1); (3, 2); (4, 3); (5, 4); (6, 5); (7, 6); (8, 7)],
      [1; 2; 3; 4; 5; 6; 7; 8]).
Proof.
  vm_compute. reflexivity.
Qed.

Definition compression_chain :=
  dom_lt_link (dom_lt_link (dom_lt_link (DomLtLinks Empty Empty []) 2%N 1%N)
    3%N 2%N) 4%N 3%N.

Definition compression_tied_semis :=
  PTrieCode.set (dom_lt_key 4%N) 1%N
    (PTrieCode.set (dom_lt_key 3%N) 1%N
      (PTrieCode.set (dom_lt_key 2%N) 1%N Empty)).

(** Equal stored semidominators still select the fresh label at every unwind frame. *)
Example compression_prefers_fresh_label_on_ties :
  snd (dom_lt_eval 4%N compression_tied_semis compression_chain 4%N) = 4%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** Exhaustion just after the first score prefetch preserves the exact partial links. *)
Example compression_preserves_exhausted_prefix :
  dom_lt_eval 1%N compression_tied_semis compression_chain 4%N =
    (DomLtLinks (lt_shortcut compression_chain) (lt_label compression_chain)
      (LtEval 4%N :: lt_operations compression_chain), 4%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example producer_retains_direct_root_parent_observations :
  map (fun g => fst (DomCode.build (DigraphCode.prepare g) 1))
    [Line.graph; Diamond.graph; JoinLoop.graph; NestedLoop.graph; SelfLoop.graph;
      Irreducible.graph; Singleton.graph; Unreachable.graph] =
  map parent_map [Line.parents; Diamond.parents; JoinLoop.parents; NestedLoop.parents;
    SelfLoop.parents; Irreducible.parents; Singleton.parents; Unreachable.parents].
Proof.
  vm_compute. reflexivity.
Qed.

Example producer_missing_root_row :
  DomCode.build (DigraphCode.prepare (fixture_graph [1; 4] [(1, 4)])) 2 = (Empty, []).
Proof.
  vm_compute. reflexivity.
Qed.

Example producer_listed_empty_row :
  DomCode.build (DigraphCode.prepare (fixture_graph [1; 4] [(1, 4)])) 4 = (Empty, [4]).
Proof.
  vm_compute. reflexivity.
Qed.

Example producer_ignores_unlisted_wide_successor :
  DomCode.build (DigraphCode.prepare (fixture_graph [1; 2] [(1, 2); (2, 1024)])) 1 =
    (parent_map [(2, 1)], [1; 2]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Narrower width guards retain rejection of foreign order entries and parent keys. *)
Example rejects_unlisted_wide_candidate_keys :
  let g := DigraphCode.prepare (fixture_graph [1; 2] [(1, 2); (2, 1024)]) in
  (DomCode.check g 1 (parent_map [(1024, 1)]) [1; 1024],
    DomCode.check g 1 (parent_map [(2, 1024)]) [1; 2]) = (false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example paired_positions_and_subtree_sizes :
  let o := [1; 2; 3; 4] in
  let info := dom_info_sizes (parent_map Line.parents) o (dom_positions o) in
  map (fun v => trie_get v info) [1; 2; 3; 4; 9] =
    [Some (0%N, 4%N); Some (1%N, 3%N); Some (2%N, 2%N); Some (3%N, 1%N); None].
Proof.
  vm_compute. reflexivity.
Qed.

Example rejects_noncontiguous_child_subtree :
  let g := DigraphCode.prepare
    (fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4)]) in
  let m := parent_map [(2, 1); (3, 1); (4, 2)] in
  let o := [1; 2; 3; 4] in
  (dom_map_check_known (dom_scan g) 1 m o,
    dom_info_sizes_ok m (dom_info_sizes m o (dom_positions o)) o,
    DomCode.check g 1 m o) = (true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.
