(** * Strict SSA edge observations

    Prepared queries retain dominating edge occurrences in ancestor order.
    For example, neither arm of a diamond dominates its join.
    Builds on: Program.Ssa and graph fixtures. *)

From Stdlib Require Import List PArith Bool.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data Digraph Dom.
From Galois.Program Require Import CfgSig SsaSig Ssa.
Import List.ListNotations.
Open Scope positive_scope.
Definition fixture_graph (vertices : list positive) (edges : list (positive * positive)) : digraph :=
  Digraph vertices (fold_right (fun u tr =>
    PTrieCode.set u (map snd (filter (fun e => Pos.eqb (fst e) u) edges)) tr) Empty vertices).

Module Diamond.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
  Definition parents := [(2, 1); (3, 1); (4, 1)].
End Diamond.
Module Line.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
  Definition parents := [(2, 1); (3, 2); (4, 3)].
End Line.
Module NestedLoop.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
  Definition parents := Line.parents.
End NestedLoop.


Definition parent_map (pairs : list (positive * positive)) : ptrie positive :=
  fold_right (fun pair acc => PTrieCode.set (fst pair) (snd pair) acc) Empty pairs.

Definition diamond_edges : list (positive * positive) := [(1, 2); (1, 3); (2, 4); (3, 4)].
Definition diamond_graph := DigraphCode.prepare Diamond.graph.
Definition diamond_tree := DomCode.tree diamond_graph 1 (parent_map Diamond.parents) [1; 2; 4; 3].
Definition diamond_context :=
  make_strict_context fst snd diamond_edges diamond_graph Diamond.roots diamond_tree.

Example diamond_left_arm : dominating_edges_in diamond_context 2 = [(1, 2)].
Proof. vm_compute; reflexivity. Qed.
Example diamond_join : dominating_edges_in diamond_context 4 = [].
Proof. vm_compute; reflexivity. Qed.
Example diamond_entry : dominating_edges_in diamond_context 1 = [].
Proof. vm_compute; reflexivity. Qed.
Example diamond_unknown : dominating_edges_in diamond_context 9 = [].
Proof. vm_compute; reflexivity. Qed.

Definition line_edges : list (positive * positive) := [(1, 2); (2, 3); (3, 4)].
Definition line_graph := DigraphCode.prepare Line.graph.
Definition line_tree := DomCode.tree line_graph 1 (parent_map Line.parents) [1; 2; 3; 4].
Definition line_context := make_strict_context fst snd line_edges line_graph Line.roots line_tree.
Example line_ancestor_order :
  dominating_edges_in line_context 4 = [(1, 2); (2, 3); (3, 4)].
Proof. vm_compute; reflexivity. Qed.

Definition loop_edges : list (positive * positive) := [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
Definition loop_graph := DigraphCode.prepare NestedLoop.graph.
Definition loop_tree := DomCode.tree loop_graph 1 (parent_map NestedLoop.parents) [1; 2; 3; 4].
Definition loop_context := make_strict_context fst snd loop_edges loop_graph NestedLoop.roots loop_tree.
Example loop_preheader_edge : dominating_edges_in loop_context 3 = [(1, 2); (2, 3)].
Proof. vm_compute; reflexivity. Qed.

Definition repeated_graph := DigraphCode.prepare (fixture_graph [1; 2] [(1, 2); (1, 2)]).
Definition repeated_tree := DomCode.tree repeated_graph 1 (parent_map [(2, 1)]) [1; 2].
Definition repeated_edges : list ((unit * nat) * (positive * positive)) :=
  [((tt, 0%nat), (1, 2)); ((tt, 1%nat), (1, 2))].
Definition repeated_context := make_strict_context (fun e => fst (snd e)) (fun e => snd (snd e))
  repeated_edges repeated_graph [1] repeated_tree.
Example repeated_query_is_conservative : dominating_edges_in repeated_context 2 = [].
Proof. vm_compute; reflexivity. Qed.
Example empty_walk_boundary : strict_walk_step diamond_context (None, []) = inr [].
Proof. vm_compute; reflexivity. Qed.

Module ProgramType <: TYPE. Definition t := bool. End ProgramType.
Module OpType <: TYPE. Definition t := unit. End OpType.
Module EdgeKey := PairKeyCode NatKeyCode NatKeyCode.
Module DiamondCfg <: CFG_INDEXED_OPS ProgramType NatKeyCode EdgeKey.
  Definition entries (_ : bool) := [1%nat].
  Definition edges (_ : bool) := [(1%nat, 2%nat); (1%nat, 3%nat); (2%nat, 4%nat); (3%nat, 4%nat)].
  Definition src (_ : bool) (e : EdgeKey.t) := fst e.
  Definition dst (_ : bool) (e : EdgeKey.t) := snd e.
  Definition nodes (_ : bool) := [1%nat; 2%nat; 3%nat; 4%nat].
  Definition out (p : bool) (n : nat) := filter (fun e => Nat.eqb (src p e) n) (edges p).
  Definition inc (p : bool) (n : nat) := filter (fun e => Nat.eqb (dst p e) n) (edges p).
End DiamondCfg.
Module DiamondData <: SSA_DATA ProgramType NatKeyCode EdgeKey NatKeyCode OpType OpType.
  Definition tables (_ : bool) : ssa_tables nat EdgeKey.t nat unit unit := SsaTables [0%nat; 1%nat] [] []
    (PTrieCode.set (NatKeyCode.encode 0%nat) (Op tt [])
      (PTrieCode.set (NatKeyCode.encode 1%nat) (Param 4%nat 0%nat) Empty))
    Empty 1%nat Empty Empty
    (PTrieCode.set (EdgeKey.encode (1%nat, 2%nat)) [(tt, [0%nat])] Empty).
End DiamondData.
Module DiamondSsa := SsaCode ProgramType NatKeyCode EdgeKey DiamondCfg NatKeyCode
  OpType OpType DiamondData.
Example diamond_guard : DiamondSsa.guards true (1%nat, 2%nat) = [(tt, [0%nat])].
Proof. vm_compute; reflexivity. Qed.
Example diamond_parameter : DiamondSsa.def true 1%nat = Param 4%nat 0%nat.
Proof. vm_compute; reflexivity. Qed.
