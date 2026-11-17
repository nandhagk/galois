(** * Strict SSA edge observations

    Prepared queries retain dominating edge occurrences in ancestor order.
    For example, neither arm of a diamond dominates its join.

    Groups:
    - Diamond: only the entry edge of the left arm dominates; the join and the entry have none.
    - Line: the ancestors of the last node of a line come in order.
    - Loop: the preheader edges dominate the loop header.
    - Repeated: repeated edges give no dominator, and an empty walk stops at the boundary.
    - Ssa: the SSA tables record the guard of an edge and the parameter definition.

    Builds on: Program.Ssa and graph fixtures. *)

From Stdlib Require Import List PArith Bool.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data Digraph Dom.
From Galois.Program Require Import CfgSig SsaSig Ssa.
Import List.ListNotations.
Open Scope positive_scope.

(** * Fixtures *)

(** A digraph on the given vertices with the given edges, in their order. *)
Definition fixture_graph (vertices : list positive) (edges : list (positive * positive)) : digraph :=
  Digraph vertices (fold_right (fun u tr =>
    PTrieCode.set u (map snd (filter (fun e => Pos.eqb (fst e) u) edges)) tr) Empty vertices).

(** A map from each child to its parent, given as the list of pairs. *)
Definition parent_map (pairs : list (positive * positive)) : ptrie positive :=
  fold_right (fun pair acc => PTrieCode.set (fst pair) (snd pair) acc) Empty pairs.

(** A diamond with root 1, edges 1 to 2 and 1 to 3, and both arms joining at 4. *)
Module Diamond.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
  Definition parents := [(2, 1); (3, 1); (4, 1)].
End Diamond.

(** A line 1, 2, 3, 4 with root 1. *)
Module Line.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
  Definition parents := [(2, 1); (3, 2); (4, 3)].
End Line.

(** A line whose last edge returns from 4 to 1, with the loop 2 and 3 inside it. *)
Module NestedLoop.
  Definition roots := [1].
  Definition graph := fixture_graph [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
  Definition parents := Line.parents.
End NestedLoop.

(** The edges of the diamond. *)
Definition diamond_edges : list (positive * positive) := [(1, 2); (1, 3); (2, 4); (3, 4)].

(** The prepared diamond, with its dominator tree. *)
Definition diamond_graph := DigraphCode.prepare Diamond.graph.
Definition diamond_tree := DomCode.tree diamond_graph 1 (parent_map Diamond.parents) [1; 2; 4; 3].

(** The strict context of the diamond. *)
Definition diamond_context :=
  make_strict_context fst snd diamond_edges diamond_graph Diamond.roots diamond_tree.

(** * Diamond *)

Module DiamondTests.

  (** The edge from 1 to 2 dominates node 2. *)
  Example left_arm_edge_dominates :
    dominating_edges_in diamond_context 2 = [(1, 2)].
  Proof. vm_compute; reflexivity. Qed.

  (** Neither arm dominates the join 4, so no edge dominates it. *)
  Example join_has_no_dominating_edge :
    dominating_edges_in diamond_context 4 = [].
  Proof. vm_compute; reflexivity. Qed.

  (** The entry 1 has no dominating edge. *)
  Example entry_has_no_dominating_edge :
    dominating_edges_in diamond_context 1 = [].
  Proof. vm_compute; reflexivity. Qed.

  (** A node that the diamond does not have has no dominating edge. *)
  Example unknown_node_has_no_edge :
    dominating_edges_in diamond_context 9 = [].
  Proof. vm_compute; reflexivity. Qed.

End DiamondTests.

(** * Line *)

Module LineTests.

  (** The line edges are 1 to 2, 2 to 3 and 3 to 4 in the line's own order. *)
  Definition line_edges : list (positive * positive) := [(1, 2); (2, 3); (3, 4)].
  Definition line_graph := DigraphCode.prepare Line.graph.
  Definition line_tree := DomCode.tree line_graph 1 (parent_map Line.parents) [1; 2; 3; 4].

  (** The strict context of the line. *)
  Definition line_context := make_strict_context fst snd line_edges line_graph Line.roots line_tree.

  (** The dominating edges of node 4 are its ancestors' edges, from the root onward. *)
  Example ancestors_in_order :
    dominating_edges_in line_context 4 = [(1, 2); (2, 3); (3, 4)].
  Proof. vm_compute; reflexivity. Qed.

End LineTests.

(** * Loop *)

Module LoopTests.

  (** The loop edges are those of the nested loop, with the back edge 4 to 1. *)
  Definition loop_edges : list (positive * positive) := [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
  Definition loop_graph := DigraphCode.prepare NestedLoop.graph.
  Definition loop_tree := DomCode.tree loop_graph 1 (parent_map NestedLoop.parents) [1; 2; 3; 4].

  (** The strict context of the nested loop. *)
  Definition loop_context := make_strict_context fst snd loop_edges loop_graph NestedLoop.roots loop_tree.

  (** The edges 1 to 2 and 2 to 3 dominate the loop node 3. *)
  Example preheader_edges_dominate_header :
    dominating_edges_in loop_context 3 = [(1, 2); (2, 3)].
  Proof. vm_compute; reflexivity. Qed.

End LoopTests.

(** * Repeated *)

Module RepeatedTests.

  (** Two copies of the edge from 1 to 2 give no dominating edge for node 2. *)
  Definition repeated_graph := DigraphCode.prepare (fixture_graph [1; 2] [(1, 2); (1, 2)]).
  Definition repeated_tree := DomCode.tree repeated_graph 1 (parent_map [(2, 1)]) [1; 2].
  Definition repeated_edges : list ((unit * nat) * (positive * positive)) :=
    [((tt, 0%nat), (1, 2)); ((tt, 1%nat), (1, 2))].
  Definition repeated_context := make_strict_context (fun e => fst (snd e)) (fun e => snd (snd e))
    repeated_edges repeated_graph [1] repeated_tree.

  (** Duplicate edges are not reported as dominating, so the answer is conservative. *)
  Example repeated_edges_give_no_dominator :
    dominating_edges_in repeated_context 2 = [].
  Proof. vm_compute; reflexivity. Qed.

  (** An empty walk from no node takes the boundary step with an empty result. *)
  Example empty_walk_step_is_empty :
    strict_walk_step diamond_context (None, []) = inr [].
  Proof. vm_compute; reflexivity. Qed.

End RepeatedTests.

(** * Ssa *)

Module SsaTests.

  (** The program type of the SSA fixture, with booleans as programs. *)
  Module ProgramType <: TYPE. Definition t := bool. End ProgramType.

  (** The operation type of the SSA fixture, with a single unit operation. *)
  Module OpType <: TYPE. Definition t := unit. End OpType.

  (** Edges of the SSA fixture are pairs of nat nodes. *)
  Module EdgeKey := PairKeyCode NatKeyCode NatKeyCode.

  (** The SSA fixture's CFG: the diamond on nodes 1 to 4, with node 1 as its entry. *)
  Module DiamondCfg <: CFG_INDEXED_OPS ProgramType NatKeyCode EdgeKey.
    Definition entries (_ : bool) := [1%nat].
    Definition edges (_ : bool) := [(1%nat, 2%nat); (1%nat, 3%nat); (2%nat, 4%nat); (3%nat, 4%nat)].
    Definition src (_ : bool) (e : EdgeKey.t) := fst e.
    Definition dst (_ : bool) (e : EdgeKey.t) := snd e.
    Definition nodes (_ : bool) := [1%nat; 2%nat; 3%nat; 4%nat].
    Definition out (p : bool) (n : nat) := filter (fun e => Nat.eqb (src p e) n) (edges p).
    Definition inc (p : bool) (n : nat) := filter (fun e => Nat.eqb (dst p e) n) (edges p).
  End DiamondCfg.

  (** The SSA tables of the diamond: value 1 is a parameter of 4, and edge 1 to 2 has one guard. *)
  Module DiamondData <: SSA_DATA ProgramType NatKeyCode EdgeKey NatKeyCode OpType OpType.
    Definition tables (_ : bool) : ssa_tables nat EdgeKey.t nat unit unit :=
      SsaTables [0%nat; 1%nat] [] []
        (PTrieCode.set (NatKeyCode.encode 0%nat) (Op tt [])
          (PTrieCode.set (NatKeyCode.encode 1%nat) (Param 4%nat 0%nat) Empty))
        Empty 1%nat Empty Empty
        (PTrieCode.set (EdgeKey.encode (1%nat, 2%nat)) [(tt, [0%nat])] Empty).
  End DiamondData.

  Module DiamondSsa := SsaCode ProgramType NatKeyCode EdgeKey DiamondCfg NatKeyCode
    OpType OpType DiamondData.

  (** The edge from 1 to 2 has the guard of the unit operation over value 0. *)
  Example edge_guard_recorded :
    DiamondSsa.guards true (1%nat, 2%nat) = [(tt, [0%nat])].
  Proof. vm_compute; reflexivity. Qed.

  (** Value 1 is defined as the parameter 0 of node 4. *)
  Example parameter_definition_recorded :
    DiamondSsa.def true 1%nat = Param 4%nat 0%nat.
  Proof. vm_compute; reflexivity. Qed.

End SsaTests.
