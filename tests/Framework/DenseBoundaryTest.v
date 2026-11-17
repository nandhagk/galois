(** * Dense loop and boundary observations

    Loop, singleton and empty graphs exercise seeds in both directions.
    For example, an empty graph yields the bottom value.

    Groups:
    - [LoopTests] A loop gives true forward, and backward it gives true only before its boundary
      node.
    - [SingletonTests] A one-node graph gives its seed, runs out of fuel, or stays false without
      one.
    - [UnlistedTests] A boundary at a node outside the graph adds no row.

    Builds on: Framework.Dense and Framework.DenseTest. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense.
From Galois.Tests.Framework Require Import DenseTest.
Import List.ListNotations.

(** * Fixtures *)

(** Shapes are numbered by nat, and each shape is a graph of three edges or of none. *)
Module Shape <: TYPE. Definition t := nat. End Shape.

(** Shape 0 has entries 0 to 2 and edges 0 to 2. Shape 2 has no entries and no edges. *)
Module Graph <: CFG_OPS Shape NatKeyCode Edge.
  Definition entries p := if Nat.eqb p 2 then [] else if Nat.eqb p 0 then [0; 1; 2] else [0].
  Definition edges p := if Nat.eqb p 0 then [0; 1; 2] else [].
  Definition src (_ : nat) e := if Nat.eqb e 0 then 0 else 1.
  Definition dst (_ : nat) e := if Nat.eqb e 2 then 2 else 1.
End Graph.

(** Forward flow with boundary true and identity transfer. *)
Module Forward <: FLOW_OPS Shape NatKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : nat) (_ : nat) := true.
  Definition transfer (_ : nat) (_ : nat) (a : bool) := a.
End Forward.

(** Backward flow whose boundary is true only at node 1, with identity transfer. *)
Module Backward <: FLOW_OPS Shape NatKeyCode Edge BoolOps.
  Definition dir := Backward.
  Definition boundary (_ : nat) n := Nat.eqb n 1.
  Definition transfer (_ : nat) (_ : nat) (a : bool) := a.
End Backward.

Module F := DenseCode Shape NatKeyCode Edge Graph BoolOps Forward.
Module B := DenseCode Shape NatKeyCode Edge Graph BoolOps Backward.
Module FC := CheckCode BoolOps F.
Module BC := CheckCode BoolOps B.
Module FW := WorklistCode BoolOps F P HeapCode.
Module BW := WorklistCode BoolOps B P HeapCode.
Module FR := NarrowCode BoolOps F FC.
Module BR := NarrowCode BoolOps B BC.
Module FA := CertifiedCode BoolOps F FW FC FR.
Module BA := CertifiedCode BoolOps B BW BC BR.

(** * Loops *)

Module LoopTests.

  (** The forward analysis of the loop gives true at nodes 0, 1 and 2. *)
  Example forward_loop_values :
    match FA.analyze 0 flat 8%N with
    | Solved m => Some (map (FC.look m) [0; 1; 2])
    | _ => None
    end = Some [true; true; true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The backward analysis of the loop gives true at nodes 0 and 1, and false at node 2. *)
  Example backward_loop_values :
    match BA.analyze 0 flat 8%N with
    | Solved m => Some (map (BC.look m) [0; 1; 2])
    | _ => None
    end = Some [true; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

End LoopTests.

(** * Singletons *)

Module SingletonTests.

  (** The forward seed of the singleton graph is true at node 0 and false at node 1. *)
  Example forward_singleton_seed :
    match FA.analyze 1 flat 2%N with
    | Solved m => Some (map (FC.look m) [0; 1])
    | _ => None
    end = Some [true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With fuel 1 the backward analysis of the singleton runs out and gives no solution. *)
  Example backward_singleton_runs_out_at_one :
    match BA.analyze 1 flat 1%N with
    | Solved m => Some (map (BC.look m) [0])
    | _ => None
    end = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Without its boundary seed the backward singleton is false at node 0. *)
  Example unseeded_singleton_is_false :
    match BA.analyze 1 flat 2%N with
    | Solved m => Some (map (BC.look m) [0])
    | _ => None
    end = Some [false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty graph gives false at node 0. *)
  Example empty_graph_gives_false :
    match FA.analyze 2 flat 1%N with
    | Solved m => Some (map (FC.look m) [0])
    | _ => None
    end = Some [false].
  Proof.
    vm_compute; reflexivity.
  Qed.

End SingletonTests.

(** * Unlisted *)

Module UnlistedTests.

  (** A boundary at node 99, which the graph does not list, adds no row to the check. *)
  Module Unlisted <: FLOW_OPS Shape NatKeyCode Edge BoolOps.
    Definition dir := Forward.
    Definition boundary (_ : nat) n := Nat.eqb n 99.
    Definition transfer (_ : nat) (_ : nat) (a : bool) := a.
  End Unlisted.

  Module U := DenseCode Shape NatKeyCode Edge Graph BoolOps Unlisted.
  Module UC := CheckCode BoolOps U.

  (** The check accepts the empty candidate for shape 1, so the unlisted boundary is not a row. *)
  Example unlisted_boundary_not_a_row : UC.check 1 PTrieCode.empty = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End UnlistedTests.
