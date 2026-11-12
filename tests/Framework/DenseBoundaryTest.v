(** * Dense loop and boundary observations

    Loop, singleton and empty graphs exercise seeds in both directions.
    For example, an empty graph yields the bottom value.
    Builds on: Framework.Dense and Framework.DenseTest. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense.
From Galois.Tests.Framework Require Import DenseTest.
Import List.ListNotations.

Module Shape <: TYPE. Definition t := nat. End Shape.
Module Graph <: CFG_OPS Shape NatKeyCode Edge.
  Definition entries p := if Nat.eqb p 2 then [] else if Nat.eqb p 0 then [0; 1; 2] else [0].
  Definition edges p := if Nat.eqb p 0 then [0; 1; 2] else [].
  Definition src (_ : nat) e := if Nat.eqb e 0 then 0 else 1.
  Definition dst (_ : nat) e := if Nat.eqb e 2 then 2 else 1.
End Graph.
Module Forward <: FLOW_OPS Shape NatKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : nat) (_ : nat) := true.
  Definition transfer (_ : nat) (_ : nat) (a : bool) := a.
End Forward.
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

Example loop_forward :
  match FA.analyze 0 flat 8%N with
  | Solved m => Some (map (FC.look m) [0; 1; 2])
  | _ => None
  end = Some [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_backward :
  match BA.analyze 0 flat 8%N with
  | Solved m => Some (map (BC.look m) [0; 1; 2])
  | _ => None
  end = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_seed :
  match FA.analyze 1 flat 2%N with
  | Solved m => Some (map (FC.look m) [0; 1])
  | _ => None
  end = Some [true; false].
Proof.
  vm_compute; reflexivity.
Qed.

(* At fuel 1 the old result was Some [false]. The new result is None. *)
Example no_boundary_singleton_old_fuel :
  match BA.analyze 1 flat 1%N with
  | Solved m => Some (map (BC.look m) [0])
  | _ => None
  end = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example no_boundary_singleton :
  match BA.analyze 1 flat 2%N with
  | Solved m => Some (map (BC.look m) [0])
  | _ => None
  end = Some [false].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_rows :
  match FA.analyze 2 flat 1%N with
  | Solved m => Some (map (FC.look m) [0])
  | _ => None
  end = Some [false].
Proof.
  vm_compute; reflexivity.
Qed.

Module Unlisted <: FLOW_OPS Shape NatKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : nat) n := Nat.eqb n 99.
  Definition transfer (_ : nat) (_ : nat) (a : bool) := a.
End Unlisted.
Module U := DenseCode Shape NatKeyCode Edge Graph BoolOps Unlisted.
Module UC := CheckCode BoolOps U.

Example unlisted_boundary_is_not_a_row : UC.check 1 PTrieCode.empty = true.
Proof.
  vm_compute; reflexivity.
Qed.
