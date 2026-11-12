(** * Dense dataflow observations

    A diamond graph exercises forward and backward rows and candidate checks.
    For example, a boundary at node one propagates backward to node zero.
    Builds on: Framework.Dense and Fixpoint.Worklist. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense.
Import List.ListNotations.

Module BoolOps <: WLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow := andb.
End BoolOps.

Module Prog <: TYPE. Definition t := bool. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module Diamond <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (backward : bool) := if backward then [0; 1; 2; 3] else [0].
  Definition edges (_ : bool) := [0; 1; 2; 3].
  Definition src (_ : bool) e := match e with 2 => 1 | 3 => 2 | _ => 0 end.
  Definition dst (_ : bool) e := match e with 0 => 1 | 1 => 2 | _ => 3 end.
End Diamond.
Module ForwardFlow <: FLOW_OPS Prog NatKeyCode Edge BoolOps.
  Definition dir := Forward.
  Definition boundary (_ : bool) (_ : nat) := true.
  Definition transfer (_ : bool) (_ : nat) (a : bool) := a.
End ForwardFlow.
Module BackwardFlow <: FLOW_OPS Prog NatKeyCode Edge BoolOps.
  Definition dir := Backward.
  Definition boundary (_ : bool) n := Nat.eqb n 1.
  Definition transfer (_ : bool) (_ : nat) (a : bool) := a.
End BackwardFlow.
Module F := DenseCode Prog NatKeyCode Edge Diamond BoolOps ForwardFlow.
Module B := DenseCode Prog NatKeyCode Edge Diamond BoolOps BackwardFlow.
Module P := PolicyCode BoolOps.
Module FC := CheckCode BoolOps F.
Module BC := CheckCode BoolOps B.
Module FW := WorklistCode BoolOps F P HeapCode.
Module BW := WorklistCode BoolOps B P HeapCode.
Module FR := NarrowCode BoolOps F FC.
Module BR := NarrowCode BoolOps B BC.
Module FA := CertifiedCode BoolOps F FW FC FR.
Module BA := CertifiedCode BoolOps B BW BC BR.
Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.

Example forward_seed_order :
  F.rows false = [Seed 0; Flow 0; Flow 1; Flow 2; Flow 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example backward_seed_order :
  B.rows true = [Seed 0; Seed 1; Seed 2; Seed 3; Flow 0; Flow 1; Flow 2; Flow 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_forward :
  match FA.analyze false flat 8%N with
  | Solved m => Some (map (FC.look m) [0; 1; 2; 3; 99])
  | _ => None
  end = Some [true; true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

(* At fuel 8 the old result was Some [true; true; false; false].
   The new result is None because the worklist exhausts its fuel. *)
Example backward_old_fuel :
  match BA.analyze true flat 8%N with
  | Solved m => Some (map (BC.look m) [0; 1; 2; 3])
  | _ => None
  end = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_backward_nonterminal_boundary :
  match BA.analyze true flat 12%N with
  | Solved m => Some (map (BC.look m) [0; 1; 2; 3])
  | _ => None
  end = Some [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_candidate_rejected : FC.check false PTrieCode.empty = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_exhausted :
  match FA.analyze false flat 1%N with OutOfFuel _ => true | _ => false end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_candidate_accepted :
  BC.check true (PTrieCode.set (NatKeyCode.encode 1) (1, true)
    (PTrieCode.set (NatKeyCode.encode 0) (0, true) PTrieCode.empty)) = true.
Proof.
  vm_compute; reflexivity.
Qed.
