(** * Summary solver observations

    Recursive call graphs propagate local effects to their callers.
    For example, a caller of a recursive pair receives the pair's local effect.
    Builds on: Framework.Summary and Fixpoint.Certified. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Graph Require Import Data.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CallsSig.
From Galois.Framework Require Import SummarySig Summary.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := nat. End Prog.
Module Lat <: WLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow := andb.
End Lat.
Module Calls <: CALLS_OPS Prog NatKeyCode NatKeyCode.
  Definition functions p := match p with 0 => [0; 1] | 1 => [0; 1; 2] | 2 => [0] | _ => [] end.
  Definition roots p := if Nat.eqb p 3 then [] else [0].
  Definition sites_of p f := if Nat.ltb f (length (functions p)) then
    if Nat.ltb p 2 then [f] else [] else [].
  Definition caller_of (_ : nat) (site : nat) := site.
  Definition resolve p site := match p, site with
    | 0, 0 => [1] | 0, 1 => [0]
    | 1, 0 => [1] | 1, 1 => [2] | 1, 2 => [1]
    | _, _ => [] end.
  Definition call_graph (_ : nat) := Digraph [] Empty.
End Calls.
Module Body <: BODY_OPS Prog NatKeyCode NatKeyCode Lat.
  Definition local p f := Nat.eqb f (if Nat.eqb p 0 then 1 else 2).
  Definition via_call (_ _ _ : nat) (a : bool) := a.
  Definition entry (_ _ _ : nat) := false.
End Body.
Module S := SummaryCode Prog NatKeyCode NatKeyCode Calls Lat Body.
Module P := PolicyCode Lat.
Module C := CheckCode Lat S.
Module W := WorklistCode Lat S P HeapCode.
Module R := NarrowCode Lat S C.
Module A := CertifiedCode Lat S W C R.
Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.
Definition observe p fuel xs := match A.analyze p flat fuel with
  | Solved m => Some (map (C.look m) xs)
  | _ => None
  end.

Example recursive_pair : observe 0 8%N [0; 1; 2] = Some [true; true; false].
Proof. vm_compute; reflexivity. Qed.

Example recursive_pair_and_caller : observe 1 8%N [0; 1; 2; 3] =
  Some [true; true; true; false].
Proof. vm_compute; reflexivity. Qed.

Example single_function_boundary : observe 2 2%N [0; 1] = Some [false; false].
Proof. vm_compute; reflexivity. Qed.

Example empty_summary : observe 3 1%N [0] = Some [false].
Proof. vm_compute; reflexivity. Qed.

Example recursive_bottom_rejected : C.check 1 PTrieCode.empty = false.
Proof. vm_compute; reflexivity. Qed.
