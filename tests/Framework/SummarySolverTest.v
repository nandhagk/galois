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

Module NatLat <: WLATTICE_OPS.
  Definition t := nat.
  Definition leb := Nat.leb.
  Definition bot := 0.
  Definition is_bot n := Nat.eqb n 0.
  Definition join := Nat.max.
  Definition wparam := unit.
  Definition widen (_ : unit) := Nat.max.
  Definition narrow := Nat.min.
End NatLat.
Module Chain <: CALLS_OPS Prog NatKeyCode NatKeyCode.
  Definition functions (_ : nat) := [0; 1; 2; 3].
  Definition roots (_ : nat) := [0].
  Definition sites_of (_ : nat) f := match f with 0 => [0; 3] | 1 => [1] | 2 => [2] | _ => [] end.
  Definition caller_of (_ : nat) site := if Nat.eqb site 3 then 0 else site.
  Definition resolve (_ : nat) site := match site with 0 => [1] | 1 => [2] | 2 | 3 => [3] | _ => [] end.
  Definition call_graph (_ : nat) := Digraph [] Empty.
End Chain.
Module ChainBody <: BODY_OPS Prog NatKeyCode NatKeyCode NatLat.
  Definition local (_ : nat) f := match f with 2 => 2 | 3 => 1 | _ => 0 end.
  Definition via_call (_ : nat) site callee a := a + S site + callee.
  Definition entry (_ _ _ : nat) := 0.
End ChainBody.
Module CS := SummaryCode Prog NatKeyCode NatKeyCode Chain NatLat ChainBody.
Module CP := PolicyCode NatLat.
Module CC := CheckCode NatLat CS.
Module CW := WorklistCode NatLat CS CP HeapCode.
Module CR := NarrowCode NatLat CS CC.
Module CA := CertifiedCode NatLat CS CW CC CR.

(* At fuel 8 the old ordinary result was Some [13; 11; 7; 1].
   The new certified worklist returns None at that fuel. *)

Example site_sensitive_ordinary_results :
  match CA.analyze 0 flat 16%N with
  | Solved m => Some (map (CC.look m) [0; 1; 2; 3])
  | _ => None
  end = Some [13; 11; 7; 1].
Proof. vm_compute; reflexivity. Qed.

Module AntiBody <: BODY_OPS Prog NatKeyCode NatKeyCode Lat.
  Definition local (_ _ : nat) := false.
  Definition via_call (_ _ _ : nat) (a : bool) := negb a.
  Definition entry (_ _ _ : nat) := false.
End AntiBody.
Module AntiS := SummaryCode Prog NatKeyCode NatKeyCode Calls Lat AntiBody.
Module AntiC := CheckCode Lat AntiS.
Module AntiW := WorklistCode Lat AntiS P HeapCode.
Module AntiR := NarrowCode Lat AntiS AntiC.
Module AntiA := CertifiedCode Lat AntiS AntiW AntiC AntiR.
Definition first_zero : policy unit := Policy unit
  (PTrieCode.set (NatKeyCode.encode 0) 1%positive
    (PTrieCode.set (NatKeyCode.encode 1) 2%positive PTrieCode.empty)) PTrieCode.empty tt 0.
Definition first_one : policy unit := Policy unit
  (PTrieCode.set (NatKeyCode.encode 0) 2%positive
    (PTrieCode.set (NatKeyCode.encode 1) 1%positive PTrieCode.empty)) PTrieCode.empty tt 0.
Definition anti_observe pol := match AntiA.analyze 0 pol 16%N with
  | Solved m => Some (map (AntiC.look m) [0; 1])
  | _ => None
  end.

(* The old policy-ordered round produced ([true; false], [false; true]).
   The certified worklist produces (Some [true; false], Some [true; false]). *)

Definition anti_checked pol := match AntiA.analyze 0 pol 16%N with
  | Solved m => AntiC.check 0 m
  | _ => false
  end.

Example both_schedules_are_checked_post_solutions :
  (anti_checked first_zero, anti_checked first_one) = (true, true).
Proof. vm_compute; reflexivity. Qed.

Definition joining_observe pol := match A.analyze 0 pol 8%N with
  | Solved m => Some (map (C.look m) [0; 1; 2])
  | _ => None
  end.

Example selected_joining_lookups :
  (joining_observe first_zero, joining_observe first_one) =
    (Some [true; true; false], Some [true; true; false]).
Proof. vm_compute; reflexivity. Qed.
