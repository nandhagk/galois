(** * Summary solver observations

    Recursive call graphs propagate local effects to their callers.
    For example, a caller of a recursive pair receives the pair's local effect.

    Groups:
    - [RecursiveTests] A recursive pair and its callers give their local effects, and bottom is
      rejected.
    - [ChainTests] A chain of calls with two sites gives its ordinary, site-sensitive results.
    - [ScheduleTests] Two policies give checked post-solutions and the same joined lookups.

    Builds on: Framework.Summary and Fixpoint.Certified. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Graph Require Import Data.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CallsSig.
From Galois.Framework Require Import SummarySig Summary.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := nat. End Prog.

(** Booleans as a widening lattice, ordered by implication and joined by or. *)
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

(** Two recursive functions, 0 and 1 in program 0, and a call graph with a self-call. *)
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
  Definition calls p := flat_map (fun f =>
    flat_map (fun site => map (pair site) (resolve p site)) (sites_of p f)) (functions p).
End Calls.

(** The local effect is true at the function that the program selects, and calls pass the value through. *)
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

(** The policy with empty tries, unit parameter and bound 0. *)
Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** The lookups of the keys xs in the summary that the program p solves to, if it is solved within fuel. *)
Definition observe p fuel xs := match A.analyze p flat fuel with
  | Solved m => Some (map (C.look m) xs)
  | _ => None
  end.

(** * Recursive *)

Module RecursiveTests.

  (** The recursive pair gives true at its two functions and false at the third. *)
  Example recursive_pair_effect : observe 0 8%N [0; 1; 2] = Some [true; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A caller of the recursive pair gives true, which it receives from the pair. *)
  Example caller_of_pair_inherits_effect : observe 1 8%N [0; 1; 2; 3] =
    Some [true; true; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A single function at the boundary gives false at both of its keys. *)
  Example single_function_boundary_false : observe 2 2%N [0; 1] = Some [false; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A program without functions gives false at its only key. *)
  Example empty_summary_false : observe 3 1%N [0] = Some [false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The check rejects the empty candidate for program 1. *)
  Example bottom_candidate_rejected : C.check 1 PTrieCode.empty = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End RecursiveTests.

(** * Chain *)

Module ChainTests.

  (** Natural numbers ordered by the usual order, with 0 as bottom and max as join. *)
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

  (** A chain of four functions, where function 0 calls function 1 at site 0 and function 3 at site 3. *)
  Module Chain <: CALLS_OPS Prog NatKeyCode NatKeyCode.
    Definition functions (_ : nat) := [0; 1; 2; 3].
    Definition roots (_ : nat) := [0].
    Definition sites_of (_ : nat) f := match f with 0 => [0; 3] | 1 => [1] | 2 => [2] | _ => [] end.
    Definition caller_of (_ : nat) site := if Nat.eqb site 3 then 0 else site.
    Definition resolve (_ : nat) site := match site with 0 => [1] | 1 => [2] | 2 | 3 => [3] | _ => [] end.
    Definition call_graph (_ : nat) := Digraph [] Empty.
    Definition calls p := flat_map (fun f =>
      flat_map (fun site => map (pair site) (resolve p site)) (sites_of p f)) (functions p).
  End Chain.

  (** The body whose call transfer adds the site and the callee to the incoming value. *)
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

  (** The site-sensitive results of program 0 are 13, 11, 7 and 1 at the four functions. *)
  Example site_sensitive_results :
    match CA.analyze 0 flat 16%N with
    | Solved m => Some (map (CC.look m) [0; 1; 2; 3])
    | _ => None
    end = Some [13; 11; 7; 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

End ChainTests.

(** * Schedules *)

Module ScheduleTests.

  (** A body whose local effect is false and whose call transfer negates the incoming value. *)
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

  (** The first policy ranks function 0 first. *)
  Definition first_zero : policy unit := Policy unit
    (PTrieCode.set (NatKeyCode.encode 0) 1%positive
      (PTrieCode.set (NatKeyCode.encode 1) 2%positive PTrieCode.empty)) PTrieCode.empty tt 0.

  (** The second policy ranks function 1 first. *)
  Definition first_one : policy unit := Policy unit
    (PTrieCode.set (NatKeyCode.encode 0) 2%positive
      (PTrieCode.set (NatKeyCode.encode 1) 1%positive PTrieCode.empty)) PTrieCode.empty tt 0.

  (** The lookups of keys 0 and 1 under the anti-body policy, if it is solved within fuel. *)
  Definition anti_observe pol := match AntiA.analyze 0 pol 16%N with
    | Solved m => Some (map (AntiC.look m) [0; 1])
    | _ => None
    end.

  (** Whether the solution under the policy pol passes the check for program 0. *)
  Definition anti_checked pol := match AntiA.analyze 0 pol 16%N with
    | Solved m => AntiC.check 0 m
    | _ => false
    end.

  (** The solution under each policy is a checked post-solution. *)
  Example both_schedules_checked :
    (anti_checked first_zero, anti_checked first_one) = (true, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The lookups of keys 0, 1 and 2 under the policy pol, if it is solved within fuel. *)
  Definition joining_observe pol := match A.analyze 0 pol 8%N with
    | Solved m => Some (map (C.look m) [0; 1; 2])
    | _ => None
    end.

  (** Both policies give the same lookups for the joining body. *)
  Example joining_lookups_agree :
    (joining_observe first_zero, joining_observe first_one) =
      (Some [true; true; false], Some [true; true; false]).
  Proof.
    vm_compute; reflexivity.
  Qed.

End ScheduleTests.
