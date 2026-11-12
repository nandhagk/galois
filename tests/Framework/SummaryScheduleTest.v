(** * Schedules for recursive summaries

    Dependency schedules expose head choices for recursive calls.
    For example, each self-dependent function needs a widening head.
    Builds on: Framework.SummarySolverTest and Fixpoint.Schedule. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import Key Trie.
From Galois.Graph Require Import Data Digraph Wto.
From Galois.Fixpoint Require Import PolicySig Schedule.
From Galois.Program Require Import CallsSig.
From Galois.Framework Require Import Summary.
From Galois.Tests.Framework Require Import SummarySolverTest.
Import List.ListNotations.

Module AllCalls <: CALLS_OPS Prog NatKeyCode NatKeyCode.
  Definition functions (_ : nat) := [0; 1].
  Definition roots (_ : nat) := [0].
  Definition sites_of (_ : nat) f := match f with 0 => [0] | 1 => [1] | _ => [] end.
  Definition caller_of (_ : nat) (site : nat) := site.
  Definition resolve (_ : nat) site := match site with 0 | 1 => [0; 1] | _ => [] end.
  Definition call_graph (_ : nat) := Digraph [] Empty.
End AllCalls.
Module SAll := SummaryCode Prog NatKeyCode NatKeyCode AllCalls Lat Body.
Module H := ScheduleCode Lat SAll DigraphCode WtoCode.
Definition is_head (pol : policy unit) n :=
  match trie_get (NatKeyCode.encode n) (heads pol) with Some _ => true | None => false end.

Example current_all_listed :
  match H.plan 0 (HeadCfg 0%N 0) tt 0 with
  | Some pol => (is_head pol 0, is_head pol 1, is_head pol 2)
  | None => (false, false, false)
  end = (true, true, false).
Proof. vm_compute; reflexivity. Qed.

Module HRecursive := ScheduleCode Lat S DigraphCode WtoCode.
Definition priority (pol : policy unit) n :=
  match trie_get (NatKeyCode.encode n) (prio pol) with Some rank => rank | None => 1%positive end.

(* The old SCC policy returned [4; 3; 3]%positive for the recursive graph.
   The dependency WTO policy returns [3; 1; 2]%positive. *)

(* The old singleton SCC policy returned (2%positive, true, false).
   The dependency WTO policy returns (1%positive, false, false). *)
