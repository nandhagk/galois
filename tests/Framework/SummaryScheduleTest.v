(** * Schedules for recursive summaries

    Dependency schedules expose head choices for recursive calls.
    For example, each self-dependent function needs a widening head.

    Groups:
    - Heads: the schedule marks the recursive functions as heads.
    - Edges: a self-call gives one call edge for each of its resolved targets.
    - Reach: the prepared search reaches the nodes of a cyclic graph as expected.

    Builds on: Framework.SummarySolverTest and Fixpoint.Schedule. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import Key Trie.
From Galois.Graph Require Import Data Digraph Wto SearchSig Search.
From Galois.Fixpoint Require Import PolicySig Schedule.
From Galois.Program Require Import CallsSig.
From Galois.Framework Require Import Summary.
From Galois.Tests.Framework Require Import SummarySolverTest.
Import List.ListNotations.

(** * Fixtures *)

(** Two functions whose sites 0 and 1 both resolve to functions 0 and 1, so each may call itself. *)
Module AllCalls <: CALLS_OPS Prog NatKeyCode NatKeyCode.
  Definition functions (_ : nat) := [0; 1].
  Definition roots (_ : nat) := [0].
  Definition sites_of (_ : nat) f := match f with 0 => [0] | 1 => [1] | _ => [] end.
  Definition caller_of (_ : nat) (site : nat) := site.
  Definition resolve (_ : nat) site := match site with 0 | 1 => [0; 1] | _ => [] end.
  Definition call_graph (_ : nat) := Digraph [] Empty.
  Definition calls p := flat_map (fun f =>
    flat_map (fun site => map (pair site) (resolve p site)) (sites_of p f)) (functions p).
End AllCalls.

Module SAll := SummaryCode Prog NatKeyCode NatKeyCode AllCalls Lat Body.
Module H := ScheduleCode Lat SAll DigraphCode WtoCode.

(** Whether the policy pol makes the node n a head. *)
Definition is_head (pol : policy unit) n :=
  match trie_get (NatKeyCode.encode n) (heads pol) with Some _ => true | None => false end.

Module HRecursive := ScheduleCode Lat S DigraphCode WtoCode.

(** The priority of the node n under the policy pol, which is 1 when it has none. *)
Definition priority (pol : policy unit) n :=
  match trie_get (NatKeyCode.encode n) (prio pol) with Some rank => rank | None => 1%positive end.

(** A cyclic graph on nodes 1, 2 and 3, with the edges 1 to 2, 2 to 3 and 3 to 2. *)
Definition recursive_graph := Digraph [1; 2; 3]%positive
  (PTrieCode.set 1%positive [2%positive]
    (PTrieCode.set 2%positive [3%positive] (PTrieCode.set 3%positive [2%positive] Empty))).

(** Whether the node v is reached from the node u by the prepared search. *)
Definition reachable_from (u v : positive) :=
  existsb (Pos.eqb v) (entered (prepared_search_trace (DigraphCode.prepare recursive_graph) [u])).

(** * Heads *)

Module HeadTests.

  (** The first plan marks nodes 0 and 1 as heads and node 2 as not a head. *)
  Example all_listed_heads :
    match H.plan 0 (HeadCfg 0%N 0) tt 0 with
    | Some pol => (is_head pol 0, is_head pol 1, is_head pol 2)
    | None => (false, false, false)
    end = (true, true, false).
  Proof.
    vm_compute; reflexivity.
  Qed.

End HeadTests.

(** * Edges *)

Module EdgeTests.

  (** Function 0 calls itself at site 0, so the call edges are to 0 and to 1. *)
  Example self_call_edges :
    call_edges (AllCalls.resolve 0) (AllCalls.sites_of 0 0) = [CallEdge 0 0; CallEdge 0 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

End EdgeTests.

(** * Reach *)

Module ReachTests.

  (** The prepared search from each node of the cyclic graph reaches the nodes 1, 2 and 3 as stated. *)
  Example prepared_reach_sets :
    map (fun f => map (reachable_from f) [1; 2; 3]%positive) [1; 2; 3]%positive =
      [[true; true; true]; [false; true; true]; [false; true; true]].
  Proof.
    vm_compute; reflexivity.
  Qed.

End ReachTests.
