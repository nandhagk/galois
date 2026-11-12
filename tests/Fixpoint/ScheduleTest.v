(** * Schedule construction observations

    A self-dependent row exercises graph construction and widening cuts.
    For example, a self edge needs a configured head.
    Builds on: Fixpoint.Schedule and Fixpoint.WorklistSelfTest. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Wto.
From Galois.Fixpoint Require Import PolicySig Schedule.
From Galois.Tests.Fixpoint Require Import WorklistTest WorklistSelfTest.
Import List.ListNotations.

Module H := ScheduleCode BoolOps Self DigraphCode WtoCode.
Definition plain : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.
Definition head : head_cfg := HeadCfg 0%N 0.

Example self_graph_occurrences :
  (verts (H.dep_graph tt), succs (H.dep_graph tt) 1%positive) =
    ([1%positive], [1%positive; 1%positive; 1%positive;
      1%positive; 1%positive; 1%positive]).
Proof. vm_compute; reflexivity. Qed.

Example self_cut_requires_head : H.cuts tt plain = false.
Proof. vm_compute; reflexivity. Qed.

Example planned_self_cut :
  match H.plan tt head tt 0 with
  | Some pol => H.cuts tt pol
  | None => false
  end = true.
Proof. vm_compute; reflexivity. Qed.
