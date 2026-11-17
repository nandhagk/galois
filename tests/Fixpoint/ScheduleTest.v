(** * Schedule construction observations

    A self-dependent row exercises graph construction and widening cuts.
    For example, a self edge needs a configured head.

    Groups:
    - [GraphTests] The vertices and successors of the dependency graph.
    - [CutTests] A self edge is cut only when the policy configures a head.

    Builds on: Fixpoint.Schedule and Fixpoint.WorklistSelfTest. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Digraph Wto.
From Galois.Fixpoint Require Import PolicySig Schedule.
From Galois.Tests.Fixpoint Require Import WorklistTest WorklistSelfTest.
Import List.ListNotations.

(** * Fixtures *)

Module H := ScheduleCode BoolOps Self DigraphCode WtoCode.

(** A policy with no heads. *)
Definition plain : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** A head with no delay. *)
Definition head : head_cfg := HeadCfg 0%N 0.

(** * Graph *)

Module GraphTests.

  (** The self-dependent row is the only vertex. *)
  Example self_graph_vertices : verts (H.dep_graph tt) = [1%positive].
  Proof. vm_compute; reflexivity. Qed.

  (** The self edge of row 1 appears once for each of its six occurrences. *)
  Example self_graph_successors :
    succs (H.dep_graph tt) 1%positive = [1%positive; 1%positive; 1%positive;
      1%positive; 1%positive; 1%positive].
  Proof. vm_compute; reflexivity. Qed.

End GraphTests.

(** * Cut *)

Module CutTests.

  (** Without a configured head, the self edge is not cut. *)
  Example self_cut_requires_head : H.cuts tt plain = false.
  Proof. vm_compute; reflexivity. Qed.

  (** The planned policy for the configured head cuts the self edge. *)
  Example planned_self_cut :
    match H.plan tt head tt 0 with
    | Some pol => H.cuts tt pol
    | None => false
    end = true.
  Proof. vm_compute; reflexivity. Qed.

End CutTests.
