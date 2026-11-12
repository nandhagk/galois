(** * Control-flow graph observations

    Preparation retains edge occurrences and their adjacency order.
    For example, a repeated edge receives distinct occurrence numbers.
    Builds on: Program.Cfg. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key.
From Galois.Program Require Import CfgSig Cfg.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := bool. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module Three <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (p : bool) := if p then [0] else [].
  Definition edges (p : bool) := if p then [0; 1; 2] else [].
  Definition src (_ : bool) e := match e with 0 => 0 | _ => 1 end.
  Definition dst (_ : bool) e := match e with 0 => 1 | 1 => 1 | _ => 2 end.
End Three.
Module Prep := CfgCode Prog NatKeyCode Edge Three.
Module View := PreparedCfg Prog NatKeyCode Edge Three.

Example repeated_occurrences : occurrences [7; 7; 7] 0 = [(7, 0); (7, 1); (7, 2)].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_occurrences : occurrences (@nil nat) 0 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example three_edges : View.Ops.edges (Prep.prepare true) = [0; 1; 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example self_loop : (Three.src true 1, Three.dst true 1) = (1, 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_node : View.Adj.out (Prep.prepare true) 9 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example no_edges : View.Ops.edges (Prep.prepare false) = [].
Proof.
  vm_compute; reflexivity.
Qed.
