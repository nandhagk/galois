(** * Prepared edge enumeration

    Explicit edge inventories retain duplicates through adjacency preparation.
    For example, two occurrences of false stay before true in the outgoing list.
    Builds on: Program.Cfg. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key.
From Galois.Program Require Import CfgSig Cfg.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := bool. End Prog.
Module Edge <: TYPE. Definition t := bool. End Edge.
Module Cfg <: CFG_OPS Prog BoolKeyCode Edge.
  Definition entries (p : bool) := if p then [false] else [].
  Definition edges (p : bool) := if p then [false; false; true] else [].
  Definition src (_ : bool) (_ : bool) := false.
  Definition dst (_ : bool) (_ : bool) := true.
End Cfg.
Module Prep := CfgCode Prog BoolKeyCode Edge Cfg.
Module View := PreparedCfg Prog BoolKeyCode Edge Cfg.

Example duplicate_edges : View.Adj.out (Prep.prepare true) false = [false; false; true].
Proof.
  vm_compute; reflexivity.
Qed.

(* empty_enumeration had ([], 0 ticks). Its value projection is retained. *)
Example empty_enumeration : View.Ops.edges (Prep.prepare false) = [].
Proof.
  vm_compute; reflexivity.
Qed.

(* FrameworkUtil's fw_edges_c flattened outgoing callbacks over listed nodes.
   CFG_OPS now supplies its edge inventory explicitly, and CfgCode prepares
   adjacency from that inventory. varying_price_bound, nonunit_reader_charge
   and symbolic_flatten are Cost contracts excluded from this code-only port. *)
