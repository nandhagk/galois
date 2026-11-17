(** * Prepared edge enumeration

    Explicit edge inventories keep their duplicates through adjacency preparation.
    For example, two occurrences of false stay before true in the outgoing list.

    Groups:
    - Adjacency: outgoing lists keep duplicate edges in their order.
    - Enumeration: a program without entries has no edges.

    Builds on: Program.Cfg. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key.
From Galois.Program Require Import CfgSig Cfg.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := bool. End Prog.
Module Edge <: TYPE. Definition t := bool. End Edge.

(** A CFG whose edge inventory lists the labels false, false and true, all from false to true. *)
Module Cfg <: CFG_OPS Prog BoolKeyCode Edge.
  Definition entries (p : bool) := if p then [false] else [].
  Definition edges (p : bool) := if p then [false; false; true] else [].
  Definition src (_ : bool) (_ : bool) := false.
  Definition dst (_ : bool) (_ : bool) := true.
End Cfg.

Module Prep := CfgCode Prog BoolKeyCode Edge Cfg.
Module View := PreparedCfg Prog BoolKeyCode Edge Cfg.

(** * Adjacency *)

Module AdjacencyTests.

  (** Preparing keeps every copy of a duplicate edge, in the order given. *)
  Example duplicate_edges_kept :
    View.Adj.out (Prep.prepare true) false = [false; false; true].
  Proof.
    vm_compute; reflexivity.
  Qed.

End AdjacencyTests.

(** * Enumeration *)

Module EnumerationTests.

  (** A program without entries enumerates no edges. *)
  Example no_entries_no_edges :
    View.Ops.edges (Prep.prepare false) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

End EnumerationTests.
