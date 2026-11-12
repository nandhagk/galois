(** * Dual boolean fixtures

    Reversing boolean implication makes conjunction the join.
    For example, the dual bottom is true.
    Builds on: Dual and Simple. *)

From Stdlib Require Import Bool NArith.
From Galois.Lattice Require Import Dual Simple.
Module DualBool := DualCode BoolLatCode.

Example dual_positive : DualBool.leb true false = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_negative : DualBool.leb false true = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_join : DualBool.join true false = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_boundary : (DualBool.bot, DualBool.join true true) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

(* Cost and height examples are in LatticeDualTest.v at 87192fe. *)
