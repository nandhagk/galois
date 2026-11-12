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

(* The old dual height had bound 1 and ranked true and false as 0 and 1.
   No dual height constructor is exported. *)
