(** * Dual boolean fixtures

    Reversing boolean implication makes conjunction the join.
    For example, the dual bottom is true.
    Builds on: Dual and Simple. *)

From Stdlib Require Import Bool NArith.
From Galois.Lattice Require Import Dual Simple.
Module DualBool := DualCode BoolLatCode.
Module DualBoolLat := Dual BoolLat.
Module DualBoolHeight := DualHeight BoolLat BoolLatHeight DualBoolLat.

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

Example dual_height_client :
  (DualBoolHeight.height, DualBoolHeight.rank true, DualBoolHeight.rank false) = (1, 0, 1).
Proof.
  vm_compute. reflexivity.
Qed.

(* LatticeDualTest.dual_leb_ticks, dual_join_ticks and dual_callback_charges retire
   with Cost.ticks. bool_meet_contract is a proof client of the retired dictionary
   meet_laws. BoolLat supplies the meet laws used by DualBoolLat. *)
