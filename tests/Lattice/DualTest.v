(** * Dual boolean fixtures

    Reversing boolean implication makes conjunction the join.
    For example, the dual bottom is true.
    Builds on: Dual and Simple.

    Groups:
    - OrderTests: the reversed order of the dual boolean lattice.
    - JoinTests: the join and the bottom of the dual boolean lattice.
    - HeightTests: the height and the ranks of the dual boolean lattice. *)

From Stdlib Require Import Bool NArith.
From Galois.Lattice Require Import Dual Simple.

(** * Fixtures *)

(** The dual of the boolean lattice. *)
Module DualBool := DualCode BoolLatCode.

(** The dual of the boolean lattice, as a lattice module. *)
Module DualBoolLat := Dual BoolLat.

(** The height structure of the dual boolean lattice. *)
Module DualBoolHeight := DualHeight BoolLat BoolLatHeight DualBoolLat.

(** * Order *)

Module OrderTests.

  (** True lies below false in the dual order. *)
  Example dual_true_below_false : DualBool.leb true false = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** False does not lie below true in the dual order. *)
  Example dual_false_not_below_true : DualBool.leb false true = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End OrderTests.

(** * Join *)

Module JoinTests.

  (** The dual join of true and false is false. *)
  Example dual_join_of_true_and_false_is_false : DualBool.join true false = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The dual bottom is true. *)
  Example dual_bottom_is_true : DualBool.bot = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The dual join of true with itself is true. *)
  Example dual_join_of_true_with_itself_is_true : DualBool.join true true = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End JoinTests.

(** * Height *)

Module HeightTests.

  (** The dual boolean lattice has height one. *)
  Example dual_height_is_one : DualBoolHeight.height = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** True has rank zero in the dual lattice. *)
  Example dual_true_has_rank_zero : DualBoolHeight.rank true = 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** False has rank one in the dual lattice. *)
  Example dual_false_has_rank_one : DualBoolHeight.rank false = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

End HeightTests.

(* LatticeDualTest.dual_leb_ticks, dual_join_ticks and dual_callback_charges retire
   with Cost.ticks. bool_meet_contract is a proof client of the retired dictionary
   meet_laws. BoolLat supplies the meet laws used by DualBoolLat. *)
