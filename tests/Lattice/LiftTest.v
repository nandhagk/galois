(** * Top-lift fixtures

    Unknown absorbs joins and narrowing can descend from it.
    For example, narrowing Unknown toward Elem false gives Elem false.
    Builds on: WithTop and Simple. *)

From Stdlib Require Import NArith.
From Galois.Lattice Require Import WithTop Simple.
Module TopBool := WithTopCode BoolLatCode.

Example lift_positive :
  TopBool.join (Elem false) (Elem true) = Elem true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_negative :
  TopBool.leb Unknown (Elem true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example lift_unknown :
  TopBool.join (Elem false) Unknown = Unknown.
Proof.
  vm_compute; reflexivity.
Qed.

(* The narrowing example in LatticeLiftTest.v at 87192fe has no current operation. *)

Example lift_bottom :
  TopBool.bot = Elem false.
Proof.
  vm_compute; reflexivity.
Qed.

(* Cost and height examples are in LatticeLiftTest.v at 87192fe. *)
