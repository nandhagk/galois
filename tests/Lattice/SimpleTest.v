(** * Simple and lifted lattice fixtures

    These examples check boolean and unit lattice operations and lifted bottom.
    For example, [Some false] lies above [None].
    Builds on: Simple and WithBot. *)

From Stdlib Require Import Bool List.
From Galois.Lattice Require Import Simple WithBot.
Import List.ListNotations.

Module LiftedBool := WithBotCode BoolLatCode.

Example boolean_table :
  map (fun xy => let '(x, y) := xy in
    (BoolLatCode.leb x y, BoolLatCode.join x y))
    [(false, false); (false, true); (true, false); (true, true)] =
  [(true, false); (true, true); (false, true); (true, true)].
Proof.
  vm_compute. reflexivity.
Qed.

Example unit_boundary :
  (UnitLatCode.leb tt tt, UnitLatCode.join tt tt) = (true, tt).
Proof.
  vm_compute. reflexivity.
Qed.

Example lift_none_none :
  (LiftedBool.leb None None, LiftedBool.join None None) = (true, None).
Proof.
  vm_compute. reflexivity.
Qed.

Example lift_none_some :
  (LiftedBool.leb None (Some false), LiftedBool.leb (Some false) None,
   LiftedBool.join None (Some false)) = (true, false, Some false).
Proof.
  vm_compute. reflexivity.
Qed.

Example lift_some_some :
  (LiftedBool.leb (Some true) (Some false),
   LiftedBool.join (Some false) (Some true)) = (false, Some true).
Proof.
  vm_compute. reflexivity.
Qed.

(* Widening, narrowing, cost, height and gamma examples are in
   LatticeSimpleTest.v at 87192fe. *)
