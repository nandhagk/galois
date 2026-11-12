(** * Encoded equality tests

    Equality tests distinguish matching, different and boundary keys.
    For example, lists compare by their injective serialized codes.
    Builds on: Key and Code. *)

From Stdlib Require Import Bool List NArith.
From Galois.Base Require Import Key Code.
Import List.ListNotations.

Module NatList := ListKeyCode NatKeyCode.

Local Open Scope positive_scope.

Example equality_accepts : NatList.eqb [1; 2]%nat [1; 2]%nat = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_rejects : NatList.eqb [1; 2]%nat [2; 1]%nat = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_empty_boundary : NatList.eqb [] [] = true.
Proof.
  vm_compute. reflexivity.
Qed.

(* The cost example is in BaseEqTest.v at 87192fe. *)

Example key_positive : PosKeyCode.eqb 1 1 = true.
Proof. vm_compute. reflexivity. Qed.

Example key_negative : PosKeyCode.eqb 1 2 = false.
Proof. vm_compute. reflexivity. Qed.
