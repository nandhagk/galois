(** * Scalar encoding tests

    These examples pin scalar layouts and key equality.
    For example, signed negative three has a different code from positive three.
    Builds on: Key. *)

From Stdlib Require Import Bool NArith ZArith.
From Galois.Base Require Import Key.

Local Open Scope positive_scope.

Example scalar_rejects :
  Pos.eqb (ZKeyCode.encode 3%Z) (ZKeyCode.encode (-3)%Z) = false.
Proof. vm_compute. reflexivity. Qed.

Example scalar_zero_boundary :
  (PosKeyCode.encode 1, NKeyCode.encode 0%N, NatKeyCode.encode 0%nat,
    ZKeyCode.encode 0%Z, BoolKeyCode.encode false, UnitKeyCode.encode tt) =
  (1%positive, 1%positive, 1%positive, 1%positive, 1%positive, 1%positive).
Proof. vm_compute. reflexivity. Qed.

Example positive_scalar_boundary_widths : (PosKey.bits 1, PosKey.bits 2) = (1, 2)%nat.
Proof. vm_compute. reflexivity. Qed.

Example unit_scalar_width : UnitKey.bits tt = 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* Decoder and cost APIs from BaseEncodingTest.v at 87192fe have been removed. *)
