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

Example imported_positive_scalar_value p : PosKeyCode.encode p = p.
Proof.
  vm_compute. reflexivity.
Qed.

Example imported_unit_scalar_value x : UnitKeyCode.encode x = 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(* BaseEncodingTest.scalar_roundtrips expects six Some results and scalar_rejects
   also expects (None, None) from bool and unit decoding. These coordinates retire
   because KEY has no decoder and core section 4 deletes decoders with no consumer.
   The signed-code comparison of scalar_rejects is checked above.
   scalar_ticks, arbitrary_component_ticks, imported_positive_scalar_cost,
   imported_unit_scalar_cost and scalar_adapter_charges retire with Cost.ticks.
   imported_positive_scalar_width and imported_unit_scalar_width are symbolic
   width laws. The concrete boundary widths above use the new nat-valued bits. *)
