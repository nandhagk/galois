(** * Scalar encoding tests

    These examples pin scalar layouts and key equality.
    For example, signed negative three has a different code from positive three.
    Builds on: Key.

    Groups:
    - ScalarTests: the codes of scalar values, including zero and the signs of integers.
    - WidthTests: the widths in bits of the scalar keys. *)

From Stdlib Require Import Bool NArith ZArith.
From Galois.Base Require Import Key.

(** * Scalar codes *)

Module ScalarTests.

  Local Open Scope positive_scope.

  (** Signed positive and negative three have different codes. *)
  Example signed_codes_differ_by_sign :
    Pos.eqb (ZKeyCode.encode 3%Z) (ZKeyCode.encode (-3)%Z) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The positive key one encodes to one. *)
  Example positive_one_encodes_to_one : PosKeyCode.encode 1 = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero as a natural number encodes to one. *)
  Example zero_nat_encodes_to_one : NKeyCode.encode 0%N = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero as a machine natural encodes to one. *)
  Example zero_natural_encodes_to_one : NatKeyCode.encode 0%nat = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Zero as an integer encodes to one. *)
  Example zero_integer_encodes_to_one : ZKeyCode.encode 0%Z = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The boolean false encodes to one. *)
  Example false_encodes_to_one : BoolKeyCode.encode false = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** The unit value encodes to one. *)
  Example unit_encodes_to_one : UnitKeyCode.encode tt = 1.
  Proof. vm_compute. reflexivity. Qed.

End ScalarTests.

(** * Widths *)

Module WidthTests.

  Local Open Scope positive_scope.

  (** The positive key one has one bit. *)
  Example positive_one_has_one_bit : PosKey.bits 1 = 1%nat.
  Proof. vm_compute. reflexivity. Qed.

  (** The positive key two has two bits. *)
  Example positive_two_has_two_bits : PosKey.bits 2 = 2%nat.
  Proof. vm_compute. reflexivity. Qed.

  (** The unit key has one bit. *)
  Example unit_key_is_one_bit : UnitKey.bits tt = 1%nat.
  Proof. vm_compute. reflexivity. Qed.

  (** The positive key encodes to itself. *)
  Example positive_key_is_identity (p : positive) : PosKeyCode.encode p = p.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unit key encodes every value to one. *)
  Example unit_key_encodes_to_one (x : unit) : UnitKeyCode.encode x = 1%positive.
  Proof.
    vm_compute. reflexivity.
  Qed.

End WidthTests.

(* BaseEncodingTest.scalar_roundtrips expects six Some results and scalar_rejects
   also expects (None, None) from bool and unit decoding. These coordinates retire
   because KEY has no decoder and core section 4 deletes decoders with no consumer.
   The signed-code comparison of scalar_rejects is checked above.
   scalar_ticks, arbitrary_component_ticks, imported_positive_scalar_cost,
   imported_unit_scalar_cost and scalar_adapter_charges retire with Cost.ticks.
   imported_positive_scalar_width and imported_unit_scalar_width are symbolic
   width laws. The concrete boundary widths above use the new nat-valued bits. *)
