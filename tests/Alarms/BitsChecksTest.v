(** * Range-based bit-vector check observations

    Checks use range endpoints to decide whether an error is possible.
    For example, a positive divisor range excludes division by zero.
    Builds on: BitsChecks and the constant value domain.

    Groups:
    - [DivZeroTests] Division by a divisor range that may be zero.
    - [BoundsTests] An index checked against an array bound.
    - [NullDerefTests] A dereference of a pointer of unknown value.
    - [OverflowTests] Sums and products checked against their word width. *)

From Stdlib Require Import List ZArith Bool.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import ConstSig Const BitsLang ValueSig.
From Galois.Alarms Require Import BitsChecksSig BitsChecks.
Import List.ListNotations.

(** * Fixtures *)

(** Two constant values are equal when their widths and their numbers are equal. *)
Module WordEq.
  Definition eqb (a b : word) := Pos.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
End WordEq.
Module Values := ConstCode BitsLangCode WordEq.

(** A constant value has its number as both endpoints of its range. *)
Module Range.
  Definition range (v : Values.t) : bnd * bnd :=
    match v with
    | FVal (_, z) => (Fin z, Fin z)
    | _ => (NegInf, PosInf)
    end.
End Range.

(** A constant value has the width that it was written with. *)
Module Width.
  Definition width (v : Values.t) : option positive :=
    match v with FVal (w, _) => Some w | _ => None end.
End Width.
Module Checks := BitsChecksCode Values Range Range Width.

Module DivZeroTests.

  (** A divisor range that excludes zero raises no division alarm. *)
  Example positive_divisor_is_safe :
    Checks.may_fail DivZero [FVal (8%positive, 2%Z)] = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A divisor that is the constant zero raises a division alarm. *)
  Example zero_divisor_alarms : Checks.may_fail DivZero [FVal (8%positive, 0%Z)] = true.
  Proof. vm_compute. reflexivity. Qed.

End DivZeroTests.

Module BoundsTests.

  (** An index below its bound raises no alarm. *)
  Example index_below_bound_is_safe :
    Checks.may_fail Bounds [FVal (8%positive, 2%Z); FVal (8%positive, 3%Z)] = false.
  Proof. vm_compute. reflexivity. Qed.

  (** An index equal to its bound raises an alarm. *)
  Example index_at_bound_alarms :
    Checks.may_fail Bounds [FVal (8%positive, 3%Z); FVal (8%positive, 3%Z)] = true.
  Proof. vm_compute. reflexivity. Qed.

End BoundsTests.

Module NullDerefTests.

  (** A pointer of unknown value may be null, so it raises an alarm. *)
  Example unknown_pointer_alarms : Checks.may_fail NullDeref [FTop] = true.
  Proof. vm_compute. reflexivity. Qed.

End NullDerefTests.

Module OverflowTests.

  (** A sum that stays within its word width raises no alarm. *)
  Example sum_fits_width :
    Checks.may_fail (Overflow bvadd false) [FVal (8%positive, 2%Z); FVal (8%positive, 3%Z)] = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A sum that passes the largest value of its word width raises an alarm. *)
  Example sum_past_width_alarms :
    Checks.may_fail (Overflow bvadd false)
      [FVal (8%positive, 255%Z); FVal (8%positive, 1%Z)] = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Operands of different widths raise an alarm, even when the sum is small. *)
  Example mixed_width_sum_alarms :
    Checks.may_fail (Overflow bvadd false) [FVal (8%positive, 2%Z); FVal (4%positive, 3%Z)] = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A product that stays within its word width raises no alarm. *)
  Example product_fits_width :
    Checks.may_fail (Overflow bvmul false) [FVal (8%positive, 2%Z); FVal (8%positive, 3%Z)] = false.
  Proof. vm_compute. reflexivity. Qed.

End OverflowTests.
