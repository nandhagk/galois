(** * Range-based bit-vector check observations

    Checks use range endpoints to decide whether an error is possible.
    For example, a positive divisor range excludes division by zero.
    Builds on: BitsChecks and the constant value domain. *)

From Stdlib Require Import List ZArith Bool.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import ConstSig Const BitsLang ValueSig.
From Galois.Alarms Require Import BitsChecksSig BitsChecks.
Import List.ListNotations.

Module WordEq.
  Definition eqb (a b : word) := Pos.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
End WordEq.
Module Values := ConstCode BitsLangCode WordEq.
Module Range.
  Definition range (v : Values.t) : bnd * bnd :=
    match v with
    | FVal (_, z) => (Fin z, Fin z)
    | _ => (NegInf, PosInf)
    end.
End Range.
Module Width.
  Definition width (v : Values.t) : option positive :=
    match v with FVal (w, _) => Some w | _ => None end.
End Width.
Module Checks := BitsChecksCode Values Range Range Width.

Example positive_divisor : Checks.may_fail DivZero [FVal (8%positive, 2%Z)] = false.
Proof. vm_compute. reflexivity. Qed.
Example zero_divisor : Checks.may_fail DivZero [FVal (8%positive, 0%Z)] = true.
Proof. vm_compute. reflexivity. Qed.
Example in_bounds : Checks.may_fail Bounds [FVal (8%positive, 2%Z); FVal (8%positive, 3%Z)] = false.
Proof. vm_compute. reflexivity. Qed.
Example at_bound : Checks.may_fail Bounds [FVal (8%positive, 3%Z); FVal (8%positive, 3%Z)] = true.
Proof. vm_compute. reflexivity. Qed.
Example unknown_pointer : Checks.may_fail NullDeref [FTop] = true.
Proof. vm_compute. reflexivity. Qed.

Example addition_fits :
  Checks.may_fail (Overflow bvadd false) [FVal (8%positive, 2%Z); FVal (8%positive, 3%Z)] = false.
Proof. vm_compute. reflexivity. Qed.
Example addition_overflows :
  Checks.may_fail (Overflow bvadd false) [FVal (8%positive, 255%Z); FVal (8%positive, 1%Z)] = true.
Proof. vm_compute. reflexivity. Qed.
Example different_widths_alarm :
  Checks.may_fail (Overflow bvadd false) [FVal (8%positive, 2%Z); FVal (4%positive, 3%Z)] = true.
Proof. vm_compute. reflexivity. Qed.
Example multiplication_fits :
  Checks.may_fail (Overflow bvmul false) [FVal (8%positive, 2%Z); FVal (8%positive, 3%Z)] = false.
Proof. vm_compute. reflexivity. Qed.
