(** * Interval backward operations

    These examples exercise direct backward interval refinement.
    For example, an addition result narrows its first operand.
    Builds on: IntervalBack and Thresholds. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import ValueSig Interval IntervalSig IntervalBack Thresholds ThresholdsSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Scalar := IntervalBaseCode ThresholdsCode.
Module Back := IntervalBackCode ThresholdsCode Scalar.

Example backward_add :
  Back.interval_assume_pair bvadd 8%positive (I (Fin 0) (Fin 10)) (I (Fin 2) (Fin 2))
    (I (Fin 5) (Fin 7)) = (I (Fin 3) (Fin 5), I (Fin 2) (Fin 2)).
Proof. vm_compute. reflexivity. Qed.

Example backward_unsigned_false :
  Back.interval_bwd2 bvult 1%positive (I (Fin 0) (Fin 0))
    [(8%positive, I (Fin 0) (Fin 20)); (8%positive, I (Fin 5) (Fin 10))] =
  [I (Fin 5) (Fin 20); I (Fin 5) (Fin 10)].
Proof. vm_compute. reflexivity. Qed.

Example backward_resize :
  Back.interval_bwd1 4%positive (I (Fin 3) (Fin 5))
    [(8%positive, I (Fin 0) (Fin 10))] = [I (Fin 3) (Fin 5)].
Proof. vm_compute. reflexivity. Qed.
