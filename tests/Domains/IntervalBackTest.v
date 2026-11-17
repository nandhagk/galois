(** * Interval backward operations

    These examples exercise direct backward interval refinement.
    For example, an addition result narrows its first operand.
    Builds on: IntervalBack and Thresholds.

    Groups:
    - [AddTests] Backward addition narrows an operand.
    - [UnsignedTests] A false unsigned comparison narrows both operands.
    - [ResizeTests] A truncated result keeps an operand that already fits. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import ValueSig Interval IntervalSig IntervalBack Thresholds
  ThresholdsSig.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Scalar := IntervalBaseCode ThresholdsCode.
Module Back := IntervalBackCode ThresholdsCode Scalar.

(** * Addition *)

Module AddTests.

  (** An addition whose result and second operand are known narrows the first operand. *)
  Example addition_narrows_first_operand :
    Back.interval_assume_pair bvadd 8%positive (I (Fin 0) (Fin 10)) (I (Fin 2) (Fin 2))
      (I (Fin 5) (Fin 7)) = (I (Fin 3) (Fin 5), I (Fin 2) (Fin 2)).
  Proof.
    vm_compute. reflexivity.
  Qed.

End AddTests.

(** * Unsigned comparison *)

Module UnsignedTests.

  (** A comparison that must be false raises the lower bound of its first operand. *)
  Example false_unsigned_less_than_raises_first_lower_bound :
    Back.interval_bwd2 bvult 1%positive (I (Fin 0) (Fin 0))
      [(8%positive, I (Fin 0) (Fin 20)); (8%positive, I (Fin 5) (Fin 10))] =
    [I (Fin 5) (Fin 20); I (Fin 5) (Fin 10)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End UnsignedTests.

(** * Resize *)

Module ResizeTests.

  (** A result truncated to four bits keeps an operand that already fits in four bits. *)
  Example truncated_result_keeps_operand_that_fits :
    Back.interval_bwd1 4%positive (I (Fin 3) (Fin 5))
      [(8%positive, I (Fin 0) (Fin 10))] = [I (Fin 3) (Fin 5)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ResizeTests.
