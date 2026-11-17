(** * Environment budget operations

    These examples exercise the executable tagged-value helpers used by the budget.
    For example, untagging rejects a value without a concrete width.
    Builds on: EnvBudgetSig.

    Groups:
    - [UntagTests] Reading a list of tagged values back as concrete pairs.
    - [BinaryTests] Combining two tagged values with a payload function.
    - [IntersectionTests] Intersecting two tagged values. *)

From Stdlib Require Import List Arith PArith.
From Galois.Domains Require Import WordSig.
From Galois.States Require Import EnvBudgetSig.
Import List.ListNotations.

(** * Fixtures *)

(** The payload check that accepts a value of zero. *)
Definition zero_payload (_ : positive) (n : nat) := Nat.eqb n 0.

(** The payload combination that adds two numbers. *)
Definition add_payload (_ : positive) := Nat.add.

Module UntagTests.

  (** A list of concrete tagged values untags to its widths and numbers, in order. *)
  Example concrete_values_untag_in_order :
    budget_untag [TVal 8%positive 2; TVal 4%positive 3] =
    Some [(8%positive, 2); (4%positive, 3)].
  Proof. vm_compute. reflexivity. Qed.

  (** A list that contains an unknown value does not untag. *)
  Example unknown_value_blocks_untag : budget_untag [TVal 8%positive 2; TAny] = None.
  Proof. vm_compute. reflexivity. Qed.

End UntagTests.

Module BinaryTests.

  (** Two values of the same width combine into one value of that width. *)
  Example equal_widths_combine :
    budget_binary zero_payload add_payload (TVal 8%positive 2) (TVal 8%positive 3) =
    TVal 8%positive 5.
  Proof. vm_compute. reflexivity. Qed.

  (** Two values of different widths combine into an unknown value. *)
  Example different_widths_give_any :
    budget_binary zero_payload add_payload (TVal 8%positive 2) (TVal 4%positive 3) = TAny.
  Proof. vm_compute. reflexivity. Qed.

End BinaryTests.

Module IntersectionTests.

  (** Two zero values of one width intersect to the bottom value. *)
  Example zero_values_intersect_to_bot :
    budget_intersection zero_payload add_payload (TVal 8%positive 0) (TVal 8%positive 0) =
    TBot.
  Proof. vm_compute. reflexivity. Qed.

End IntersectionTests.
