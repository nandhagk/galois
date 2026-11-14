(** * Environment budget operations

    These examples exercise the executable tagged-value helpers used by the budget.
    For example, untagging rejects a value without a concrete width.
    Builds on: EnvBudgetSig. *)

From Stdlib Require Import List Arith PArith.
From Galois.Domains Require Import WordSig.
From Galois.States Require Import EnvBudgetSig.
Import List.ListNotations.

Definition zero_payload (_ : positive) (n : nat) := Nat.eqb n 0.
Definition add_payload (_ : positive) := Nat.add.

Example untag_values :
  budget_untag [TVal 8%positive 2; TVal 4%positive 3] =
  Some [(8%positive, 2); (4%positive, 3)].
Proof. vm_compute. reflexivity. Qed.

Example untag_any : budget_untag [TVal 8%positive 2; TAny] = None.
Proof. vm_compute. reflexivity. Qed.

Example binary_equal_widths :
  budget_binary zero_payload add_payload (TVal 8%positive 2) (TVal 8%positive 3) =
  TVal 8%positive 5.
Proof. vm_compute. reflexivity. Qed.

Example binary_different_widths :
  budget_binary zero_payload add_payload (TVal 8%positive 2) (TVal 4%positive 3) = TAny.
Proof. vm_compute. reflexivity. Qed.

Example intersection_zero :
  budget_intersection zero_payload add_payload (TVal 8%positive 0) (TVal 8%positive 0) = TBot.
Proof. vm_compute. reflexivity. Qed.
