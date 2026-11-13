(** * Binary-fuel loop fixtures

    These examples check exhaustion and stopping for a countdown callback.
    For example, one unit of fuel decrements two to one.
    Builds on: Loop. *)

From Stdlib Require Import NArith.
From Galois.Base Require Import Loop.

Definition countdown (n : nat) : nat + nat :=
  match n with
  | O => inr 42
  | S n' => inl n'
  end.

Example zero_fuel : loopN countdown 0%N 2 = inl 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example one_exhausted : loopN countdown 1%N 2 = inl 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example one_stopped : loopN countdown 1%N 0 = inr 42.
Proof.
  vm_compute. reflexivity.
Qed.

Example even_exhausted : loopN countdown 4%N 9 = inl 5.
Proof.
  vm_compute. reflexivity.
Qed.

Example odd_exhausted : loopN countdown 3%N 9 = inl 6.
Proof.
  vm_compute. reflexivity.
Qed.

Example even_stopped : loopN countdown 8%N 0 = inr 42.
Proof.
  vm_compute. reflexivity.
Qed.

Example odd_stopped : loopN countdown 9%N 0 = inr 42.
Proof.
  vm_compute. reflexivity.
Qed.

Example countdown_stopped : loopN countdown 3%N 2 = inr 42.
Proof.
  vm_compute. reflexivity.
Qed.
