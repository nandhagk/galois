(** * Binary-fuel loop fixtures

    These examples check exhaustion and stopping for a countdown callback.
    For example, one unit of fuel decrements two to one.

    Groups:
    - [FuelTests] Runs that use up their fuel and return the state.
    - [StopTests] Runs that stop early because the callback returns a result.

    Builds on: Loop. *)

From Stdlib Require Import NArith.
From Galois.Base Require Import Loop.

(** * Fixtures *)

(** Counts a state down by one, and stops with 42 at zero. *)
Definition countdown (n : nat) : nat + nat :=
  match n with
  | O => inr 42
  | S n' => inl n'
  end.

(** * Fuel *)

Module FuelTests.

  (** Zero fuel returns the starting state at once. *)
  Example zero_fuel_returns_start : loopN countdown 0%N 2 = inl 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** One unit of fuel takes one step. *)
  Example one_fuel_takes_one_step : loopN countdown 1%N 2 = inl 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Four units of fuel take four steps from nine. *)
  Example four_fuel_takes_four_steps : loopN countdown 4%N 9 = inl 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Three units of fuel take three steps from nine. *)
  Example three_fuel_takes_three_steps : loopN countdown 3%N 9 = inl 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

End FuelTests.

(** * Stop *)

Module StopTests.

  (** With one unit of fuel, a start at zero stops with the callback result. *)
  Example stop_at_zero_gives_result : loopN countdown 1%N 0 = inr 42.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A start at zero stops with the callback result when fuel is even. *)
  Example even_fuel_stops_at_zero : loopN countdown 8%N 0 = inr 42.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A start at zero stops with the callback result when fuel is odd. *)
  Example odd_fuel_stops_at_zero : loopN countdown 9%N 0 = inr 42.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The callback result stops the run before the fuel runs out. *)
  Example stop_before_fuel_ends : loopN countdown 3%N 2 = inr 42.
  Proof.
    vm_compute. reflexivity.
  Qed.

End StopTests.
