(** * Actual Euclidean machine examples

    These examples evaluate the costed floor machine and its independent finite sum.
    For example, an empty prefix has sum zero.
    Builds on: AnalysesLoopsFloor. *)

From Stdlib Require Import NArith Bool List.
From Galois.Cost Require Import CostMonad.
From Galois.Analyses.Loops Require Import AnalysesLoopsFloor.
Import Floor List.ListNotations.

Example floor_small_sum : floor_sum_fast 4 3 2 0 = 3%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example floor_zero_modulus : floor_sum_counted 4 0 2 9 = (0, 0, false)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example floor_empty_prefix : floor_sum_counted 0 3 2 9 = (0, 1, true)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example floor_actual_updates : floor_sum_counted 4 3 2 0 = (3, 3, true)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example floor_single_step_ticks :
  Cost.ticks (floor_step_c (State 0 3 2 9 0 false 0)) = 15%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example floor_zero_ticks : Cost.ticks (floor_sum_fast_c 4 0 2 9) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition floor_grid_values : list N := [0; 1; 2; 3; 4; 5; 6; 7; 8]%N.

Example floor_small_exhaustive_reference :
  forallb (fun n =>
    forallb (fun m =>
      forallb (fun a =>
        forallb (fun b =>
          N.eqb (floor_sum_fast n m a b) (floor_sum_reference n m a b))
          floor_grid_values) floor_grid_values)
      [1; 2; 3; 4; 5; 6; 7; 8]%N) floor_grid_values = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example floor_width128_client_discharges_primitive_bounds :
  (floor_primitive_bits (N.iter 3 floor_step
    (State 340282366920938463463374607431768211456
      340282366920938463463374607431768211456 1 1 0 false 0)) <=
    500 * (128 + 1))%N.
Proof.
  apply (word_floor_primitive_bits 128%positive); vm_compute; discriminate.
Qed.
