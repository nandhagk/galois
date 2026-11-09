(** * Fast wrapped first-failure examples

    Finite grids compare the Euclidean search with the independent executable specification.
    For example, all word residues at width four include signed and unsigned wrap boundaries.
    Builds on: AnalysesLoopsTrip and AnalysesLoopsFailure. *)

From Stdlib Require Import List Bool NArith ZArith.
From Galois.Cost Require Import CostMonad.
From Galois.Analyses.Loops Require Import
  AnalysesLoopsChrec AnalysesLoopsFailure AnalysesLoopsFloor AnalysesLoopsTrip.
Import List.ListNotations.

Definition option_count_eqb (left right : option N) : bool :=
  match left, right with
  | Some a, Some b => N.eqb a b
  | None, None => true
  | _, _ => false
  end.

Definition fast_agreement_case w sg cmp (a step bound : Z) : bool :=
  option_count_eqb (Cost.value (Trip.first_failure_fast w sg cmp a step bound))
    (Trip.first_failure w sg cmp a step bound).

Definition fast_agreement_grid w (values : list Z) : bool :=
  forallb (fun sg =>
    forallb (fun cmp =>
      forallb (fun a =>
        forallb (fun step =>
          forallb (fast_agreement_case w sg cmp a step) values) values) values)
      [CmpLt; CmpLe; CmpNe]) [Unsigned; Signed].

Definition small_grid w : list Z :=
  List.map (fun i => Z.of_nat i)
    (List.seq 0 (N.to_nat (N.pos (Failure.word_period w)))).

(* The exhaustive widths and sampled widths are required by run/cards/LOOP-SCEV.md. *)
Example fast_all_residues_widths_one_to_four :
  List.map (fun w => fast_agreement_grid w (small_grid w))
    [1; 2; 3; 4]%positive = [true; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

(* Each list contains zero, one, both sign boundaries, both modulus boundaries
   and the fixed interior samples 2, 3, 5, 11 and 17. *)
Example fast_explicit_boundaries_and_samples_five_to_eight :
  [fast_agreement_grid 5%positive [0; 1; 2; 3; 5; 11; 15; 16; 17; 30; 31]%Z;
   fast_agreement_grid 6%positive [0; 1; 2; 3; 5; 11; 17; 31; 32; 33; 62; 63]%Z;
   fast_agreement_grid 7%positive [0; 1; 2; 3; 5; 11; 17; 63; 64; 65; 126; 127]%Z;
   fast_agreement_grid 8%positive [0; 1; 2; 3; 5; 11; 17; 127; 128; 129; 254; 255]%Z] =
  [true; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example fast_signed_negative_representatives :
  fast_agreement_grid 3%positive [-9; -4; -3; -1; 0; 1; 3; 4; 7; 8]%Z = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example fast_width_two_nonfailure :
  Cost.value (Trip.first_failure_fast 2%positive Unsigned CmpLt 0 2 3) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition wide64_no_failure :=
  Trip.first_failure_fast 64%positive Unsigned CmpLt 0 2 18446744073709551615.

Definition wide128_last_failure :=
  Trip.first_failure_fast 128%positive Unsigned CmpLt 0 1
    340282366920938463463374607431768211455.

Example fast_width64_full_period_nonfailure :
  Cost.value wide64_no_failure = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example fast_width128_full_period_first_failure :
  Cost.value wide128_last_failure = Some 340282366920938463463374607431768211455%N.
Proof.
  vm_compute; reflexivity.
Qed.

(* The literal counts follow the charged period, floor and binary-driver recurrences. *)
Example fast_wide_actual_tick_counts :
  Cost.ticks wide64_no_failure = 375%N /\
    Cost.ticks wide128_last_failure = 75922%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example fast_wide_actual_ticks_fit_bound :
  ((0 <? Cost.ticks wide64_no_failure)%N &&
    (Cost.ticks wide64_no_failure <=? Trip.first_failure_fast_k * 65 * 65)%N &&
    (0 <? Cost.ticks wide128_last_failure)%N &&
    (Cost.ticks wide128_last_failure <=? Trip.first_failure_fast_k * 129 * 129)%N) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example fast_rejected_nonlinear_trip :
  Trip.trip_count_fast (fun _ : nat => 0%Z) 8%positive Unsigned CmpLt
    (Chrec.CGeo (Chrec.CInv (IConst 1)) (Chrec.CInv (IConst 2))) (IConst 3) = None.
Proof.
  vm_compute; reflexivity.
Qed.
