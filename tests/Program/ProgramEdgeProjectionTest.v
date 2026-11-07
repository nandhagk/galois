(** * Occurrence projection fixtures

    Occurrence numbers distinguish repeated client values without changing their order.
    For example, two copies of seven have occurrence numbers zero and one.
    Builds on: ProgramEdgeProjection. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Program Require Import ProgramEdgeProjection.
Import List.ListNotations.

Example repeated_occurrences :
  EdgeProjection.occurrences [7; 7; 7] 0 = [(7, 0); (7, 1); (7, 2)].
Proof.
  vm_compute; reflexivity.
Qed.

Example rejects_merged_occurrences :
  EdgeProjection.occurrences [7; 7] 0 <> [(7, 0)].
Proof.
  vm_compute; discriminate.
Qed.

Example empty_occurrences : EdgeProjection.occurrences (@nil nat) 0 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example occurrence_count_ticks :
  Cost.ticks (EdgeProjection.occurrences_c [7; 7; 7] 0) = 3%N.
Proof.
  vm_compute; reflexivity.
Qed.
