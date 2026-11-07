(** * Balanced threshold boundary computations

    These fixtures distinguish sorted preparation from repeated unbalanced insertion.
    For example, a thousand increasing thresholds produce depth ten.
    Builds on: DomainsThreshold. *)

From Stdlib Require Import ZArith List Arith.
From Galois.Cost Require Import CostMonad.
From Galois.Domains Require Import DomainsBound DomainsThreshold.
Import List.ListNotations.
Local Open Scope Z_scope.

Definition thousand_thresholds := threshold_of_list (map Z.of_nat (seq 0 1000)).

Example threshold_sorted_thousand_depth : threshold_depth thousand_thresholds = 10%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_sorted_thousand_depth_bound :
  Nat.leb (threshold_depth thousand_thresholds) 10 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_sorted_thousand_predecessor :
  lower_threshold thousand_thresholds 500 = Fin 500.
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_sorted_thousand_upper_none :
  upper_threshold thousand_thresholds 1000 = PosInf.
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_duplicates :
  threshold_of_list [10%Z; 10%Z; 10%Z] =
  ThresholdNode ThresholdEmpty 10 ThresholdEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_empty :
  (lower_threshold (threshold_of_list []) 0, upper_threshold (threshold_of_list []) 0,
    threshold_depth (threshold_of_list [])) = (NegInf, PosInf, 0%nat).
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_singleton :
  (lower_threshold (threshold_of_list [5%Z]) 4, upper_threshold (threshold_of_list [5%Z]) 4,
    lower_threshold (threshold_of_list [5%Z]) 5, upper_threshold (threshold_of_list [5%Z]) 6) =
  (NegInf, Fin 5, Fin 5, PosInf).
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_unsorted_negative :
  (lower_threshold (threshold_of_list [20%Z; -5%Z; 10%Z; 10%Z; 0%Z]) 7,
    upper_threshold (threshold_of_list [20%Z; -5%Z; 10%Z; 10%Z; 0%Z]) 7) =
  (Fin 0, Fin 10).
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_preparation_sorted_unique :
  threshold_list_ref [20%Z; -5%Z; 10%Z; 10%Z; 0%Z] = [-5%Z; 0%Z; 10%Z; 20%Z].
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_empty_ticks :
  (Cost.ticks (lower_threshold_c ThresholdEmpty 0),
    Cost.ticks (upper_threshold_c ThresholdEmpty 0)) = (1%N, 1%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example threshold_thousand_ticks :
  (Cost.ticks (lower_threshold_c thousand_thresholds (-1)),
    Cost.ticks (upper_threshold_c thousand_thresholds 1000)) = (11%N, 10%N).
Proof.
  vm_compute. reflexivity.
Qed.
