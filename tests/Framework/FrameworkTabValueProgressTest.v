(** * Constructive finite-height value completion clients

    Numeric completion constructs its own fuel from actual endpoint inventory and Boolean height.
    For example, an unlisted call output still belongs to that prepared finite endpoint inventory.
    Builds on: FrameworkTabValueProgress and the actual IDE fixtures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkIfds FrameworkIde FrameworkTabValues
  FrameworkTabValueProgress FrameworkTabValueClosure FrameworkTabCost.
From Galois.Tests.Framework Require Import FrameworkIdeTest.
Import List.ListNotations.

(** A real client supplies numeric height evidence rather than a successful-run or postcondition premise. *)
Example actual_finite_height_value_stops :
  exists stopped,
    TabValueProgress.complete_raw (TabValues.reach_ide taint) taint_jump (0, None) true
      bool_height = inr stopped /\ TabValues.work stopped = [].
Proof.
  apply TabValueProgress.complete_raw_stops.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - exact bool_laws.
Qed.

(** The actual finite-height wrapper cannot report numeric exhaustion on this client. *)
Example actual_finite_height_no_exhaustion s :
  TabValueProgress.complete (TabValues.reach_ide taint) taint_jump (0, None) true bool_height <>
    TabValues.Exhausted s.
Proof.
  apply TabValueProgress.complete_not_exhausted.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - exact bool_laws.
Qed.

Example actual_finite_height_prefix_is_informative :
  match TabValueProgress.complete (TabValues.reach_ide taint) taint_jump
    (0, None) true bool_height with
  | TabValues.Certified values =>
    TabValues.lookup (TabValues.reach_ide taint) (proj1_sig values) (2, Some tt)
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Completion retains a raw call output outside the ordinary fact inventory. *)
Example unlisted_raw_call_stops :
  exists stopped,
    TabValueProgress.complete_raw unlisted_call_ide Map.empty (0, None) true bool_height =
      inr stopped /\ TabValues.work stopped = [].
Proof.
  apply TabValueProgress.complete_raw_stops.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - exact bool_laws.
Qed.

Example unlisted_raw_call_is_not_lost :
  match TabValueProgress.complete unlisted_call_ide Map.empty (0, None) true bool_height with
  | TabValues.Certified values => TabValues.lookup unlisted_call_ide (proj1_sig values) (1, Some tt)
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example numeric_inventory_construction_keeps_its_full_charge :
  Cost.ticks (TabCost.inventory_fuel_c [tt; tt; tt] 1) = 5%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** Actual completion and checker acceptance hold for arbitrary jump maps and raw seeds. *)
Example actual_value_completion_certifies (J : Map.t positive bool) start a0 :
  exists values,
    TabValueProgress.complete (TabValues.reach_ide taint) J start a0 bool_height =
      TabValues.Certified values.
Proof.
  apply TabValueClosure.complete_certified.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact bool_laws.
Qed.

(** The theorem also covers the raw fixture whose call produces an unlisted fact. *)
Example unlisted_raw_value_completion_certifies (J : Map.t positive bool) start a0 :
  exists values, TabValueProgress.complete unlisted_call_ide J start a0 bool_height =
    TabValues.Certified values.
Proof.
  apply TabValueClosure.complete_certified.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact bool_laws.
Qed.

(** Leastness takes a genuine comparison post-solution, while completion has no result premise. *)
Example actual_value_completion_least (J : Map.t positive bool) start a0 sigma :
  post_solution bool_lattice
    (Analysis.system (value_analysis (TabValues.reach_ide taint)
      (Jump.lookup_c (TabValues.reach_ide taint) J) start a0)) sigma ->
  exists values,
    TabValueProgress.complete (TabValues.reach_ide taint) J start a0 bool_height =
      TabValues.Certified values /\
    forall v, leb bool_lattice
      (TabValues.lookup (TabValues.reach_ide taint) (proj1_sig values) v) (sigma v) = true.
Proof.
  intro Hpost; apply TabValueClosure.complete_least.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact bool_laws.
  - exact bool_lub.
  - exact TabValues.reach_micro_laws.
  - exact Hpost.
Qed.

Example actual_completion_cost_retains_certification :
  Cost.ticks (TabValueProgress.complete_c (TabValues.reach_ide taint) taint_jump
    (0%nat, None) true bool_height) =
    (Cost.ticks (TabValueProgress.complete_raw_c (TabValues.reach_ide taint) taint_jump
      (0%nat, None) true bool_height) +
      match TabValueProgress.complete_raw (TabValues.reach_ide taint) taint_jump
        (0%nat, None) true bool_height with
      | inl _ => 0
      | inr stopped =>
        Cost.ticks (TabValues.certify_c (TabValues.reach_ide taint) taint_jump
          (0%nat, None) true stopped)
      end)%N.
Proof.
  apply TabValueProgress.complete_cost_equation.
Qed.

Example actual_completion_charges_nonzero_work :
  (0 < Cost.ticks (TabValueProgress.complete_c (TabValues.reach_ide taint) taint_jump
    (0%nat, None) true bool_height))%N.
Proof.
  vm_compute; reflexivity.
Qed.
