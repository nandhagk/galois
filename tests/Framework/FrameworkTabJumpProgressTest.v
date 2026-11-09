(** * Constructive symbolic jump stopping clients

    The actual specialized jump engine constructs fuel from global symbolic height data.
    For example, an unlisted public start still has a finite conservative key inventory.
    Builds on: FrameworkTabJumpProgress and the actual call fixtures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeHeight.
From Galois.Framework Require Import FrameworkUtil FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabJumpProgress.
From Galois.Tests.Framework Require Import FrameworkIdeTest FrameworkTabCostTest.
Import List.ListNotations.

(** An actual importing client proves stopping without a successful-run or jump-post premise. *)
Example actual_jump_stops start :
  exists stopped, TabJumpProgress.complete_raw ifds_ide start bool_height = inr stopped /\
    Tab.work stopped = [].
Proof.
  apply TabJumpProgress.complete_raw_stops.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - apply jkey_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - exact bool_laws.
Qed.

(** The actual finite-height wrapper cannot exhaust its constructed numeric budget. *)
Example actual_jump_does_not_exhaust start s :
  TabJumpProgress.complete ifds_ide start bool_height <> Tab.Exhausted s.
Proof.
  apply TabJumpProgress.complete_not_exhausted.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - apply jkey_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - exact bool_laws.
Qed.

Example actual_constructed_jump_budget_certifies_this_fixture :
  match TabJumpProgress.complete ifds_ide 0 bool_height with
  | Tab.Certified _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition completed_chain_ticks n :=
  Cost.ticks (TabJumpProgress.complete_c (Ifds.as_ide (call_chain n)) 0 bool_height).

Example actual_constructed_call_cost_controls :
  (0 < completed_chain_ticks 2%nat /\ completed_chain_ticks 2%nat < completed_chain_ticks 4%nat)%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example actual_constructed_chain_returns :
  match TabJumpProgress.complete (Ifds.as_ide (call_chain 4)) 0 bool_height with
  | Tab.Certified result =>
    Jump.lookup (Ifds.as_ide (call_chain 4)) (proj1_sig result) ((0, None), (8, None))
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The actual wrapper cost includes the entire reached checker, not just worklist updates. *)
Example constructed_jump_cost_retains_checker :
  Cost.ticks (TabJumpProgress.complete_c ifds_ide 0 bool_height) =
    (Cost.ticks (TabJumpProgress.complete_raw_c ifds_ide 0%nat bool_height) +
      match TabJumpProgress.complete_raw ifds_ide 0%nat bool_height with
      | inl _ => 0
      | inr stopped => Cost.ticks (check_jumps_c ifds_ide 0%nat (Tab.jumps stopped))
      end)%N.
Proof.
  apply TabJumpProgress.complete_cost_equation.
Qed.
