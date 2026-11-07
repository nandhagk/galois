(** * Recursive function summaries

    Examples cover recursive calls, bounded contexts, rejected calls and empty inventories.
    For example, both members of a recursive pair acquire a local true effect.
    Builds on: FrameworkSummary and FrameworkDenseTest. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeSimple.
From Galois.Program Require Import ProgramCalls.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointAnalysis.
From Galois.Framework Require Import FrameworkSummary.
From Galois.Tests.Framework Require Import FrameworkDenseTest.
Import List.ListNotations Cost.Notations.

Definition calls : Calls.t nat nat :=
  Calls.of_pure [0; 1] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 => [1] | 1 => [0] | _ => [] end)
    nat_encoding nat_encoding.

Definition effects : Summary.spec nat nat bool :=
  Summary.Make bool_lattice (fun f => Cost.ret (Nat.eqb f 1))
    (fun _ _ a => Cost.ret a).

Example recursive_pair :
  observe (summary_analysis calls effects) 8 [0; 1; 2] = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example summary_row_order :
  System.constraints (Analysis.system (summary_analysis calls effects)) =
    [Summary.SLocal 0; Summary.SLocal 1; Summary.SCall 0 1; Summary.SCall 1 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example summary_hand_candidate :
  check_post bool_lattice (Analysis.system (summary_analysis calls effects))
    (fun _ => true) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example summary_rejects_bottom :
  check_post bool_lattice (Analysis.system (summary_analysis calls effects))
    (fun _ => false) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition contexts := Ctx.call_string 2 calls.

Example call_string_two :
  Ctx.enter contexts 1 0 [0; 1] = Some [1; 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_context :
  Ctx.enter (Ctx.call_string 0 calls) 1 0 [0; 1] = Some [].
Proof.
  vm_compute; reflexivity.
Qed.

Example contextual_pair :
  observe (ctx_summary_analysis calls contexts effects) 16 [(0, []); (1, [0]); (0, [1; 0])] =
    Some [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Definition rejecting_context : Ctx.t nat nat unit :=
  Ctx.Make unit_encoding [tt] (fun _ => Cost.ret tt) (fun _ _ _ => Cost.ret None).

Example rejected_enter_has_no_read :
  observe (ctx_summary_analysis calls rejecting_context effects) 8 [(0, tt); (1, tt)] =
    Some [false; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example scc_heads :
  (Policy.order (summary_policy_scc calls) 0,
   Policy.order (summary_policy_scc calls) 1,
   Policy.widen_at (summary_policy_scc calls) 0,
   Policy.widen_at (summary_policy_scc calls) 1) = (3%positive, 3%positive, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition no_calls : Calls.t nat nat :=
  Calls.of_pure [] [] (fun _ => []) (fun _ => 0) (fun _ => [])
    nat_encoding nat_encoding.

Example empty_summary :
  observe (summary_analysis no_calls effects) 1 [0] = Some [false].
Proof.
  vm_compute; reflexivity.
Qed.
