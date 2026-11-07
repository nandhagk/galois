(** * Dense direction and boundary fixtures

    Examples pin seed domains, flow direction, certified outcomes and boundary rejection.
    For example, backward seeds retain observations at a nonterminal diamond node.
    Builds on: FrameworkDense and FixpointAnalyze. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointCheck
  FixpointAnalysis FixpointSolver FixpointAnalyze.
From Galois.Framework Require Import FrameworkDense.
Import List.ListNotations Cost.Notations.

Definition diamond : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2; 3]
    (fun n => match n with 0 => [0; 1] | 1 => [2] | 2 => [3] | _ => [] end)
    (fun e => match e with 2 => 1 | 3 => 2 | _ => 0 end)
    (fun e => match e with 0 => 1 | 1 => 2 | _ => 3 end)) nat_encoding nat_encoding.

Definition loop : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2]
    (fun n => match n with 0 => [0] | 1 => [1; 2] | _ => [] end)
    (fun e => match e with 0 => 0 | _ => 1 end)
    (fun e => match e with 2 => 2 | _ => 1 end)) nat_encoding nat_encoding.

Definition singleton : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0] (fun _ => []) (fun _ => 0) (fun _ => 0))
    nat_encoding nat_encoding.

Definition empty : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [] [] (fun _ => []) (fun _ => 0) (fun _ => 0))
    nat_encoding nat_encoding.

Definition observe {X C A} (a : Analysis.t X C A) fuel xs :=
  match analyze a fuel with
  | Outcome.Solved s => Some (map (proj1_sig s) xs)
  | _ => None
  end.

Definition forward (cfg : Cfg.t nat nat) :=
  Dense.of_pure cfg Forward bool_lattice (fun _ => Some true) (fun _ a => a).

Definition backward (cfg : Cfg.t nat nat) :=
  Dense.of_pure cfg Backward bool_lattice
    (fun n => if Nat.eqb n 1 then Some true else None) (fun _ a => a).

Definition run_dense (D : Dense.t nat nat bool) :=
  Dense.analysis D (Policy.by_code nat_encoding).

Example diamond_forward :
  observe (run_dense (forward diamond)) 8 [0; 1; 2; 3; 99] =
    Some [true; true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_backward_nonterminal_boundary :
  observe (run_dense (backward diamond)) 8 [0; 1; 2; 3] = Some [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_forward :
  observe (run_dense (forward loop)) 8 [0; 1; 2] = Some [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_backward :
  observe (run_dense (backward loop)) 8 [0; 1; 2] = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_seed :
  observe (run_dense (forward singleton)) 2 [0; 1] = Some [true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example no_boundary_singleton :
  observe (run_dense (backward singleton)) 1 [0] = Some [false].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_rows :
  observe (run_dense (forward empty)) 1 [0] = Some [false].
Proof.
  vm_compute; reflexivity.
Qed.

Example forward_seed_order :
  System.constraints (Dense.system (forward diamond)) =
    [Dense.Seed 0; Dense.Flow 0; Dense.Flow 1; Dense.Flow 2; Dense.Flow 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example backward_seed_order :
  System.constraints (Dense.system (backward diamond)) =
    [Dense.Seed 0; Dense.Seed 1; Dense.Seed 2; Dense.Seed 3;
      Dense.Flow 0; Dense.Flow 1; Dense.Flow 2; Dense.Flow 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_candidate_accepted :
  check_post bool_lattice (Dense.system (backward diamond))
    (fun n => Nat.eqb n 0 || Nat.eqb n 1) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_candidate_rejected :
  check_post bool_lattice (Dense.system (forward diamond)) (fun _ => false) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example unlisted_boundary_is_not_a_row :
  check_post bool_lattice
    (Dense.system (Dense.of_pure singleton Forward bool_lattice
      (fun n => if Nat.eqb n 99 then Some true else None) (fun _ a => a)))
    (fun _ => false) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_exhausted :
  match analyze (run_dense (forward diamond)) 1 with
  | Outcome.OutOfFuel _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_dense :=
  Dense.Make singleton Forward bool_lattice
    (fun _ => Cost.tick 11 ;; Cost.ret (Some true))
    (fun _ a => Cost.tick 17 ;; Cost.ret a).

Example boundary_callee_and_invocation :
  Cost.ticks (Dense.rhs_c charged_dense (Dense.Seed 0)) = 12%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_flow : Dense.t nat nat bool :=
  Dense.Make
    (Cfg.Make (Graph.Make [0] [0; 1]
      (fun n => Cost.ret (if Nat.eqb n 0 then [0] else []))
      (fun _ => Cost.tick 5 ;; Cost.ret 0) (fun _ => Cost.tick 7 ;; Cost.ret 1))
      nat_encoding nat_encoding)
    Forward bool_lattice (fun _ => Cost.ret None)
    (fun _ a => Cost.tick 17 ;; Cost.ret a).

Definition charged_lookup (_ : nat) := Cost.tick 13 ;; Cost.ret true.

Example flow_retains_endpoints_transfer_and_continuation :
  (Cost.ticks (Dense.rhs_c charged_flow (Dense.Flow 0)),
   Cost.ticks (Dense.target_c charged_flow (Dense.Flow 0)),
   Cost.ticks (Query.run_c charged_lookup (System.rhs (Dense.system charged_flow) (Dense.Flow 0))),
   Cost.ticks (Eval.outputs_c (Dense.system charged_flow) charged_lookup (Dense.Flow 0))) =
    (6%N, 8%N, 35%N, 51%N).
Proof.
  vm_compute; reflexivity.
Qed.
