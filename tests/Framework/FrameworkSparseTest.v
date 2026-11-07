(** * Sparse arithmetic and client guards

    The fixtures port stored-subject arithmetic, truth and infeasible-edge regressions.
    For example, the value one plus one takes the equal-two edge and rejects equal-zero.
    Builds on: FrameworkSparse and the generic point word dictionary. *)

From Stdlib Require Import List Bool ZArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Domains Require Import DomainsValue DomainsPoint DomainsTagged DomainsNumeric
  DomainsBitsValue.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck FixpointAnalysis.
From Galois.Framework Require Import FrameworkRows FrameworkSparse.
From Galois.Tests.Framework Require Import FrameworkDenseTest.
Import List.ListNotations Cost.Notations Expr Sparse.
Local Open Scope nat_scope.

Definition bridge : op_bridge expr word :=
  {| op_expr_c := fun e => Cost.ret (Some e);
     to_word_c := fun c => Cost.ret (Some (fst c, wrap (fst c) (snd c)));
     truth_words := true;
     differ_words_c := fun _ => Cost.ret false |}.

Definition values := bits_values (tagged_domain point_word_domain) bridge TAny.
Definition number z : tagged point := TVal 32%positive (PVal z).

Definition ssa_cfg : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2]
    (fun n => match n with 0 => [0; 1] | 1 => [2] | _ => [] end)
    (fun e => match e with 2 => 1 | _ => 0 end)
    (fun e => match e with 0 => 1 | _ => 2 end)) nat_encoding nat_encoding.

Definition ssa_program : Ssa.t nat nat nat expr (bits_guard word) :=
  Ssa.of_pure ssa_cfg nat_encoding [0; 1]
    (fun v => match v with
      | 0 => Param 0 0
      | 1 => Op (App bvadd [Var 0; Var 1]) [0; 0]
      | _ => Arbitrary
      end)
    (fun _ => 0)
    (fun n => if Nat.eqb n 0 then [0] else [])
    (fun _ => [])
    (fun e => match e with
      | 0 => [(Equal (32%positive, 2%Z), [1])]
      | 1 => [(Equal (32%positive, 0%Z), [1])]
      | _ => []
      end).

Definition problem := Sparse.Make ssa_program values (fun _ => Cost.ret (number 1)).
Definition analysis := sparse_analysis problem 0.

Example sparse_rows_exact :
  Sparse.rows problem =
    [CBlockEntry 0; CEntryFact 0; COp 1;
      CEdge 0; CBlock 0; CEdge 1; CBlock 1; CEdge 2; CBlock 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_result :
  observe analysis 16 [UVal 0; UVal 1; UEdge 0; UEdge 1; UBlock 2] =
    Some [Some (number 1); Some (number 2); Some TAny; None; Some TAny].
Proof.
  vm_compute; reflexivity.
Qed.

Definition candidate (x : Sparse.unknown nat nat nat) :=
  match x with
  | UVal 0 => Some (number 1)
  | UVal 1 => Some (number 2)
  | UVal _ => None
  | UEdge 1 => None
  | _ => Some TAny
  end.

Example sparse_candidate_accepted :
  check_post (Analysis.lat analysis) (Analysis.system analysis) candidate = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_candidate_rejected :
  check_post (Analysis.lat analysis) (Analysis.system analysis) (fun _ => None) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_ssa : Ssa.t nat nat nat expr (bits_guard word) :=
  Ssa.of_pure empty nat_encoding [] (fun _ => Arbitrary) (fun _ => 0)
    (fun _ => []) (fun _ => []) (fun _ => []).

Example sparse_empty :
  observe (sparse_analysis (Sparse.Make empty_ssa values (fun _ => Cost.ret TAny)) 0)
    1 [UVal 0; UBlock 0] = Some [None; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example guard_uses_stored_subject :
  option_map (fun m => Map.find_or nat_encoding None 1 m)
    (Cost.value (Sparse.guard_one_c (N := nat) nat_encoding values
      (Map.of_list nat_encoding [(0, Some (number 1)); (1, Some (number 0))])
      (Truth true, [1], [(1, Op (App bvadd [Var 0; Var 1]) [0; 0])]))) =
    Some (Some TBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example true_one_plus_one_keeps_operands :
  option_map (fun m => Map.find_or nat_encoding None 0 m)
    (Cost.value (Sparse.guard_one_c (N := nat) nat_encoding values
      (Map.of_list nat_encoding [(0, Some (number 1)); (1, Some (number 2))])
      (Truth true, [1], [(1, Op (App bvadd [Var 0; Var 1]) [0; 0])]))) =
    Some (Some (number 1)).
Proof.
  vm_compute; reflexivity.
Qed.

Example false_zero_subject :
  ValueAbs.guard values (Truth false) [number 0] = [number 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_width_truth :
  (ValueAbs.guard values (Truth true) [TAny],
   ValueAbs.guard values (Truth false) [TAny]) = ([TAny], [TAny]).
Proof.
  vm_compute; reflexivity.
Qed.

Example comparison_guard_keeps_inputs :
  ValueAbs.guard values (Test (App bvult [Var 0; Var 1]) true)
    [number 1; number 2] = [number 1; number 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example truncation_guard_tests_result :
  ValueAbs.guard values (Test (App (bvtrunc 1%positive) [Var 0]) false)
    [number 2] = [number 2].
Proof.
  vm_compute; reflexivity.
Qed.

Definition parameter_cfg : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1]
    (fun n => if Nat.eqb n 0 then [0] else []) (fun _ => 0) (fun _ => 1))
    nat_encoding nat_encoding.

Definition parameter_ssa : Ssa.t nat nat nat expr (bits_guard word) :=
  Ssa.of_pure parameter_cfg nat_encoding [0; 1; 2; 3]
    (fun v => match v with
      | 0 => Param 0 0
      | 1 => Op (App bvadd [Var 0; Var 1]) [0; 0]
      | 2 => Param 1 0
      | _ => Arbitrary
      end)
    (fun v => if Nat.eqb v 2 then 1 else 0)
    (fun n => match n with 0 => [0] | 1 => [2] | _ => [] end)
    (fun _ => [1; 0])
    (fun _ => [(Test (App bvult [Var 0; Var 1]) true, [0; 1]); (Truth true, [1])]).

Definition parameter_problem :=
  Sparse.Make parameter_ssa values (fun _ => Cost.ret (number 1)).

Example all_seven_sparse_row_kinds :
  Sparse.rows parameter_problem =
    [CBlockEntry 0; CEntryFact 0; COp 1; CArbitrary 3;
      CEdge 0; CBlock 0; CArg 0 0; CArg 0 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_parameter_and_multioperand_guards :
  observe (sparse_analysis parameter_problem 0) 16 [UVal 2; UVal 3; UEdge 0] =
    Some [Some (number 2); Some TAny; Some TAny].
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_argument_slot_targets_edge :
  System.target (Analysis.system (sparse_analysis parameter_problem 0)) (CArg 0 1) = UEdge 0.
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_problem :=
  Sparse.Make ssa_program values (fun _ => Cost.tick 23 ;; Cost.ret (number 1)).

Example entry_fact_retains_callback_charge :
  Cost.ticks (System.rhs_c (Analysis.system (sparse_analysis charged_problem 0))
    (CEntryFact 0)) =
  (23 + Cost.ticks (System.rhs_c (Analysis.system analysis) (CEntryFact 0%nat)))%N.
Proof.
  vm_compute; reflexivity.
Qed.
