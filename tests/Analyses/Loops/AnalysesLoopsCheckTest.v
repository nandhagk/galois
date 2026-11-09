(** * Indexed scalar-evolution checker regressions

    These examples retain the legacy source-shape and rejection observations.
    For example, a nested recurrence is accepted and an unrelated binding is rejected.
    Builds on: AnalysesLoopsCheck and ProgramSsa. *)

From Stdlib Require Import List Bool Arith ZArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseMemo.
From Galois.Bits Require Import BitsWord.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsRecognise
  AnalysesLoopsCheck.
Import List.ListNotations Chrec Recognise PlanCheck.
Local Open Scope nat_scope.

Definition scev_shape_graph : Graph.t nat nat :=
  Graph.of_pure [0] [0; 1; 2] (fun _ => []) (fun _ => 0) (fun _ => 1).

Definition scev_shape_defs (x : nat) : definition nat nat nat :=
  match x with
  | 3 => Param 1 0
  | 6 => Param 1 1
  | 5 => Op 0 [3; 2]
  | 7 => Op 0 [6; 3]
  | 8 => Op 2 []
  | _ => Arbitrary
  end.

Definition scev_shape_loop defs entry : loop_view nat nat nat nat unit :=
  LoopView
    (Ssa.of_pure (Cfg.Make scev_shape_graph nat_encoding nat_encoding)
      nat_encoding [0; 1; 2; 3; 5; 6; 7; 8] defs
      (fun x => if Nat.eqb x 3 || Nat.eqb x 6 then 1 else
        if Nat.eqb x 5 || Nat.eqb x 7 || Nat.eqb x 8 then 2 else 0)
      (fun _ => [3; 6]) (fun e => if Nat.eqb e 0 then entry else [5; 7])
      (fun _ => []))
    1 (Cost.lift (fun _ => 1%N) (fun n => Nat.eqb n 1 || Nat.eqb n 2)) 0 1 None.

Definition scev_shape_ops : scev_ops nat Z :=
  ops_of_pure 8%positive (wrap 8%positive) (Nat.eqb 0) (Nat.eqb 1)
    (fun o => if Nat.eqb o 2 then Some 255%Z else None).

Definition scev_shape_inventory := [0; 1; 2; 3; 5; 6; 7; 8].

Definition scev_shape_nested_plan : scev_plan nat :=
  ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true;
    ScevBinding 6 1 7 SAddUpdate (Some (SPhi 3)) true] 6.

Example scev_checker_ranked_nested_phi :
  scev_plan_check (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops
    scev_shape_inventory scev_shape_nested_plan = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_geometric :
  scev_plan_check
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 1 [3; 2] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory
    (ScevPlan [ScevBinding 3 0 5 SMulUpdate (Some (SOutside 2)) true] 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_direct_self_add :
  scev_plan_check
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 3] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory
    (ScevPlan [ScevBinding 3 0 5 SDoubleUpdate None true] 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_tagged_word_literal :
  scev_plan_check
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory
    (ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SConst 8 255)) true] 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_nonlinear_direct_feedback_rejected :
  scev_plan_check
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else
      if Nat.eqb x 8 then Op 1 [3; 3] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory
    (ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SMul 8 (SPhi 3) (SPhi 3))) true] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_mutual_feedback_rejected :
  scev_plan_check
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 6] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory
    (ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SPhi 6)) true;
      ScevBinding 6 1 7 SAddUpdate (Some (SPhi 3)) true] 6) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_missing_inventory_operand :
  scev_plan_check (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops
    [0; 1; 3; 5; 6; 7; 8] scev_shape_nested_plan = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_missing_phi_argument :
  scev_plan_check (scev_shape_loop scev_shape_defs []) scev_shape_ops
    scev_shape_inventory scev_shape_nested_plan = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_duplicate_phi_rejected :
  let b := ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true in
  scev_plan_check (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops
    scev_shape_inventory (ScevPlan [b; b] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_malformed_operation_operands :
  scev_plan_check
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory
    (ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_unrelated_binding_rejected :
  scev_plan_check
    (scev_shape_loop (fun x => if Nat.eqb x 7 then Op 0 [6; 2] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory
    (ScevPlan [ScevBinding 6 1 7 SAddUpdate (Some (SOutside 2)) true;
      ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_empty_plan :
  scev_plan_check (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops
    scev_shape_inventory (ScevPlan [] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_rank_observation_invalidates_then_reuses :
  let lv := scev_shape_loop scev_shape_defs [0; 1] in
  let ix := prepare_index lv scev_shape_inventory scev_shape_nested_plan in
  let e := SPhi 3 in
  let '((r0, m0), _) := Cost.value (scev_check_expr_c nat_encoding (lbody_c lv)
    (indexed_values ix) scev_shape_ops (phi_before_c nat_encoding ix 0) e Memo.empty) in
  let '((r1, m1), _) := Cost.value (scev_check_expr_c nat_encoding (lbody_c lv)
    (indexed_values ix) scev_shape_ops (phi_before_c nat_encoding ix 1) e m0) in
  let '((r2, m2), _) := Cost.value (scev_check_expr_c nat_encoding (lbody_c lv)
    (indexed_values ix) scev_shape_ops (phi_before_c nat_encoding ix 2) e m1) in
  fst r0 = false /\ fst r1 = true /\ fst r2 = true /\ Map.size m1 = 2 /\ Map.size m2 = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
