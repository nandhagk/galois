(** * Checked scalar-evolution recognition

    These examples retain the legacy recognizer's recurrence and rejection observations.
    For example, direct self-addition keeps the idiom-owned geometric coefficient two.
    Builds on: AnalysesLoopsSound and the indexed checker fixtures. *)

From Stdlib Require Import List Bool Arith ZArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Bits Require Import BitsWord.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsFailure
  AnalysesLoopsRecognise AnalysesLoopsCheck AnalysesLoopsSound.
From Galois.Tests.Analyses.Loops Require Import AnalysesLoopsCheckTest.
Import List.ListNotations Chrec Recognise PlanCheck LoopSound Failure.
Local Open Scope nat_scope.

Example scev_recognise_nested_phis :
  run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_inventory 6 =
    Some (CRec (CInv (IVar 1)) (CRec (CInv (IVar 0)) (CInv (IVar 2)))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_geometric :
  run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 1 [3; 2] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 = Some (CGeo (CInv (IVar 0)) (CInv (IVar 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_direct_doubling :
  run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 3] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 = Some (CGeo (CInv (IVar 0)) (CInv (IConst 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_mutual_feedback_rejected :
  run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 6] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_nonlinear_self_feedback_rejected :
  run (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else
    if Nat.eqb x 8 then Op 1 [3; 3] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_missing_inventory_rejected :
  run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops [0; 1; 3; 5; 6; 7; 8] 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition scev_descending_env (x : nat) : Z :=
  if Nat.eqb x 2 then 255%Z else if Nat.eqb x 0 then 2%Z else 0%Z.

Example scev_recognise_signed_descending_variable :
  match run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_inventory 3 with
  | Some c =>
    trip_count (fun y => view_z 8%positive Signed (scev_descending_env y)) 8%positive Signed CmpNe
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253)) =
        Some 5%N
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_signed_descending_literal :
  match run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 with
  | Some c =>
    c = CRec (CInv (IVar 0)) (CInv (IWordConst 255)) /\
    trip_count (fun y => view_z 8%positive Signed (scev_descending_env y)) 8%positive Signed CmpNe
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253)) =
        Some 5%N
  | None => False
  end.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_signed_descending_variable_nowrap :
  match run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_inventory 3 with
  | Some c => nowrap_check 8%positive Signed
      (fun y => view_z 8%positive Signed (scev_descending_env y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253))
      5%N = true
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_signed_descending_literal_nowrap :
  match run (scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else scev_shape_defs x) [0; 1])
    scev_shape_ops scev_shape_inventory 3 with
  | Some c => nowrap_check 8%positive Signed
      (fun y => view_z 8%positive Signed (scev_descending_env y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253))
      5%N = true
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_signed_minimum_wrap_rejected :
  let inv := fun x => if Nat.eqb x 0 then 128%Z else if Nat.eqb x 2 then 255%Z else 0%Z in
  match run (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_inventory 3 with
  | Some c =>
    trip_count (fun y => view_z 8%positive Signed (inv y)) 8%positive Signed CmpLt
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 129)) =
        Some 1%N /\
    nowrap_check 8%positive Signed (fun y => view_z 8%positive Signed (inv y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 129))
      1%N = false
  | None => False
  end.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_machine_fuel_construction :
  N.pos (Cost.value (command_fuel_c scev_shape_inventory)) = 36%N /\
    Cost.ticks (command_fuel_c scev_shape_inventory) = 9%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_machine_root_completion_trace :
  match Cost.value (run_execution_c (scev_shape_loop scev_shape_defs [0; 1])
    scev_shape_ops scev_shape_inventory 6) with
  | Some out =>
    preparation_reuses out = [] /\ prepared_nodes out = [6; 3; 2] /\
      plan out = scev_shape_nested_plan
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition scev_shared_defs (x : nat) : definition nat nat nat :=
  match x with
  | 3 => Param 1 0
  | 6 => Param 1 1
  | 13 => Param 1 2
  | 5 => Op 0 [3; 2]
  | 7 => Op 0 [6; 11]
  | 14 => Op 0 [13; 12]
  | 8 => Op 0 [3; 2]
  | 9 => Op 0 [8; 8]
  | 10 => Op 0 [9; 9]
  | 11 => Op 0 [10; 10]
  | 12 => Op 0 [6; 11]
  | _ => Arbitrary
  end.

Definition scev_shared_inventory := [0; 1; 2; 3; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14].

Definition scev_shared_loop : loop_view nat nat nat nat unit :=
  LoopView
    (Ssa.of_pure (Cfg.Make scev_shape_graph nat_encoding nat_encoding)
      nat_encoding scev_shared_inventory scev_shared_defs
      (fun x => match x with
      | 3 | 6 | 13 => 1
      | 5 | 7 | 8 | 9 | 10 | 11 | 12 | 14 => 2
      | _ => 0
      end)
      (fun _ => [3; 6; 13])
      (fun e => if Nat.eqb e 0 then [0; 1; 0] else [5; 7; 14]) (fun _ => []))
    1 (Cost.lift (fun _ => 1%N) (fun n => Nat.eqb n 1 || Nat.eqb n 2)) 0 1 None.

Definition scev_shared_e8 : scev_expr nat := SAdd 8 (SPhi 3) (SOutside 2).
Definition scev_shared_e9 : scev_expr nat := SAdd 9 scev_shared_e8 scev_shared_e8.
Definition scev_shared_e10 : scev_expr nat := SAdd 10 scev_shared_e9 scev_shared_e9.
Definition scev_shared_e11 : scev_expr nat := SAdd 11 scev_shared_e10 scev_shared_e10.

Definition scev_shared_plan : scev_plan nat :=
  ScevPlan
    [ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true;
     ScevBinding 6 1 7 SAddUpdate (Some scev_shared_e11) true;
     ScevBinding 13 0 14 SAddUpdate (Some (SAdd 12 (SPhi 6) scev_shared_e11)) true] 13.

Example scev_integrated_dag_preparation_reuses :
  match Cost.value (run_execution_c scev_shared_loop scev_shape_ops scev_shared_inventory 13) with
  | Some out =>
    prepared_nodes out = [13; 12; 6; 11; 10; 9; 8; 3; 2] /\
    preparation_reuses out = [11; 10; 9; 8; 2] /\ plan out = scev_shared_plan
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_integrated_shared_plan_checked :
  scev_plan_check scev_shared_loop scev_shape_ops scev_shared_inventory scev_shared_plan = true.
Proof.
  vm_compute; reflexivity.
Qed.
