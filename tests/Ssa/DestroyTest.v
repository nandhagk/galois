(** * SSA destruction examples

    These examples check branch-edge copies, swaps, missing values and malformed arities.
    For example, swapping loop parameters requires a checked temporary on the back edge.
    Builds on: DestroyCode, ParMoveCode and the block interpreter. *)

From Stdlib Require Import List PArith Arith.
From Galois.Base Require Import KeySig Key.
From Galois.Ssa Require Import Lang ParMove Destroy.

Import List.ListNotations.

Module MoveOps <: OPS.
  Definition K := unit.
  Definition G := unit.
  Definition C := nat.
  Definition eval (_ : K) (cs : list C) : option C :=
    match cs with [c] => Some c | _ => None end.
  Definition test (_ : G) (cs : list C) : option bool :=
    match cs with [c] => Some (Nat.eqb c 0) | _ => None end.
  Definition mov : K := tt.
End MoveOps.

Module ProgramType <: TYPE.
  Definition t := func positive unit unit.
End ProgramType.

Module DS := DestroyCode MoveOps UnitKeyCode UnitKeyCode ProgramType ParMoveCode.

Definition swap_loop : ProgramType.t :=
  Func _ _ _ 1%positive [1%positive; 2%positive]
    [(1%positive, Block _ _ _ [] [] (Jump 2%positive [1%positive; 2%positive]));
     (2%positive, Block _ _ _ [3%positive; 4%positive] []
       (Branch tt [3%positive] 2%positive [4%positive; 3%positive] 3%positive []));
     (3%positive, Block _ _ _ [] [] (Return [3%positive; 4%positive]))].

Example swap_loop_source :
  run_with MoveOps.eval MoveOps.test 4 swap_loop [0; 9] = Returned [9; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example swap_loop_destroyed :
  option_map (fun p => run_with MoveOps.eval MoveOps.test 8 p [0; 9])
    (DS.destroy swap_loop) = Some (Returned [9; 0]).
Proof.
  vm_compute. reflexivity.
Qed.

Example swap_loop_split_blocks :
  option_map (fun p => length (blocks _ _ _ p)) (DS.destroy swap_loop) = Some 4.
Proof.
  vm_compute. reflexivity.
Qed.

Definition missing_self_copy : ProgramType.t :=
  Func _ _ _ 1%positive []
    [(1%positive, Block _ _ _ [] [] (Jump 2%positive [3%positive]));
     (2%positive, Block _ _ _ [3%positive] [] (Return []))].

Example missing_self_copy_source :
  run_with MoveOps.eval MoveOps.test 1 missing_self_copy [] = Wrong.
Proof.
  vm_compute. reflexivity.
Qed.

Example missing_self_copy_destroyed :
  option_map (fun p => run_with MoveOps.eval MoveOps.test 1 p [])
    (DS.destroy missing_self_copy) = Some Wrong.
Proof.
  vm_compute. reflexivity.
Qed.

Definition already_imperative : ProgramType.t :=
  Func _ _ _ 1%positive [2%positive]
    [(1%positive, Block _ _ _ [] [] (Return [2%positive]))].

Example imperative_unchanged : DS.destroy already_imperative = Some already_imperative.
Proof.
  vm_compute. reflexivity.
Qed.

Definition entry_parameters : ProgramType.t :=
  Func _ _ _ 1%positive [] [(1%positive, Block _ _ _ [2%positive] [] (Return []))].

Example entry_parameters_rejected : DS.destroy entry_parameters = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition mismatched_arity : ProgramType.t :=
  Func _ _ _ 1%positive [1%positive]
    [(1%positive, Block _ _ _ [] [] (Jump 2%positive [1%positive]));
     (2%positive, Block _ _ _ [3%positive; 4%positive] [] (Return []))].

Example mismatched_arity_rejected : DS.destroy mismatched_arity = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition duplicate_parameters : ProgramType.t :=
  Func _ _ _ 1%positive [1%positive; 2%positive]
    [(1%positive, Block _ _ _ [] [] (Jump 2%positive [1%positive; 2%positive]));
     (2%positive, Block _ _ _ [3%positive; 3%positive] [] (Return []))].

Example duplicate_parameters_rejected : DS.destroy duplicate_parameters = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example valid_move_preconditions :
  DS.moves_ok [(1%positive, 2%positive); (2%positive, 1%positive)] 3%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example duplicate_move_preconditions_rejected :
  DS.moves_ok [(1%positive, 2%positive); (1%positive, 3%positive)] 4%positive = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example temporary_move_preconditions_rejected :
  DS.moves_ok [(1%positive, 2%positive); (2%positive, 1%positive)] 2%positive = false.
Proof.
  vm_compute. reflexivity.
Qed.
