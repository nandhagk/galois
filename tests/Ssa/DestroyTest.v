(** * SSA destruction examples

    These examples check branch-edge copies, swaps, missing values and malformed arities.
    For example, swapping loop parameters requires a checked temporary on the back edge.

    Groups:
    - SwapLoopTests: a loop whose back edge swaps two parameters.
    - MissingValueTests: a source that reads a value that is never defined.
    - ImperativeTests: a program that is already imperative.
    - MalformedTests: programs with malformed parameters or arities.
    - MoveTests: the preconditions of a parallel move.
    - CopyBlockTests: the copies of one block's edge.

    Builds on: DestroyCode, ParMoveCode and the block interpreter. *)

From Stdlib Require Import List PArith Arith.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Ssa Require Import Lang ParMove Destroy.
Import List.ListNotations.

(** The test operations: a move that returns its single operand. *)
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

(** The programs that the examples destroy. *)
Module ProgramType <: TYPE.
  Definition t := func positive unit unit.
End ProgramType.

(** The destruction of the test programs. *)
Module DS := DestroyCode MoveOps UnitKeyCode UnitKeyCode ProgramType ParMoveCode.

(** * Swap loop *)

Module SwapLoopTests.

  (** A loop whose back edge swaps two parameters, in the source. *)
  Definition swap_loop : ProgramType.t :=
    Func _ _ _ 1%positive [1%positive; 2%positive]
      [(1%positive, Block _ _ _ [] [] (Jump 2%positive [1%positive; 2%positive]));
       (2%positive, Block _ _ _ [3%positive; 4%positive] []
         (Branch tt [3%positive] 2%positive [4%positive; 3%positive] 3%positive []));
       (3%positive, Block _ _ _ [] [] (Return [3%positive; 4%positive]))].

  (** The source loop returns the two parameters swapped. *)
  Example source_swaps_parameters :
    run_with MoveOps.eval MoveOps.test 4 swap_loop [0; 9] = Returned [9; 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The destroyed loop returns the same swapped parameters. *)
  Example destroyed_program_swaps_parameters :
    option_map (fun p => run_with MoveOps.eval MoveOps.test 8 p [0; 9])
      (DS.destroy swap_loop) = Some (Returned [9; 0]).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Destroying the swap loop gives a program of four blocks. *)
  Example swap_splits_into_four_blocks :
    option_map (fun p => length (blocks _ _ _ p)) (DS.destroy swap_loop) = Some 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SwapLoopTests.

(** * Missing value *)

Module MissingValueTests.

  Local Open Scope positive_scope.

  (** A jump that passes a value the block never defines. *)
  Definition missing_self_copy : ProgramType.t :=
    Func _ _ _ 1 []
      [(1, Block _ _ _ [] [] (Jump 2 [3]));
       (2, Block _ _ _ [3] [] (Return []))].

  (** The source program is wrong when it runs, since the value is missing. *)
  Example source_with_missing_value_is_wrong :
    run_with MoveOps.eval MoveOps.test 1 missing_self_copy [] = Wrong.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The destroyed program is wrong in the same way. *)
  Example destroyed_program_with_missing_value_is_wrong :
    option_map (fun p => run_with MoveOps.eval MoveOps.test 1 p [])
      (DS.destroy missing_self_copy) = Some Wrong.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MissingValueTests.

(** * Imperative *)

Module ImperativeTests.

  Local Open Scope positive_scope.

  (** A program with no parameter copies is returned unchanged. *)
  Definition already_imperative : ProgramType.t :=
    Func _ _ _ 1 [2]
      [(1, Block _ _ _ [] [] (Return [2]))].

  Example imperative_program_is_unchanged :
    DS.destroy already_imperative = Some already_imperative.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ImperativeTests.

(** * Malformed *)

Module MalformedTests.

  Local Open Scope positive_scope.

  (** An entry block that declares a parameter. *)
  Definition entry_parameters : ProgramType.t :=
    Func _ _ _ 1 [] [(1, Block _ _ _ [2] [] (Return []))].

  (** The entry block cannot take parameters, so the program is rejected. *)
  Example entry_parameters_are_rejected :
    DS.destroy entry_parameters = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A jump with one argument into a block with two parameters is rejected. *)
  Definition mismatched_arity : ProgramType.t :=
    Func _ _ _ 1 [1]
      [(1, Block _ _ _ [] [] (Jump 2 [1]));
       (2, Block _ _ _ [3; 4] [] (Return []))].

  Example mismatched_arity_is_rejected :
    DS.destroy mismatched_arity = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A block whose parameter list repeats a variable is rejected. *)
  Definition duplicate_parameters : ProgramType.t :=
    Func _ _ _ 1 [1; 2]
      [(1, Block _ _ _ [] [] (Jump 2 [1; 2]));
       (2, Block _ _ _ [3; 3] [] (Return []))].

  Example duplicate_parameters_are_rejected :
    DS.destroy duplicate_parameters = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MalformedTests.

(** * Moves *)

Module MoveTests.

  Local Open Scope positive_scope.

  (** Two distinct moves that swap two variables are accepted, with 3 as the temporary. *)
  Example distinct_swap_moves_are_accepted :
    DS.moves_ok [(1, 2); (2, 1)] 3 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A variable that is the source of two moves is rejected. *)
  Example duplicate_move_source_is_rejected :
    DS.moves_ok [(1, 2); (1, 3)] 4 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A temporary that a move already uses is rejected. *)
  Example temporary_used_by_a_move_is_rejected :
    DS.moves_ok [(1, 2); (2, 1)] 2 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MoveTests.

(** * Copy blocks *)

Module CopyBlockTests.

  Local Open Scope positive_scope.

  (** Copying a jump with two arguments gives the copies on its edge, with the temporary 5. *)
  Example copy_block_lists_its_copies :
    DS.copy_block (PTrieCode.set 2 [3; 4] Empty) 5
      (Block _ _ _ [] [] (Jump 2 [4; 3])) =
    Some (Block _ _ _ []
      [(5, tt, [4]); (5, tt, [3]);
       (5, tt, [4]); (4, tt, [3]);
       (3, tt, [5])] (Jump 2 []),
      Some ([(3, 4); (4, 3)], 5,
        [(5, 4); (4, 3); (3, 5)])).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A copy whose source list repeats a variable is rejected. *)
  Example duplicate_copy_source_is_rejected :
    DS.copy_block (PTrieCode.set 2 [3; 3] Empty) 5
      (Block _ _ _ [] [] (Jump 2 [1; 2])) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CopyBlockTests.
