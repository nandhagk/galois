(** * Parallel move examples

    These examples cover cycles, fan-out and rejection of an unsafe move order.
    For example, a swap needs a temporary whereas an independent move does not.
    Builds on: ParMove and ParMoveSig. *)

From Stdlib Require Import List PArith.
From Galois.Ssa Require Import ParMoveSig ParMove.

Import List.ListNotations.
Local Open Scope positive_scope.

Example swap_sequence :
  ParMoveCode.seq [(1, 2); (2, 1)] 3 = [(3, 2); (2, 1); (1, 3)]%positive.
Proof. vm_compute. reflexivity. Qed.

Example swap_checked :
  ParMoveCode.check_moves [(1, 2); (2, 1)] 3 (ParMoveCode.seq [(1, 2); (2, 1)] 3) = true.
Proof. vm_compute. reflexivity. Qed.

Example unsafe_swap_rejected :
  ParMoveCode.check_moves [(1, 2); (2, 1)] 3 [(1, 2); (2, 1)] = false.
Proof. vm_compute. reflexivity. Qed.

Example fanout_checked :
  ParMoveCode.check_moves [(2, 4); (1, 2); (3, 2)] 5
    (ParMoveCode.seq [(2, 4); (1, 2); (3, 2)] 5) = true.
Proof. vm_compute. reflexivity. Qed.

Example cycle_and_fanout_checked :
  ParMoveCode.check_moves [(1, 2); (2, 1); (3, 1)] 4
    (ParMoveCode.seq [(1, 2); (2, 1); (3, 1)] 4) = true.
Proof. vm_compute. reflexivity. Qed.

Example first_parallel_destination_wins :
  ParMoveCode.check_moves [(1, 2); (1, 3)] 4 [(1, 2)] = true.
Proof. vm_compute. reflexivity. Qed.

Example extra_write_rejected :
  ParMoveCode.check_moves [] 4 [(1, 2)] = false.
Proof. vm_compute. reflexivity. Qed.
