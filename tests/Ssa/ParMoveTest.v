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

Definition three_cycles : moves :=
  [(1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 7); (7, 8); (8, 9); (9, 10); (10, 1);
   (11, 12); (12, 13); (13, 14); (14, 15); (15, 16); (16, 17); (17, 18); (18, 19);
   (19, 20); (20, 11); (21, 22); (22, 23); (23, 24); (24, 25); (25, 26); (26, 27);
   (27, 28); (28, 29); (29, 30); (30, 21)].

Example three_cycles_checked :
  ParMoveCode.check_moves three_cycles 31 (ParMoveCode.seq three_cycles 31) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example temporary_destination_agrees :
  move_agrees (parallel_table [(31, 1)]) (ParMoveCode.symbolic_all [(31, 2)]) 31 31 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example ordinary_destination_disagrees :
  move_agrees (parallel_table [(1, 2)]) (ParMoveCode.symbolic_all [(1, 3)]) 31 1 = false.
Proof.
  vm_compute. reflexivity.
Qed.
