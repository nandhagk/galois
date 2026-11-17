(** * Parallel move examples

    These examples cover cycles, fan-out and rejection of an unsafe move order.
    For example, a swap needs a temporary whereas an independent move does not.

    Groups:
    - SequenceTests: the sequential moves that a parallel move expands to.
    - CheckTests: which move lists the checker accepts.
    - AgreementTests: whether a parallel table agrees with its symbolic form.

    Builds on: ParMove and ParMoveSig. *)

From Stdlib Require Import List PArith.
From Galois.Ssa Require Import ParMoveSig ParMove.
Import List.ListNotations.

(** * Sequences *)

Module SequenceTests.

  Local Open Scope positive_scope.

  (** A swap is sequenced through the temporary 3. *)
  Example swap_is_sequenced_through_temporary :
    ParMoveCode.seq [(1, 2); (2, 1)] 3 = [(3, 2); (2, 1); (1, 3)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End SequenceTests.

(** * Checks *)

Module CheckTests.

  Local Open Scope positive_scope.

  (** Three disjoint cycles, each of ten vertices. *)
  Definition three_cycles : moves :=
    [(1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 7); (7, 8); (8, 9); (9, 10); (10, 1);
     (11, 12); (12, 13); (13, 14); (14, 15); (15, 16); (16, 17); (17, 18); (18, 19);
     (19, 20); (20, 11); (21, 22); (22, 23); (23, 24); (24, 25); (25, 26); (26, 27);
     (27, 28); (28, 29); (29, 30); (30, 21)].

  (** The sequence of a swap passes the move check. *)
  Example swap_sequence_passes_check :
    ParMoveCode.check_moves [(1, 2); (2, 1)] 3 (ParMoveCode.seq [(1, 2); (2, 1)] 3) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A swap written without a temporary is rejected. *)
  Example unsequenced_swap_is_rejected :
    ParMoveCode.check_moves [(1, 2); (2, 1)] 3 [(1, 2); (2, 1)] = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The sequence of a fan-out passes the move check. *)
  Example fanout_sequence_passes_check :
    ParMoveCode.check_moves [(2, 4); (1, 2); (3, 2)] 5
      (ParMoveCode.seq [(2, 4); (1, 2); (3, 2)] 5) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The sequence of a cycle with a fan-out passes the move check. *)
  Example cycle_with_fanout_passes_check :
    ParMoveCode.check_moves [(1, 2); (2, 1); (3, 1)] 4
      (ParMoveCode.seq [(1, 2); (2, 1); (3, 1)] 4) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** When a source has two destinations, the first move is the one that is written. *)
  Example first_destination_wins :
    ParMoveCode.check_moves [(1, 2); (1, 3)] 4 [(1, 2)] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A write that the parallel move does not contain is rejected. *)
  Example extra_write_is_rejected :
    ParMoveCode.check_moves [] 4 [(1, 2)] = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The sequence of three disjoint cycles passes the move check. *)
  Example three_cycles_pass_check :
    ParMoveCode.check_moves three_cycles 31 (ParMoveCode.seq three_cycles 31) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CheckTests.

(** * Agreement *)

Module AgreementTests.

  Local Open Scope positive_scope.

  (** A move into the temporary agrees with its symbolic form. *)
  Example temporary_destination_agrees_with_symbolic :
    move_agrees (parallel_table [(31, 1)]) (ParMoveCode.symbolic_all [(31, 2)]) 31 31 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A move into an ordinary variable disagrees with a symbolic form of another destination. *)
  Example ordinary_destination_disagrees_with_symbolic :
    move_agrees (parallel_table [(1, 2)]) (ParMoveCode.symbolic_all [(1, 3)]) 31 1 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AgreementTests.
