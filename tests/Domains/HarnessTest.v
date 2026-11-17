(** * Positional harness fixtures

    Backward and guard dispatch accept only tables with the original operand count.
    For example, a short table leaves every input unchanged.
    Builds on: Harness. *)

(* Groups:
   - Fixtures: a position language, a natural base, a table of candidates and the harness.
   - Backward: backward entries of equal, shorter and longer length.
   - Guard: guard entries of equal, shorter and longer length.
   - Helpers: the positional meet of two lists. *)

From Stdlib Require Import List Arith ZArith.
From Galois.Domains Require Import Harness.
Import List.ListNotations.

(** * Fixtures *)

(** Operators, guards and values are naturals, and no operator evaluates. *)
Module PositionLanguage.
  Definition op := nat.
  Definition guard := nat.
  Definition val := nat.
  Definition eval (_ : op) (_ : list val) : option val := None.
  Definition literal (_ : op) : option Z := None.
End PositionLanguage.

(** Naturals ordered as usual, with zero as bottom and seven as top. *)
Module PositionBase.
  Definition t := nat.
  Definition leb := Nat.leb.
  Definition bot := 0.
  Definition is_bot (x : t) := Nat.eqb x 0.
  Definition join := Nat.max.
  Definition top := 7.
  Definition meet := Nat.min.
  Definition wparam := unit.
  Definition widen (_ : wparam) := join.
  Definition narrow := meet.
  Definition point (_ : t) : option nat := None.
  Definition abst (x : nat) := x.
End PositionBase.

(** Candidate lists of length two, one and three, and none for other keys. *)
Module PositionTable.
  Definition fwd (_ : nat) (_ : list nat) : option nat := None.
  Definition candidates (k : nat) : option (list nat) :=
    match k with
    | 0 => Some [2; 3]
    | 1 => Some [2]
    | 2 => Some [2; 3; 4]
    | _ => None
    end.
  Definition bwd (k : nat) (_ : nat) (_ : list nat) := candidates k.
  Definition grd (k : nat) (_ : list nat) := candidates k.
End PositionTable.

(** The harness over the position language, base and table. *)
Module PositionHarness := HarnessCode PositionLanguage PositionBase PositionTable.

(** * Backward *)

Module BackwardTests.

  (** An entry of the same length meets each original position. *)
  Example equal_length_meets_positions : PositionHarness.backward 0 7 [5; 1] = [2; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A shorter entry leaves the operands unchanged. *)
  Example shorter_entry_keeps_operands : PositionHarness.backward 1 7 [5; 1] = [5; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A longer entry leaves the operands unchanged. *)
  Example longer_entry_keeps_operands : PositionHarness.backward 2 7 [5; 1] = [5; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

End BackwardTests.

(** * Guard *)

Module GuardTests.

  (** A guard entry of the same length meets each original position. *)
  Example equal_length_guard_meets_positions : PositionHarness.guard 0 [5; 1] = [2; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A shorter guard entry leaves the operands unchanged. *)
  Example shorter_guard_keeps_operands : PositionHarness.guard 1 [5; 1] = [5; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A longer guard entry leaves the operands unchanged. *)
  Example longer_guard_keeps_operands : PositionHarness.guard 2 [5; 1] = [5; 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

End GuardTests.

(** * Helpers *)

Module HelperTests.

  (** The positional meet keeps the suffix of the longer list that has no partner. *)
  Example meet_all_keeps_unmatched_suffix :
    PositionHarness.meet_all [5; 4; 3] [2] = [2; 4; 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

End HelperTests.
