(** * Positional harness fixtures

    Backward and guard dispatch accept only tables with the original operand count.
    For example, a short table leaves every input unchanged.
    Builds on: Harness. *)

From Stdlib Require Import List Arith ZArith.
From Galois.Domains Require Import Harness.
Import List.ListNotations.

Module PositionLanguage.
  Definition op := nat.
  Definition guard := nat.
  Definition val := nat.
  Definition eval (_ : op) (_ : list val) : option val := None.
  Definition literal (_ : op) : option Z := None.
End PositionLanguage.

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

Module PositionHarness := HarnessCode PositionLanguage PositionBase PositionTable.

(** Equal-length backward entries meet each original position. *)
Example backward_positions : PositionHarness.backward 0 7 [5; 1] = [2; 1].
Proof.
  vm_compute. reflexivity.
Qed.

(** A short backward entry cannot drop an operand. *)
Example backward_short : PositionHarness.backward 1 7 [5; 1] = [5; 1].
Proof.
  vm_compute. reflexivity.
Qed.

(** A long backward entry cannot append an operand. *)
Example backward_long : PositionHarness.backward 2 7 [5; 1] = [5; 1].
Proof.
  vm_compute. reflexivity.
Qed.

(** Equal-length guard entries meet each original position. *)
Example guard_positions : PositionHarness.guard 0 [5; 1] = [2; 1].
Proof.
  vm_compute. reflexivity.
Qed.

(** Guard dispatch also rejects both shorter and longer entries. *)
Example guard_lengths :
  (PositionHarness.guard 1 [5; 1], PositionHarness.guard 2 [5; 1]) =
    ([5; 1], [5; 1]).
Proof.
  vm_compute. reflexivity.
Qed.

(** The positional helper preserves an unmatched original suffix. *)
Example meet_all_suffix : PositionHarness.meet_all [5; 4; 3] [2] = [2; 4; 3].
Proof.
  vm_compute. reflexivity.
Qed.
