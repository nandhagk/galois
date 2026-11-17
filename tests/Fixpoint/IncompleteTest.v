(** * Incomplete dependency declarations

    The evaluator rejects a row when its declared dependencies do not supply enough fuel.
    For example, a declared empty list cannot evaluate a query that reads one key.

    Groups:
    - [SummaryTests] The solver and the certified analysis both reject the incomplete summary.

    Builds on: Fixpoint.Worklist and Fixpoint.Certified. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Heap.
From Galois.Fixpoint Require Import Query SystemSig SolverSig Check Narrow Worklist Certified.
From Galois.Tests.Fixpoint Require Import WorklistTest.
Import List.ListNotations.

(** * Fixtures *)

(** A system whose row 1 asks for key 2, but declares no dependencies. *)
Module Incomplete <: SYSTEM_OPS BoolOps.
  Definition prog := unit.
  Definition key := positive.
  Definition row := positive.
  Definition frame := unit.
  Definition key_code (x : positive) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (_ : unit) := [1; 2]%positive.
  Definition target (_ : unit) (r : positive) := r.
  Definition start (_ : unit) (r : positive) : query key bool unit :=
    if Pos.eqb r 1 then Ask 2%positive tt else Ret true.
  Definition resume (_ : unit) (_ : unit) (a : bool) : query key bool unit := Ret a.
  Definition deps (_ : unit) (_ : positive) : list positive := [].
  Definition sides (_ : unit) (_ : positive) : list positive := [].
End Incomplete.
Module C := CheckCode BoolOps Incomplete.
Module R := NarrowCode BoolOps Incomplete C.
Module W := WorklistCode BoolOps Incomplete P HeapCode.
Module A := CertifiedCode BoolOps Incomplete W C R.

(** * Summary *)

Module SummaryTests.

  (** The solver rejects the incomplete summary with Check_failed. *)
  Example solver_rejects_incomplete_summary :
    W.run tt flat 3%N = Rejected Check_failed.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The certified analysis rejects the incomplete summary with Check_failed. *)
  Example certified_rejects_incomplete_summary :
    A.analyze tt flat 3%N = Rejected Check_failed.
  Proof.
    vm_compute; reflexivity.
  Qed.

End SummaryTests.
