(** * Incomplete dependency declarations

    The evaluator rejects a row when its declared dependencies do not supply enough fuel.
    For example, a declared empty list cannot evaluate a query that reads one key.
    Builds on: Fixpoint.Worklist and Fixpoint.Certified. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Heap.
From Galois.Fixpoint Require Import Query SystemSig SolverSig Check Narrow Worklist Certified.
From Galois.Tests.Fixpoint Require Import WorklistTest.
Import List.ListNotations.

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

(* The old solver returned Solved [false; true] and certification returned
   Rejected Check_failed. The new query fuel comes from dependencies, so both
   the solver and certification return Rejected Check_failed. *)
Example incomplete_summary_rejected :
  (W.run tt flat 3%N, A.analyze tt flat 3%N) =
    (Rejected Check_failed, Rejected Check_failed).
Proof.
  vm_compute; reflexivity.
Qed.
