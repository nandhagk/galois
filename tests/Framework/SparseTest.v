(** * Sparse operand observations

    Definition rows read operands in their declared order.
    For example, the old one-plus-one fixture produces two.
    Builds on: Framework.Sparse and Fixpoint.Query. *)

From Stdlib Require Import List Bool Arith ZArith.
From Galois.Base Require Import KeySig Key.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Framework Require Import SparseSig Sparse.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module Lang <: LANG_OPS.
  Definition op := unit.
  Definition guard := unit.
  Definition val := nat.
  Definition eval (_ : op) xs := Some (fold_left Nat.add xs 0).
  Definition literal (_ : op) : option Z := None.
End Lang.
Module Ops <: TYPE. Definition t := Lang.op. End Ops.
Module Guards <: TYPE. Definition t := Lang.guard. End Guards.
Module Graph <: CFG_INDEXED_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0].
  Definition edges (_ : unit) : list nat := [].
  Definition src (_ : unit) (e : nat) := e.
  Definition dst (_ : unit) (e : nat) := e.
  Definition nodes (_ : unit) := [0].
  Definition out (_ : unit) (_ : nat) : list nat := [].
  Definition inc (_ : unit) (_ : nat) : list nat := [].
End Graph.
Module Ssa <: SSA_OPS Prog NatKeyCode Edge Graph NatKeyCode Ops Guards.
  Definition values (_ : unit) := [1].
  Definition def (_ : unit) x : definition nat nat unit := if Nat.eqb x 1 then Op tt [0; 0] else Arbitrary.
  Definition home (_ : unit) (_ : nat) := 0.
  Definition params (_ : unit) (_ : nat) := [0].
  Definition args (_ : unit) (_ : nat) : list (nat * nat) := [].
  Definition guards (_ : unit) (_ : nat) : list (unit * list nat) := [].
End Ssa.
Module Values <: VALUE_DOMAIN_OPS Lang.
  Definition t := nat.
  Definition leb := Nat.leb.
  Definition bot := 0.
  Definition is_bot n := Nat.eqb n 0.
  Definition join := Nat.max.
  Definition top := 100.
  Definition meet := Nat.min.
  Definition wparam := unit.
  Definition widen (_ : unit) := Nat.max.
  Definition narrow := Nat.min.
  Definition forward (_ : unit) xs := fold_left Nat.add xs 0.
  Definition backward (_ : unit) (_ : nat) (xs : list nat) := xs.
  Definition guard (_ : unit) (xs : list nat) := xs.
End Values.
Module Transfer <: SSA_TRANSFER_OPS Prog NatKeyCode Lang Values.
  Definition seed (_ : unit) (_ : nat) := 1.
End Transfer.
Module A := SparseCode Prog NatKeyCode Edge Graph NatKeyCode Lang Ops Guards Ssa Values Transfer.
Definition look (_ : nat) := 1.

Example sparse_numeric_result :
  eval_query (A.resume tt) look (S (length (A.deps tt (SparseDef 1))))
    (A.start tt (SparseDef 1)) = Some (2, []).
Proof. vm_compute; reflexivity. Qed.
