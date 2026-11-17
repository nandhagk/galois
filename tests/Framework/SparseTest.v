(** * Sparse operand observations

    Definition rows read operands in their declared order.
    For example, a definition whose two operands are both 1 evaluates to 2.

    Groups:
    - Operands: a sparse definition evaluates its operands and gives the numeric result.

    Builds on: Framework.Sparse and Fixpoint.Query. *)

From Stdlib Require Import List Bool Arith ZArith.
From Galois.Base Require Import KeySig Key.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Framework Require Import SparseSig Sparse.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.

(** A language whose operations add their operands, and which has no literals. *)
Module Lang <: LANG_OPS.
  Definition op := unit.
  Definition guard := unit.
  Definition val := nat.
  Definition eval (_ : op) xs := Some (fold_left Nat.add xs 0).
  Definition literal (_ : op) : option Z := None.
End Lang.

Module Ops <: TYPE. Definition t := Lang.op. End Ops.
Module Guards <: TYPE. Definition t := Lang.guard. End Guards.

(** A one-node graph with entry 0 and no edges. *)
Module Graph <: CFG_INDEXED_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0].
  Definition edges (_ : unit) : list nat := [].
  Definition src (_ : unit) (e : nat) := e.
  Definition dst (_ : unit) (e : nat) := e.
  Definition nodes (_ : unit) := [0].
  Definition out (_ : unit) (_ : nat) : list nat := [].
  Definition inc (_ : unit) (_ : nat) : list nat := [].
End Graph.

(** One SSA value, 1, defined by an operation on the value 0 twice. *)
Module Ssa <: SSA_OPS Prog NatKeyCode Edge Graph NatKeyCode Ops Guards.
  Definition values (_ : unit) := [1].
  Definition def (_ : unit) x : definition nat nat unit := if Nat.eqb x 1 then Op tt [0; 0] else Arbitrary.
  Definition home (_ : unit) (_ : nat) := 0.
  Definition params (_ : unit) (_ : nat) := [0].
  Definition args (_ : unit) (_ : nat) : list (nat * nat) := [].
  Definition guards (_ : unit) (_ : nat) : list (unit * list nat) := [].
  Definition entry_params p := flat_map (params p) (Graph.entries p).
  Definition arg_rows p := flat_map (fun e => map (pair e) (args p e)) (Graph.edges p).
End Ssa.

(** Natural numbers ordered as a value domain, with 0 as bottom and 100 as top. *)
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

(** Every seed is the value 1. *)
Module Transfer <: SSA_TRANSFER_OPS Prog NatKeyCode Lang Values.
  Definition seed (_ : unit) (_ : nat) := 1.
End Transfer.

Module A := SparseCode Prog NatKeyCode Edge Graph NatKeyCode Lang Ops Guards Ssa Values Transfer.

(** The environment that gives every key the value 1. *)
Definition look (_ : nat) := 1.

(** * Operands *)

Module OperandTests.

  (** The definition of value 1 reads its two operands, both 1, and evaluates to 2. *)
  Example operands_add_to_two :
    eval_query (A.resume tt) look (S (length (A.deps tt (SparseDef 1))))
      (A.start tt (SparseDef 1)) = Some (2, []).
  Proof.
    vm_compute; reflexivity.
  Qed.

End OperandTests.
