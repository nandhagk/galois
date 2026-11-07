(** * Operator tactic clients

    The default hook solves bitwise cases and leaves all other operators to the client.
    For example, the client handles every remaining operator through a non-bitwise witness.
    Builds on: BitsOp and BitsTactics. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import BitsOp BitsTactics.
Import List.ListNotations.

Ltac op_default ::= left; reflexivity.

(** The hook closes exactly the bitwise cases and every remaining goal is non-bitwise. *)
Example bitwise_default_client : forall o,
  Desc.kind (op_desc o) = Desc.Bitwise \/
    exists k, Desc.kind (op_desc o) = k /\ k <> Desc.Bitwise.
Proof.
  intro o. op_cases o.
  all: right; eexists; split; [reflexivity|discriminate].
Qed.

(** An explicit failing default leaves every constructor available to the client. *)
Example explicit_default_residue : forall o, arity o = arity o.
Proof.
  intro o. op_cases o by fail.
  all: reflexivity.
Qed.

(** Kind splitting uses the same conservative default contract. *)
Example kind_default_client : forall k : Desc.kind_tag,
  k = Desc.Bitwise \/ k <> Desc.Bitwise.
Proof.
  intro k. kind_cases k.
  all: right; discriminate.
Qed.

(** The operator and descriptor remain directly computable in a tactic client. *)
Example tactic_client_boundary :
  result_width bvnot [] = None /\ result_width bvand [1%positive; 2%positive] = None /\
  result_width bvand [1%positive; 1%positive] = Some 1%positive.
Proof.
  vm_compute. repeat split.
Qed.
