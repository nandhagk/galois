(** * Operator tactic clients

    The default hook solves bitwise cases and leaves all other operators to the client.
    For example, the client handles every remaining operator through a non-bitwise witness.
    Builds on: Op and Tactics. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Op Tactics.
Import List.ListNotations.

Ltac op_default ::= left; reflexivity.


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

(** The operator width checks remain directly computable in a tactic client. *)
Example tactic_client_boundary :
  result_width bvnot [] = None /\ result_width bvand [1%positive; 2%positive] = None /\
  result_width bvand [1%positive; 1%positive] = Some 1%positive.
Proof.
  vm_compute. repeat split.
Qed.
