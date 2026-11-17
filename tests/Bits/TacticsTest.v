(** * Operator tactic clients

    The default hook solves bitwise cases and leaves all other operators to the client.
    For example, the client handles every remaining operator through a non-bitwise witness.
    Builds on: Op and Tactics.

    Groups:
    - [DefaultTests] The cases that the operator and kind tactics leave to the client.
    - [WidthTests] The result widths that the operator checks give. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Op Tactics.
Import List.ListNotations.

(** The default hook of the operator tactic solves its goal with the left constructor. *)
Ltac op_default ::= left; reflexivity.

(** * Defaults *)

Module DefaultTests.

  (** An explicit failing default leaves every constructor available to the client. *)
  Example explicit_failing_default_keeps_constructors : forall o, arity o = arity o.
  Proof.
    intro o. op_cases o by fail.
    all: reflexivity.
  Qed.

  (** Kind splitting leaves each kind either bitwise or not bitwise. *)
  Example kind_split_is_bitwise_or_not : forall k : Desc.kind_tag,
    k = Desc.Bitwise \/ k <> Desc.Bitwise.
  Proof.
    intro k. kind_cases k.
    all: right; discriminate.
  Qed.

End DefaultTests.

(** * Widths *)

Module WidthTests.

  (** A unary operator with no operands has no result width. *)
  Example unary_result_width_without_operands_is_none : result_width bvnot [] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A bitwise operator with operands of unequal widths has no result width. *)
  Example bitwise_result_width_rejects_unequal_widths :
    result_width bvand [1%positive; 2%positive] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A bitwise operator with equal operand widths keeps that width. *)
  Example bitwise_result_width_keeps_equal_width :
    result_width bvand [1%positive; 1%positive] = Some 1%positive.
  Proof.
    vm_compute. reflexivity.
  Qed.

End WidthTests.
