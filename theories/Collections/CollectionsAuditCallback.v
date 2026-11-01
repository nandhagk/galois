(** * Actual foreign callback source adapters

    These laws connect each genuine foreign call's argument, result and retained body to source
      work.
    For example, an operand call retains its exact node and incoming key before its input budget
      applies.
    Builds on: Rocq Stdlib lists. *)

From Stdlib Require Import List.

(** Foreign clients justify their own bodies; this relation cannot price an internal library
  call. *)
Record audit_external_callback_adapter {A R B : Type} (call : A -> R * list B)
    (work : list B -> nat) (source : A -> R -> list B -> nat -> Prop)
    (budget : A -> nat) : Prop := AuditExternalCallbackAdapter {
  audit_external_callback_source : forall argument result body,
    call argument = (result, body) -> source argument result body (work body);
  audit_external_callback_input_bound : forall argument result body,
    call argument = (result, body) -> work body <= budget argument
}.

(** Every observed call is charged at the same returned body and actual input. *)
Definition audit_external_callback_observed_statement : Prop :=
  forall A R B (call : A -> R * list B) work source budget,
    audit_external_callback_adapter call work source budget ->
    forall argument,
      source argument (fst (call argument)) (snd (call argument)) (work (snd (call argument))) /\
      work (snd (call argument)) <= budget argument.
