(** * Generic expression examples

    Expressions normalize variables and constants and propagate argument failures.
    For example, a malformed nested application rejects its enclosing application.
    Builds on: Word, Op and Expr.

    Groups:
    - [EvaluationTests] Nested applications, unbound variables and malformed arguments.
    - [GenericTests] A second operator language that uses the same syntax. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op Expr.
Import List.ListNotations Expr.

Open Scope Z_scope.

(** * Evaluation *)

Module EvaluationTests.

  (** A nested application reads a wrapped one-bit condition and adds two variables. *)
  Example nested_application_evaluates :
    eval eval_op (env_of (1%positive, 0) [(8%positive, 200); (8%positive, 100)])
      (App bvite [Const 1%positive 3;
        App bvadd [Var 0; Var 1]; Const 8%positive 17]) = Some (8%positive, 44).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An unbound variable evaluates to the default word of width one and value zero. *)
  Example unbound_variable_defaults_to_zero :
    eval eval_op (env_of (1%positive, 0) []) (Var 9) = Some (1%positive, 0).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A malformed argument makes the enclosing argument list fail. *)
  Example malformed_argument_rejects_arguments :
    eval_args eval_op (env_of (1%positive, 0) [])
      [Const 8%positive 260; App bvadd []] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EvaluationTests.

(** * Generic *)

Module GenericTests.

  (** A second operator language applies its unary operator to a variable. *)
  Definition unit_eval (_ : unit) (xs : list word) : option word :=
    match xs with
    | [x] => Some x
    | _ => None
    end.

  (** The unary operator of the second language applies to a variable of the environment. *)
  Example custom_language_applies_unary_operator :
    eval unit_eval (env_of (3%positive, 10) []) (App tt [Var 8]) = Some (3%positive, 2).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The second language rejects an application with no argument. *)
  Example custom_language_rejects_missing_argument :
    eval unit_eval (env_of (1%positive, 0) []) (App tt []) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty argument list evaluates to an empty list of words. *)
  Example empty_arguments_evaluate_to_empty :
    eval_args unit_eval (env_of (1%positive, 0) []) [] = Some [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End GenericTests.
