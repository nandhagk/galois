(** * Generic expression examples

    Expressions normalize variables and constants and propagate argument failures.
    For example, a malformed nested application rejects its enclosing application.
    Builds on: BitsWord, BitsOp and BitsExpr. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
Import List.ListNotations Expr.

Open Scope Z_scope.

(** Nested applications normalize entries and read a wrapped one-bit condition. *)
Example expression_evaluation :
  eval eval_op (env_of (1%positive, 0) [(8%positive, 200); (8%positive, 100)])
    (App bvite [Const 1%positive 3;
      App bvadd [Var 0; Var 1]; Const 8%positive 17]) = Some (8%positive, 44) /\
  eval eval_op (env_of (1%positive, 0) []) (Var 9) = Some (1%positive, 0) /\
  eval_args eval_op (env_of (1%positive, 0) [])
    [Const 8%positive 260; App bvadd []] = None.
Proof.
  vm_compute. repeat split.
Qed.

Definition unit_eval (_ : unit) (xs : list word) : option word :=
  match xs with
  | [x] => Some x
  | _ => None
  end.

(** A second operator language uses the same syntax and preserves a custom default. *)
Example generic_expression :
  eval unit_eval (env_of (3%positive, 10) []) (App tt [Var 8]) = Some (3%positive, 2) /\
  eval unit_eval (env_of (1%positive, 0) []) (App tt []) = None /\
  eval_args unit_eval (env_of (1%positive, 0) []) [] = Some [].
Proof.
  vm_compute. repeat split.
Qed.
