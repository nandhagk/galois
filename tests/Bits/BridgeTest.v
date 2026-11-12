(** * Bridge and width-changing expression examples

    Consecutive variables preserve operand order and extensions preserve low bits.
    For example, subtraction through variables zero and one retains their order.
    Builds on: Word, Op, Expr and Bridge. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op Expr Bridge.
Import List.ListNotations Expr.

Open Scope Z_scope.

(** The bridge's consecutive variable list preserves both addition and subtraction. *)
Example bridge_application :
  eval eval_op (env_of (1%positive, 0) [(8%positive, 200); (8%positive, 100)])
    (App bvadd (vars (arity bvadd))) = Some (8%positive, 44) /\
  eval eval_op (env_of (1%positive, 0) [(8%positive, 3); (8%positive, 7)])
    (App bvsub (vars (arity bvsub))) = Some (8%positive, 252).
Proof.
  vm_compute. repeat split.
Qed.

(** Zero and sign extension give different larger unsigned representations. *)
Example extension_values :
  eval eval_op (env_of (1%positive, 0) [(8%positive, 255)])
    (App (bvzext 8%positive) [Var 0]) = Some (16%positive, 255) /\
  eval eval_op (env_of (1%positive, 0) [(8%positive, 255)])
    (App (bvsext 8%positive) [Var 0]) = Some (16%positive, 65535).
Proof.
  vm_compute. repeat split.
Qed.

(** Truncation recovers an extended word and commutes with an overflowing sum. *)
Example truncation_values :
  eval eval_op (env_of (1%positive, 0) [(8%positive, 511)])
    (App (bvtrunc 8%positive) [App (bvsext 8%positive) [Var 0]]) = Some (8%positive, 255) /\
  eval eval_op (env_of (1%positive, 0) [(8%positive, 250); (8%positive, 20)])
    (App (bvtrunc 4%positive) [App bvadd [Var 0; Var 1]]) = Some (4%positive, 14).
Proof.
  vm_compute. repeat split.
Qed.

(** Unequal operand widths discriminate high and low concatenation parts. *)
Example concat_parts :
  eval eval_op (env_of (1%positive, 0) [(3%positive, 5); (5%positive, 19)])
    (App (bvextract 7 5) [App bvconcat [Var 0; Var 1]]) = Some (3%positive, 5) /\
  eval eval_op (env_of (1%positive, 0) [(3%positive, 5); (5%positive, 19)])
    (App (bvtrunc 5%positive) [App bvconcat [Var 0; Var 1]]) = Some (5%positive, 19) /\
  eval eval_op (env_of (1%positive, 0) [])
    (App (bvextract 2 3) [Const 8%positive 1]) = None.
Proof.
  vm_compute. repeat split.
Qed.

Definition identity_client (_ : unit) (xs : list Z) : option Z :=
  match xs with
  | [x] => Some x
  | _ => None
  end.

Definition bool_target (o : bool) (xs : list word) : option word :=
  match o, xs with
  | true, [x] => Some x
  | _, _ => None
  end.

Definition client_word z : word := (8%positive, wrap 8%positive z).

(** The general bridge theorem supports a target vocabulary distinct from Bits operators. *)
Example second_language_bridge :
  bridge_expr identity_client client_word bool_target (fun _ => App true (vars 1)).
Proof.
  apply (bridge_op_expr identity_client client_word bool_target (fun _ => 1%nat)
    (fun _ => true)).
  - intros o xs r Hresult. destruct o; destruct xs as [|x [|y rest]];
      cbn in Hresult; discriminate || reflexivity.
  - intro z. apply wrap_is_word.
  - intros o xs r Hresult. destruct xs as [|x [|y rest]];
      cbn in Hresult; try discriminate.
    inversion Hresult; subst. reflexivity.
Qed.

(** The second language bridge accepts one raw value and rejects malformed arities. *)
Example second_language_boundaries :
  identity_client tt [-1] = Some (-1) /\
  eval bool_target (env_of (1%positive, 0) [client_word (-1)])
    (App true (vars 1)) = Some (8%positive, 255) /\
  identity_client tt [] = None /\ bool_target false [client_word 0] = None.
Proof.
  vm_compute. repeat split.
Qed.
