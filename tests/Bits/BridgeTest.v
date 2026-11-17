(** * Bridge and width-changing expression examples

    Consecutive variables preserve operand order and extensions preserve low bits.
    For example, subtraction through variables zero and one retains their order.
    Builds on: Word, Op, Expr and Bridge.

    Groups:
    - [ApplicationTests] Applying an operator to the consecutive variables of its arity.
    - [ExtensionTests] Zero and sign extension of words.
    - [TruncationTests] Truncation after extension and after an overflowing sum.
    - [ConcatTests] The high and low parts of a concatenation, and reversed extraction bounds.
    - [SecondLanguageTests] A bridge into a second operator language with its own values. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Word Op Expr Bridge.
Import List.ListNotations Expr.

Open Scope Z_scope.

(** * Application *)

Module ApplicationTests.

  (** Addition applied to the consecutive variables gives the sum of the first two values. *)
  Example bridge_add_of_consecutive_variables :
    eval eval_op (env_of (1%positive, 0) [(8%positive, 200); (8%positive, 100)])
      (App bvadd (vars (arity bvadd))) = Some (8%positive, 44).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Subtraction applied to the consecutive variables keeps the order of its operands. *)
  Example bridge_sub_of_consecutive_variables :
    eval eval_op (env_of (1%positive, 0) [(8%positive, 3); (8%positive, 7)])
      (App bvsub (vars (arity bvsub))) = Some (8%positive, 252).
  Proof.
    vm_compute. reflexivity.
  Qed.

End ApplicationTests.

(** * Extension *)

Module ExtensionTests.

  (** Zero extension of 255 gives the sixteen-bit value 255. *)
  Example zero_extension_of_255 :
    eval eval_op (env_of (1%positive, 0) [(8%positive, 255)])
      (App (bvzext 8%positive) [Var 0]) = Some (16%positive, 255).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Sign extension of 255 gives the sixteen-bit all-ones value. *)
  Example sign_extension_of_255 :
    eval eval_op (env_of (1%positive, 0) [(8%positive, 255)])
      (App (bvsext 8%positive) [Var 0]) = Some (16%positive, 65535).
  Proof.
    vm_compute. reflexivity.
  Qed.

End ExtensionTests.

(** * Truncation *)

Module TruncationTests.

  (** Truncating a sign-extended 511 gives back the eight-bit value 255. *)
  Example truncation_recovers_extended_word :
    eval eval_op (env_of (1%positive, 0) [(8%positive, 511)])
      (App (bvtrunc 8%positive) [App (bvsext 8%positive) [Var 0]]) = Some (8%positive, 255).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Truncating the sum of two words keeps the low four bits of the overflowing sum. *)
  Example truncation_of_overflowing_sum :
    eval eval_op (env_of (1%positive, 0) [(8%positive, 250); (8%positive, 20)])
      (App (bvtrunc 4%positive) [App bvadd [Var 0; Var 1]]) = Some (4%positive, 14).
  Proof.
    vm_compute. reflexivity.
  Qed.

End TruncationTests.

(** * Concatenation *)

Module ConcatTests.

  (** Extracting bits five to seven of a concatenation gives the high part. *)
  Example high_part_of_concat :
    eval eval_op (env_of (1%positive, 0) [(3%positive, 5); (5%positive, 19)])
      (App (bvextract 7 5) [App bvconcat [Var 0; Var 1]]) = Some (3%positive, 5).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Truncating a concatenation to five bits gives the low part. *)
  Example low_part_of_concat :
    eval eval_op (env_of (1%positive, 0) [(3%positive, 5); (5%positive, 19)])
      (App (bvtrunc 5%positive) [App bvconcat [Var 0; Var 1]]) = Some (5%positive, 19).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Extraction with reversed bounds gives no value. *)
  Example extract_with_reversed_bounds_is_none :
    eval eval_op (env_of (1%positive, 0) [])
      (App (bvextract 2 3) [Const 8%positive 1]) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ConcatTests.

(** * Second language *)

Module SecondLanguageTests.

  (** A client-language function over raw integers. *)
  Definition identity_client (_ : unit) (xs : list Z) : option Z :=
    match xs with
    | [x] => Some x
    | _ => None
    end.

  (** A boolean target that reads one word and rejects other arities. *)
  Definition bool_target (o : bool) (xs : list word) : option word :=
    match o, xs with
    | true, [x] => Some x
    | _, _ => None
    end.

  (** A word of width eight that wraps the integer z. *)
  Definition client_word z : word := (8%positive, wrap 8%positive z).

  (** The general bridge theorem supports a target vocabulary distinct from Bits operators. *)
  Example bridge_accepts_second_language :
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

  (** The client function returns its one raw value. *)
  Example identity_client_accepts_one_value : identity_client tt [-1] = Some (-1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The target reads the wrapped value of its one word. *)
  Example second_language_reads_wrapped_value :
    eval bool_target (env_of (1%positive, 0) [client_word (-1)])
      (App true (vars 1)) = Some (8%positive, 255).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The client function rejects an empty argument list. *)
  Example identity_client_rejects_empty_input : identity_client tt [] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The target rejects a word list of the wrong arity. *)
  Example bool_target_rejects_wrong_arity : bool_target false [client_word 0] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SecondLanguageTests.
