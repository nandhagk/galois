(** * Generic word expressions

    Expressions share variables, constants and argument evaluation across operator languages.
    For example, a client may supply a unit operator whose evaluator always rejects.
    Builds on: Word and Op. *)

From Stdlib Require Import ZArith List.
From Argent Require Import Time.
From Galois.Bits Require Import Word Op.
Import List.ListNotations.

Open Scope Z_scope.

Scheme All for list.

Module Expr.

(** The operator carrier is a parameter of the expression syntax. *)
Inductive t (O : Type) : Type :=
  | Var (i : nat)
  | Const (w : width) (z : Z)
  | App (o : O) (args : list (t O)).

Arguments Var {O} i.
Arguments Const {O} w z.
Arguments App {O} o args.

Section Eval.

Context {O : Type} (ev : O -> list word -> option word).

(** Evaluation normalizes variables and constants and propagates failed applications. *)
Fixpoint eval (env : nat -> word) (e : t O) : option word :=
  match e with
  | Var i => Some (normalize_word (env i))
  | Const w z => Some (w, wrap w z)
  | App o args =>
    match (fix go (es : list (t O)) : option (list word) :=
      match es with
      | [] => Some []
      | e :: rest =>
        match eval env e, go rest with
        | Some x, Some xs => Some (x :: xs)
        | _, _ => None
        end
      end) args with
    | Some xs => ev o xs
    | None => None
    end
  end.

(** Argument evaluation preserves order and propagates failure from any argument. *)
Definition eval_args (env : nat -> word) (es : list (t O)) : option (list word) :=
  (fix go (es : list (t O)) : option (list word) :=
    match es with
    | [] => Some []
    | e :: rest =>
      match eval env e, go rest with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
    end) es.

End Eval.

(** A list environment uses the caller's default for missing variables. *)
Definition env_of (d : word) (xs : list word) : nat -> word := fun i => nth i xs d.

(** Consecutive variables preserve the order of an operator's arguments. *)
Definition vars {O} (n : nat) : list (t O) := map Var (seq 0 n).

End Expr.
Import Expr.

(** The legacy word-operator expression language is the generic instance at [op]. *)
Abbreviation expr := (Expr.t op).

(** Variables evaluate to their normalized environment entry. *)
Theorem eval_var : forall {O} (ev : O -> list word -> option word) env i,
  eval ev env (Var i) = Some (normalize_word (env i)).
Proof.
  reflexivity.
Qed.

(** Constants evaluate to their normalized literal. *)
Theorem eval_const : forall {O} (ev : O -> list word -> option word) env w z,
  eval ev env (Const w z) = Some (w, wrap w z).
Proof.
  reflexivity.
Qed.

(** Applications evaluate their arguments before dispatching the supplied evaluator. *)
Theorem eval_app : forall {O} (ev : O -> list word -> option word) o env args,
  eval ev env (App o args) =
    match eval_args ev env args with Some xs => ev o xs | None => None end.
Proof.
  reflexivity.
Qed.

(** The empty argument list evaluates successfully. *)
Theorem eval_args_nil : forall {O} (ev : O -> list word -> option word) env,
  eval_args ev env nil = Some nil.
Proof.
  reflexivity.
Qed.

(** Argument-list evaluation follows the head and the remaining arguments. *)
Theorem eval_args_cons : forall {O} (ev : O -> list word -> option word) env e args,
  eval_args ev env (e :: args) =
    match eval ev env e, eval_args ev env args with
    | Some x, Some xs => Some (x :: xs)
    | _, _ => None
    end.
Proof.
  reflexivity.
Qed.

(** A word-valued operator evaluator makes every successful expression result a word. *)
Theorem eval_is_word : forall {O} (ev : O -> list word -> option word),
  (forall o xs r, ev o xs = Some r -> is_word (fst r) (snd r)) ->
  forall r env e, eval ev env e = Some r -> is_word (fst r) (snd r).
Proof.
  intros O ev Hwords r env [i|w z|o args] Hresult.
  - rewrite eval_var in Hresult. inversion Hresult. apply wrap_is_word.
  - rewrite eval_const in Hresult. inversion Hresult. apply wrap_is_word.
  - rewrite eval_app in Hresult. destruct (eval_args ev env args); [|discriminate].
    now apply (Hwords o l r).
Qed.
