(** * Languages and terms

    Terms evaluate ordered operands before applying a language operator.
    For example, a leaf reads the value of its variable in the concrete state.
    Builds on: Stdlib List and ZArith, Argent Time and Std. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Time Tactics Std.
Import List.ListNotations.

Scheme All for list.

(** A term contains variable leaves and operator nodes. *)
Inductive term (K X : Type) : Type :=
  | Leaf (x : X)
  | Node (k : K) (ts : list (term K X)).

Arguments Leaf {K X} x.
Arguments Node {K X} k ts.

(** Sequencing retains operand order and propagates failure. *)
Fixpoint sequence {C} (xs : list (option C)) : option (list C) :=
  match xs with
  | [] => Some []
  | Some c :: xs =>
    match sequence xs with
    | Some cs => Some (c :: cs)
    | None => None
    end
  | None :: _ => None
  end.

TimeFun sequence.

(** Evaluation propagates failure from any operand or operator. *)
Fixpoint eval_term {K X C} (ev : K -> list C -> option C) (st : X -> C)
    (e : term K X) : option C :=
  match e with
  | Leaf x => Some (st x)
  | Node k ts =>
    match sequence (map (eval_term ev st) ts) with
    | Some cs => ev k cs
    | None => None
    end
  end.

TimeFun eval_term.

(** Evaluating a list retains its original order. *)
Definition eval_terms {K X C} (ev : K -> list C -> option C) (st : X -> C)
    (ts : list (term K X)) : option (list C) :=
  sequence (map (eval_term ev st) ts).

TimeFun eval_terms.

(** Size counts both leaves and operator nodes. *)
Fixpoint tsize {K X} (e : term K X) : nat :=
  match e with
  | Leaf _ => 1
  | Node _ ts => S (fold_right Nat.add 0 (map tsize ts))
  end.

TimeFun tsize.

(** Updating a state changes the value selected by the supplied equality test. *)
Definition upd {X C} (eqb : X -> X -> bool) (st : X -> C) (x : X) (c : C)
    (y : X) : C :=
  if eqb y x then c else st y.

TimeFun upd.

Module Type LANG_OPS.
  Parameter op guard val : Type.
  Parameter eval : op -> list val -> option val.
  Parameter literal : op -> option Z.
End LANG_OPS.

Module Type LANG_LAWS (Import L : LANG_OPS).
  (* spec: holds *)
  Parameter holds : guard -> list val -> Prop.
End LANG_LAWS.

Module Type LANG := LANG_OPS <+ LANG_LAWS.

Module Type LANG_TIME (Import L : LANG).
  (* spec: work *)
  Parameter work : op -> list val -> nat.
  Parameter T_eval : op -> list val -> N.
  Parameter T_literal : op -> N.
  Parameter c_lang : N.
  (** Evaluation time is bounded by the language's operator work. *)
  Parameter T_eval_le : forall o vs, (T_eval o vs <= c_lang * N.of_nat (work o vs + 1))%N.
  (** Literal recognition has a uniform bound. *)
  Parameter T_literal_le : forall o, (T_literal o <= c_lang)%N.
End LANG_TIME.

Module Type LANG_T := LANG <+ LANG_TIME.
