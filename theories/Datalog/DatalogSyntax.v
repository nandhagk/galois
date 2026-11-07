(** * Datalog syntax and range restriction

    Rules relate predicates over encoded constants and carry explicit literal polarity.
    For example, a positive body atom can copy a tuple into the rule head.
    Builds on: BaseEncoding and Stdlib lists. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding.
Import List.ListNotations.

(** * Syntax *)

Definition tuple : Type := list positive.

Inductive term : Type :=
  | TVar (v : nat)
  | TConst (c : positive).

Record atom (P : Type) : Type := Atom {
  pred : P;
  args : list term
}.

Arguments Atom {P}.
Arguments pred {P}.
Arguments args {P}.

Inductive literal (P : Type) : Type :=
  | LPos (a : atom P)
  | LNeg (a : atom P).

Arguments LPos {P}.
Arguments LNeg {P}.

Record rule (P : Type) : Type := Rule {
  head : atom P;
  body : list (literal P)
}.

Arguments Rule {P}.
Arguments head {P}.
Arguments body {P}.

Record program (P : Type) : Type := Program {
  penc : encoding P;
  arity : P -> nat;
  rules : list (rule P)
}.

Arguments Program {P}.
Arguments penc {P}.
Arguments arity {P}.
Arguments rules {P}.

Definition ground_atom (P : Type) : Type := (P * tuple)%type.

Definition inst (sigma : nat -> positive) (t : term) : positive :=
  match t with
  | TVar v => sigma v
  | TConst c => c
  end.

Definition ground {P} (sigma : nat -> positive) (a : atom P) : ground_atom P :=
  (pred a, map (inst sigma) (args a)).

Definition lit_atom {P} (l : literal P) : atom P :=
  match l with
  | LPos a => a
  | LNeg a => a
  end.

Definition atom_vars {P} (a : atom P) : list nat :=
  flat_map (fun t => match t with TVar v => [v] | TConst _ => [] end) (args a).

(** * Well-formed programs *)

(** Every head or negative variable occurs in a positive body atom. *)
Definition safe_rule {P} (r : rule P) : Prop :=
  forall v, (In v (atom_vars (head r)) \/
    exists a, In (LNeg a) (body r) /\ In v (atom_vars a)) ->
  exists a, In (LPos a) (body r) /\ In v (atom_vars a).

(** Every rule is safe and every rule atom and fact has its predicate's arity. *)
Definition program_wf {P} (prog : program P) (facts : list (ground_atom P)) : Prop :=
  (forall r, In r (rules prog) -> safe_rule r /\
    length (args (head r)) = arity prog (pred (head r)) /\
    forall l, In l (body r) -> length (args (lit_atom l)) = arity prog (pred (lit_atom l))) /\
  forall f, In f facts -> length (snd f) = arity prog (fst f).
