(** * Block language for imperative and SSA programs

    Functions contain blocks whose exits pass values to successor parameters.
    For example, a return exit returns the values of its listed variables.
    Builds on: Stdlib lists and positive identifiers. *)

From Stdlib Require Import List PArith.

Inductive exit (X G : Type) : Type :=
  | Jump (b : positive) (args : list X)
  | Branch (g : G) (xs : list X) (b1 : positive) (a1 : list X)
      (b2 : positive) (a2 : list X)
  | Return (xs : list X).

Arguments Jump {X G}.
Arguments Branch {X G}.
Arguments Return {X G}.

Record block (X K G : Type) : Type := Block {
  params : list X;
  code : list (X * K * list X);
  term : exit X G
}.

Record func (X K G : Type) : Type := Func {
  entry : positive;
  inputs : list X;
  blocks : list (positive * block X K G)
}.

Inductive result (C : Type) : Type :=
  | Returned (cs : list C)
  | Wrong
  | Timeout.

Arguments Returned {C}.
Arguments Wrong {C}.
Arguments Timeout {C}.
