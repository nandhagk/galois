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

(** Imperative exits pass no block arguments. *)
Definition imp_exit {X G} (e : exit X G) : Prop :=
  match e with
  | Jump _ args => args = nil
  | Branch _ _ _ a1 _ a2 => a1 = nil /\ a2 = nil
  | Return _ => True
  end.

(** An imperative function has no block parameters or edge arguments. *)
Definition imp_form {K G} (p : func positive K G) : Prop :=
  Forall (fun item => params _ _ _ (snd item) = nil /\ imp_exit (term _ _ _ (snd item)))
    (blocks _ _ _ p).

Module Type OPS.
  Parameter K G C : Type.
  Parameter eval : K -> list C -> option C.
  Parameter test : G -> list C -> option bool.
  Parameter mov : K.
  (** The move operator returns its sole operand. *)
  Parameter eval_mov : forall c, eval mov (c :: nil) = Some c.
End OPS.
