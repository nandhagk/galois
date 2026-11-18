(** * Right sides of rewrites

    The rule of a rewrite ends with a union of its two sides, and the sort check accepts a
    union only of two classes. So the right side of a rewrite of a well-sorted specification
    is a constructor pattern, or a variable of a class. The input rows hold only values, so a
    body that holds in them binds no variable of a class, and such a variable sits at a class
    position of the left side. A left side that a class represents in a sorted view then makes
    the instance of the right side an application.
    For example, the instances of the commutativity rewrite [Add a b => Add b a] have the
    application [Add b a] on the right.

    Builds on: the rewrite signature, the specifications, their lowering and the sort
    checker. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig RunnerSig RewriteSig.

Import List.ListNotations.

Module RewriteSorts (V : VALUE) <: REWRITE_SORTS_PLAN V.
  Lemma rewrite_right_app : forall (s : spec V.t) rows (w : @view V.t) c e l r tl tr i,
    spec_ok s = true -> rows_ok s rows = true ->
    view_sorted (program_sorts (spec_program s)) w ->
    In c (clauses s) -> head c = Rewrites l r ->
    Forall (input_premise V.prim (rows_in rows) e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    represents w (Id i) tl -> exists f us, tr = EApp f us.
  Proof.
  Admitted. (* STUB *)
End RewriteSorts.
