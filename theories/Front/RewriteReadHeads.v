(** * Sides of the equations of well-sorted specifications

    The rule of an equation ends with a union of its two sides, and the sort check accepts a
    union only of two classes. The lowering turns a value pattern into a literal and a primitive
    pattern into a variable of a value, so neither is a class. So both sides of an equation of a
    well-sorted specification are variables or constructor patterns, which the model of the
    relations reads as its one class.
    For example, the rewrite [Mul a (Num 1) => a] has a constructor pattern on the left and a
    variable on the right, and the sort check rejects a rewrite whose right side is the literal
    [1].

    Builds on: the signature of rewrites that read rows, the specifications, their lowering and
    the sort checker. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig RunnerSig RewriteReadSig.

Import List.ListNotations.

Module RewriteReadHeads <: REWRITE_READ_HEADS_PLAN.
  (* STUB: [check_program_spec] makes the rule of the clause well sorted, and its last action
     [Union tl tr] needs both terms at the sort [SId] in the context after the earlier actions.
     [build_pat] and [query_pat] give a value pattern the literal [Lit v], whose only sort is
     [SVal]. They give a primitive pattern a fresh variable, which a [Let] binds at [SVal] and
     no later action binds again, or which a [Prim] atom of the query reads before any atom
     binds it. *)
  Lemma equation_sides_class : forall {V} (s : spec V) c l r,
    spec_ok s = true -> In c (clauses s) -> (head c = Unify l r \/ head c = Rewrites l r) ->
    pat_class l = true /\ pat_class r = true.
  Proof.
  Admitted. (* STUB *)
End RewriteReadHeads.
