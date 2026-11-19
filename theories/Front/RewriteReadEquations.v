(** * The rules of equations in the model of the relations

    The rule of a clause that equates two terms has a query and actions that define values,
    build terms and end with a union. The model [unit_model] of [RewriteReadSig.v] has one
    class, so every union holds in it, and a well-sorted environment gives every argument of an
    action a meaning of its sort. This file proves that the model validates such a rule on
    well-sorted environments, which the soundness of [RewriteReadSound.v] needs beside the
    clauses of the relations.

    For example, the rule of the rewrite [Mul (Var x) a => Scale c a] builds [Scale c a] and
    joins it with the matched class, and both are the one class of the model.

    Builds on: the signature of rewrites that read rows, the specifications, their lowering and
    the sort checker. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig RunnerSig RewriteReadSig.

Import List.ListNotations.

Module RewriteReadEquations (V : VALUE) <: REWRITE_READ_EQUATION_PLAN V.
  (* STUB: the head of the clause is [Unify] or [Rewrites], so the actions of [clause_rule c]
     are the definitions of its body, the actions of [build_pat] and one [Union], with no
     [Put]. [check_program_spec] makes the rule well sorted, and the context of its query is
     the context of [rule_ok], because [query_ok] computes it. Every argument of a [Let] or a
     [Make] then has a meaning of its sort in the environment, [Make] names an identifier
     table, and the two sides of the [Union] are [inl tt] in the model, which are equal. *)
  Lemma equation_rule_valid : forall (s : spec V.t) (I : positive -> list V.t -> Prop) c,
    spec_ok s = true -> In c (clauses s) -> value_clause c = false ->
    rule_valid_sorted V.prim (unit_model V.prim V.merge s I) (program_sorts (spec_program s))
      (program_kind (spec_program s)) (clause_rule c).
  Proof.
  Admitted. (* STUB *)
End RewriteReadEquations.
