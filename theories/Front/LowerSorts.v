(** * Sorts of the variables of well-sorted clauses

    The sort checker types the query of the rule of a clause from the declarations of its
    tables. A query atom binds a variable at the sort of its first position, and every later
    position, primitive and action that reads the variable checks that sort. So the query of
    the rule of a clause of a well-sorted specification binds each variable at the sort at
    which the clause uses it, and a variable that the query leaves unbound is the result of an
    equation premise, which a [Let] defines as a value. The validity of the lowered rules and
    the congruence of ground runs read the sorts of their environments from this fact.
    For example, the rule of [mul_one x : Mul x (Num 1) => x] binds [x] in its query at the
    sort of a class, which is the sort at which both sides of the rewrite use [x].

    Builds on: the lowering signature, the specifications and the sort checker. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerSorts (PV : LOWER_VALUES) <: LOWER_SORTS.
  (* STUB: [check_program_spec] gives [rule_ok] of [clause_rule c]. Its context is [g], because
     [binds], [binds_list], [binds_result] and [query_ok] determine their output context. The
     query binds each variable at the sort of its first table position, and every later
     position, [Prim] atom and action checks that sort, so the sort agrees with [pat_sorts] at
     each use in the body and in the head. The arguments and the results of primitives are
     values. A variable that the query leaves unbound is defined by a [Let], which
     [query_body] makes only from a premise [Computes q args (PVar x)]. *)
  Lemma clause_sorts_query : forall {V} (s : spec V) c g x so,
    check_program (spec_program s) = true -> kinds_ok s = true -> In c (clauses s) ->
    query_ok (program_sorts (spec_program s)) (program_kind (spec_program s)) ctx_empty
      (query V (clause_rule c)) g ->
    In (x, so) (clause_sorts (tables s) c) ->
    g x = Some so \/
    (g x = None /\ so = SVal /\ exists q args, In (Computes q args (PVar x)) (body c)).
  Proof.
  Admitted. (* STUB *)
End LowerSorts.
