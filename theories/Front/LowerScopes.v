(** * Scoped rules

    The rule of each clause of a well-sorted specification that passes the kind check reads
    only variables that its query or an earlier action binds, and binds each of its own
    variables once, outside the query. A well-sorted relational specification passes the kind
    check, because it has no constructor and no lattice table.
    For example, the rule of a clause with the premise [f x = y], where no table atom binds
    [y], computes [y] with one [Let] that no query atom reads.

    Builds on: the lowering signature and the sort checker. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerScopes <: LOWER_PLAN.
  Lemma relational_kinds_ok : forall {V} (s : spec V),
    check_program (spec_program s) = true -> relational_fragment (spec_program s) = true ->
    kinds_ok s = true.
  Proof.
  Admitted. (* STUB *)

  Lemma clause_rule_scoped : forall {V} (s : spec V) c,
    check_program (spec_program s) = true -> kinds_ok s = true -> In c (clauses s) ->
    rule_scoped (clause_rule c) = true.
  Proof.
  Admitted. (* STUB *)
End LowerScopes.
