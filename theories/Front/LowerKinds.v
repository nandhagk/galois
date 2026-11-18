(** * Kinds and head variables of well-sorted specifications

    A well-sorted relational specification passes the kind check, because it has no
    constructor and no lattice table. Every variable of the head of a clause of a well-sorted
    specification is bound by a table premise or by the left side of its rewrite, or is
    computed by an equation premise, because the sort checker reads every variable of the
    actions of a rule.
    For example, the head [Derive path [PVar 1; PVar 3]] of [path_step] reads variables that
    its two table premises bind.

    Builds on: the lowering signature and the sort checker. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerKinds <: LOWER_KINDS_PLAN.
  Lemma relational_kinds_ok : forall {V} (s : spec V),
    check_program (spec_program s) = true -> relational_fragment (spec_program s) = true ->
    kinds_ok s = true.
  Proof.
  Admitted. (* STUB *)

  Lemma head_vars_bound : forall {V} (s : spec V) c x,
    check_program (spec_program s) = true -> In c (clauses s) ->
    In x (match head c with
          | Derive _ args => flat_map pat_vars args
          | Assign _ args v => flat_map pat_vars args ++ pat_vars v
          | Unify l r | Rewrites l r => pat_vars l ++ pat_vars r
          end) ->
    In x (body_bound (body c)) \/
    In x (match head c with Rewrites l _ => pat_bound l | _ => [] end) \/
    exists q args, In (Computes q args (PVar x)) (body c).
  Proof.
  Admitted. (* STUB *)
End LowerKinds.
