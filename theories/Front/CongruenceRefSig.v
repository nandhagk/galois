(** * An exact model of a ground specification

    The instances of a ground specification over its input rows are finitely many equations
    between terms. Their congruence closure over the finite set of their subterms, extended
    freely to all other terms, is a model in which two terms are equal exactly when they are
    congruent. It exists without any quotient, because the closure has canonical forms. The
    proof of ground soundness uses it to read class equalities of the engine as congruences.
    For example, Steensgaard's model equates [Deref (Cell x)] and [Cell a] exactly when an
    address constraint or a chain of them makes them congruent.

    Builds on: the specifications and the engine models. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import Spec RunnerSig.

Import List.ListNotations.

(** A premise reads an input table of the specification. *)
Definition input_premise_b {V} (s : spec V) (p : premise V) : bool :=
  match p with
  | Holds r _ => existsb (Pos.eqb r) (inputs s)
  | _ => false
  end.

(** A ground specification: every clause reads only input rows and unifies two built terms. *)
Definition ground {V} (s : spec V) : bool :=
  forallb (fun c =>
    match head c with
    | Unify _ _ => forallb (input_premise_b s) (body c)
    | _ => false
    end) (clauses s).

Module Type CONGRUENCE_REF (V : VALUE).
  (** A ground specification has a model of its input rows whose equality on terms is
      exactly congruence. *)
  Parameter exact_model : forall (s : spec V.t) rows,
    ground s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      forall t u, denote M t = denote M u <-> congruent V.prim s (rows_in rows) t u.
End CONGRUENCE_REF.
