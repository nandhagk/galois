(** * An exact model of a ground specification

    A ground specification has clauses that read only input rows and primitives, bind each of
    their variables in an input row, and unify two constructor terms. Its instances over the
    input rows are then finitely many equations between applications. Their congruence closure,
    computed on the finite set of their subterms and extended freely to all other terms, is a
    model in which two terms are equal exactly when they are congruent. It exists without any
    quotient, because the closure has normal forms ([ClosureSig.v]). The proof of ground
    soundness uses it to read class equalities of the engine as congruences.
    For example, Steensgaard's model equates [Deref (Cell x)] and [Cell a] exactly when an
    address constraint or a chain of them makes them congruent.

    Main results
    - [exact_model] A ground specification has a model of its input rows whose equality on
      terms is exactly congruence.
    - [instances_listed], [instances_apps] The instances of a ground specification are
      finitely many equations between applications.
    - [congruent_closure] Congruence of a ground specification is the closure of its
      instances.

    Builds on: the specifications, their lowering, the runner conditions, the reference closure
    and the engine models. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import Spec LowerSig RunnerSig ClosureSig.

Import List.ListNotations.

(** * Ground specifications *)

(** A premise reads an input table of the specification or computes a value. *)
Definition input_premise_b {V} (s : spec V) (p : premise V) : bool :=
  match p with
  | Holds r _ => existsb (Pos.eqb r) (inputs s)
  | Computes _ _ _ => true
  | Equals _ _ _ => false
  end.

(** A ground specification. Every clause reads only input rows and primitives, binds each of
    its variables by a relation premise outside primitive calls, and unifies two constructor
    terms. The instances are then finitely many equations between applications. *)
Definition ground {V} (s : spec V) : bool :=
  forallb (fun c =>
    match head c with
    | Unify (PNode _ _ as l) (PNode _ _ as r) =>
        forallb (input_premise_b s) (body c) &&
        forallb (fun x => existsb (Pos.eqb x) (body_bound (body c)))
          (flat_map premise_vars (body c) ++ pat_vars l ++ pat_vars r)
    | _ => false
    end) (clauses s).

(** An instance of a specification: the two built sides of a union clause whose body holds in
    the input rows [I]. *)
Definition instance {V} (prim : positive -> list V -> option V) (s : spec V)
    (I : positive -> list V -> Prop) (t u : @expr V) : Prop :=
  exists c e l r, In c (clauses s) /\ head c = Unify l r /\
    Forall (input_premise prim I e) (body c) /\ pat_term prim e l = Some t /\
    pat_term prim e r = Some u.

(** * Laws *)

Module Type CONGRUENCE_REF (V : VALUE).
  (** A ground specification has a model of its input rows whose equality on terms is exactly
      congruence. *)
  Parameter exact_model : forall (s : spec V.t) rows,
    ground s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      forall t u, denote M t = denote M u <-> congruent V.prim s (rows_in rows) t u.
End CONGRUENCE_REF.

(** * Proof plan *)

(** The instances of a ground specification. *)
Module Type CONGRUENCE_INSTANCES (V : VALUE).
  (** A ground specification over listed input rows has finitely many instances. *)
  Parameter instances_listed : forall (s : spec V.t) rows,
    ground s = true ->
    exists eqs, forall t u, instance V.prim s (rows_in rows) t u <-> In (t, u) eqs.
  (** Every instance of a ground specification is an equation between applications. *)
  Parameter instances_apps : forall (s : spec V.t) I t u,
    ground s = true -> instance V.prim s I t u ->
    (exists f ts, t = EApp f ts) /\ (exists g us, u = EApp g us).
End CONGRUENCE_INSTANCES.

(** The congruence of a ground specification. *)
Module Type CONGRUENCE_REF_PLAN (V : VALUE).
  (** Congruence of a ground specification is the closure of a list of its instances. *)
  Parameter congruent_closure : forall (s : spec V.t) I eqs,
    ground s = true -> (forall t u, instance V.prim s I t u <-> In (t, u) eqs) ->
    forall t u, congruent V.prim s I t u <-> closure eqs t u.
End CONGRUENCE_REF_PLAN.
