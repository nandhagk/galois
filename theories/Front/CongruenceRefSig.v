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

(** A premise reads an input table of the specification or computes a value. *)
Definition input_premise_b {V} (s : spec V) (p : premise V) : bool :=
  match p with
  | Holds r _ => existsb (Pos.eqb r) (inputs s)
  | Computes _ _ _ => true
  | Equals _ _ _ => false
  end.

(** A ground specification: every clause reads only input rows and primitives, and unifies two
    built terms. *)
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

(** * Proof plan *)

(** An instance of a specification: the two built sides of a union clause whose body holds in
    the input rows [I]. *)
Definition instance {V} (prim : positive -> list V -> option V) (s : spec V)
    (I : positive -> list V -> Prop) (t u : @expr V) : Prop :=
  exists c e l r, In c (clauses s) /\ head c = Unify l r /\
    Forall (input_premise prim I e) (body c) /\ pat_term prim e l = Some t /\
    pat_term prim e r = Some u.

(** The least congruence that contains listed equations. *)
Inductive closure {V} (eqs : list (@expr V * @expr V)) : @expr V -> @expr V -> Prop :=
  | closure_eq t u : In (t, u) eqs -> closure eqs t u
  | closure_refl t : closure eqs t t
  | closure_sym t u : closure eqs t u -> closure eqs u t
  | closure_trans t u w : closure eqs t u -> closure eqs u w -> closure eqs t w
  | closure_cong f ts us : Forall2 (closure eqs) ts us -> closure eqs (EApp f ts) (EApp f us).

Module Type CONGRUENCE_REF_PLAN (V : VALUE).
  (** A ground specification over listed input rows has finitely many instances. *)
  Parameter instances_listed : forall (s : spec V.t) rows,
    ground s = true ->
    exists eqs, forall t u, instance V.prim s (rows_in rows) t u <-> In (t, u) eqs.
  (** Congruence of a ground specification is the closure of a list of its instances. *)
  Parameter congruent_closure : forall (s : spec V.t) I eqs,
    ground s = true -> (forall t u, instance V.prim s I t u <-> In (t, u) eqs) ->
    forall t u, congruent V.prim s I t u <-> closure eqs t u.
  (** The closure of finitely many equations is the equality of a model, whose relations hold
      exactly of the rows of a given relation on values. *)
  Parameter closure_model : forall (eqs : list (@expr V.t * @expr V.t))
      (P : positive -> list V.t -> Prop),
    exists M : @model V.t, (forall t u, denote M t = denote M u <-> closure eqs t u) /\
      (forall r vs, rel M r (map inr vs) <-> P r vs).
End CONGRUENCE_REF_PLAN.
