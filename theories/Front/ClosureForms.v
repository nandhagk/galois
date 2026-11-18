(** * Normal forms of the reference closure

    The normal form of a term of the universe is its representative, and the normal form of an
    application depends only on the normal forms of its arguments. Every expression is equal in
    the closure to its normal form, so two expressions with one normal form are equal in the
    closure.
    For example, with the equation [f(a) = b], the normal form of [g(f(a))] is [g] over the
    representative of the class of [f(a)] and [b].

    Builds on: the reference closure signature, through the classes of its plan. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import ClosureSig.

Import List.ListNotations.

Module ClosureForms (V : VALUE) (C : CLOSURE_CLASSES V) <: CLOSURE_FORMS V.
  Lemma nf_universe : forall eqs t, In t (universe V.eqb eqs) ->
    nf V.eqb eqs t = rep_of V.eqb eqs t.
  Proof.
  Admitted. (* STUB *)

  Lemma nf_app : forall eqs f ts,
    nf V.eqb eqs (EApp f ts) = nf V.eqb eqs (EApp f (map (nf V.eqb eqs) ts)).
  Proof.
  Admitted. (* STUB *)

  Lemma nf_lit : forall eqs v, ~ In (ELit v) (universe V.eqb eqs) ->
    nf V.eqb eqs (ELit v) = ELit v.
  Proof.
  Admitted. (* STUB *)

  Lemma nf_sound : forall eqs t u, nf V.eqb eqs t = nf V.eqb eqs u -> closure eqs t u.
  Proof.
  Admitted. (* STUB *)
End ClosureForms.
