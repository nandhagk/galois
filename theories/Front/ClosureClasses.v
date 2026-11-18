(** * Classes of the reference closure

    The classes that [classes] computes are inside the closure of the equations, contain the
    equations, and are closed under congruence on the universe. The first two hold for every
    pass, because a pass merges only congruent classes. The last holds because the classes are a
    fixed point of a pass, which [ClosureFixpoint.v] proves.
    For example, with the equations [a = b], [f(a) = c] and [f(b) = d], a pass merges [f(a)]
    with [f(b)], and with them [c] with [d].

    Builds on: the reference closure signature and the fixed point of its classes. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import ClosureSig.

Import List.ListNotations.

Module ClosureClasses (V : VALUE) (PF : CLOSURE_FIXPOINT V) <: CLOSURE_CLASSES V.
  Lemma universe_eqs : forall eqs t u, In (t, u) eqs ->
    In t (universe V.eqb eqs) /\ In u (universe V.eqb eqs).
  Proof.
  Admitted. (* STUB *)

  Lemma universe_args : forall eqs f ts t, In (EApp f ts) (universe V.eqb eqs) -> In t ts ->
    In t (universe V.eqb eqs).
  Proof.
  Admitted. (* STUB *)

  Lemma rep_of_universe : forall eqs t, In t (universe V.eqb eqs) ->
    In (rep_of V.eqb eqs t) (universe V.eqb eqs) /\
    rep_of V.eqb eqs (rep_of V.eqb eqs t) = rep_of V.eqb eqs t.
  Proof.
  Admitted. (* STUB *)

  Lemma rep_of_sound : forall eqs t u, rep_of V.eqb eqs t = rep_of V.eqb eqs u ->
    closure eqs t u.
  Proof.
  Admitted. (* STUB *)

  Lemma rep_of_eqs : forall eqs t u, In (t, u) eqs -> rep_of V.eqb eqs t = rep_of V.eqb eqs u.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [PF.classes_closed] says that a pass merges nothing on the classes, so two
     applications of one constructor whose arguments are in one class each are in one class. *)
  Lemma rep_of_cong : forall eqs f ts us,
    In (EApp f ts) (universe V.eqb eqs) -> In (EApp f us) (universe V.eqb eqs) ->
    Forall2 (fun t u => rep_of V.eqb eqs t = rep_of V.eqb eqs u) ts us ->
    rep_of V.eqb eqs (EApp f ts) = rep_of V.eqb eqs (EApp f us).
  Proof.
  Admitted. (* STUB *)
End ClosureClasses.
