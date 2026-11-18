(** * A model of the closure of finitely many equations

    The normal forms of the reference closure give a model whose equality is exactly the
    closure, so no quotient is needed. The carrier is the expressions, and a constructor
    applied to meanings is the normal form of the application. Every equation of the closure
    keeps its normal forms, and the plan says that one normal form means one class, so two
    terms mean the same exactly when the closure equates them. The equations relate only
    applications, so a literal keeps its own normal form and means its value.
    For example, the closure of the one equation [Deref (Cell x) = Cell a] gives both sides one
    meaning, and leaves every other term its own.

    Builds on: the reference closure signature, through the classes and normal forms of its
    plan, and the engine models. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import ClosureSig.

Import List.ListNotations.

Module ClosureModel (V : VALUE) (C : CLOSURE_CLASSES V) (F : CLOSURE_FORMS V)
    <: CLOSURE_MODEL V.
  Lemma closure_model : forall (eqs : list (@expr V.t * @expr V.t))
      (P : positive -> list V.t -> Prop),
    apps_only eqs ->
    exists M : @model V.t, (forall t u, denote M t = denote M u <-> closure eqs t u) /\
      (forall r xs, rel M r xs <-> exists vs, xs = map inr vs /\ P r vs) /\
      (forall f xs v, ~ lat M f xs v).
  Proof.
  Admitted. (* STUB *)
End ClosureModel.
