(** * An exact model of a ground specification

    The instances of a ground specification over listed rows are finitely many, and congruence
    is their closure. The model of that closure ([CongruenceClosure.v]) is then a model of the
    specification whose equality is exactly congruence.
    For example, each class of Steensgaard's closure is one element of the carrier.

    Builds on: the signature of the reference closure, the closure model and the
    specifications. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import Spec RunnerSig CongruenceRefSig CongruenceClosure.

Import List.ListNotations.

Module CongruenceInstances (V : VALUE).
  Lemma instances_listed : forall (s : spec V.t) rows,
    ground s = true ->
    exists eqs, forall t u, instance V.prim s (rows_in rows) t u <-> In (t, u) eqs.
  Proof.
  Admitted. (* STUB *)

  Lemma congruent_closure : forall (s : spec V.t) I eqs,
    ground s = true -> (forall t u, instance V.prim s I t u <-> In (t, u) eqs) ->
    forall t u, congruent V.prim s I t u <-> closure eqs t u.
  Proof.
  Admitted. (* STUB *)
End CongruenceInstances.

Module CongruenceRefPlan (V : VALUE) <: CONGRUENCE_REF_PLAN V.
  Include CongruenceInstances V.
  Include ClosureModel V.
End CongruenceRefPlan.

Module CongruenceRef (V : VALUE) (P : CONGRUENCE_REF_PLAN V) <: CONGRUENCE_REF V.
  Lemma exact_model : forall (s : spec V.t) rows,
    ground s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      forall t u, denote M t = denote M u <-> congruent V.prim s (rows_in rows) t u.
  Proof.
  Admitted. (* STUB *)
End CongruenceRef.
