(** * An exact model of a ground specification

    The instances of a ground specification over listed rows are finitely many equations
    between applications, and congruence is their closure. The model of that closure is then
    a model of the specification whose equality is exactly congruence. The theorem instantiates
    its own plan [CongruenceRefPlan], and it shares on purpose the plans of the instances
    ([CongruenceInstances.v]) and of the reference closure ([ClosureClasses.v],
    [ClosureForms.v] and [CongruenceClosure.v]), which separate files prove.
    For example, each class of Steensgaard's closure is one element of the carrier.

    Builds on: the signature of the exact model, the reference closure and the files of the
    plans. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import Spec LowerSig RunnerSig ClosureSig CongruenceRefSig
  CongruenceInstances ClosureClasses ClosureForms CongruenceClosure.

Import List.ListNotations.

Module CongruenceRefPlan (V : VALUE) <: CONGRUENCE_REF_PLAN V.
  Lemma congruent_closure : forall (s : spec V.t) I eqs,
    ground s = true -> (forall t u, instance V.prim s I t u <-> In (t, u) eqs) ->
    forall t u, congruent V.prim s I t u <-> closure eqs t u.
  Proof.
  Admitted. (* STUB *)
End CongruenceRefPlan.

Module CongruenceRef (V : VALUE) <: CONGRUENCE_REF V.
  Module P := CongruenceRefPlan V.
  Module Instances := CongruenceInstances V.
  Module Classes := ClosureClasses V.
  Module Forms := ClosureForms V Classes.
  Module Closure := ClosureModel V Classes Forms.

  Lemma exact_model : forall (s : spec V.t) rows,
    ground s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      forall t u, denote M t = denote M u <-> congruent V.prim s (rows_in rows) t u.
  Proof.
  Admitted. (* STUB *)
End CongruenceRef.
