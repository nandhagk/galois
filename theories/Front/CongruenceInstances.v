(** * Instances of a ground specification

    A ground specification over listed input rows has finitely many instances, and each is an
    equation between applications. Each variable of a ground clause is bound by a relation
    premise, so an instance is fixed by the choice of one input row for each premise, and the
    primitive premises check the choice. The sides of a ground clause are constructor
    patterns, so their terms are applications.
    For example, Steensgaard's instances are one equation for each constraint and initial
    pointer.

    Builds on: the signature of the exact model. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import Spec LowerSig RunnerSig ClosureSig CongruenceRefSig.

Import List.ListNotations.

Module CongruenceInstances (V : VALUE) <: CONGRUENCE_INSTANCES V.
  Lemma instances_listed : forall (s : spec V.t) rows,
    ground s = true ->
    exists eqs, forall t u, instance V.prim s (rows_in rows) t u <-> In (t, u) eqs.
  Proof.
  Admitted. (* STUB *)

  Lemma instances_apps : forall (s : spec V.t) I t u,
    ground s = true -> instance V.prim s I t u ->
    (exists f ts, t = EApp f ts) /\ (exists g us, u = EApp g us).
  Proof.
  Admitted. (* STUB *)
End CongruenceInstances.
