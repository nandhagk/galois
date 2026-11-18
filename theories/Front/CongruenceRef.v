(** * An exact model of a ground specification

    The model is built from the congruence closure of the ground instances, computed on the
    finite set of their subterms, with canonical forms as its carrier and a free extension for
    every other term.
    For example, each class of Steensgaard's closure is one element of the carrier.

    Builds on: the signature of the reference closure, the specifications and the models. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import Spec RunnerSig CongruenceRefSig.

Import List.ListNotations.

Module CongruenceRef (V : VALUE) <: CONGRUENCE_REF V.
  Lemma exact_model : forall (s : spec V.t) rows,
    ground s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      forall t u, denote M t = denote M u <-> congruent V.prim s (rows_in rows) t u.
  Proof.
  Admitted. (* STUB *)
End CongruenceRef.
