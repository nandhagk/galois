(** * Lattice tables

    Every put into a lattice table merges an assigned value into the stored one, and a
    saturated run is closed under the clauses, so each assigned value is already below it.
    For example, a run of upper bounds stores the largest derived bound.

    Builds on: the lattice signature and the run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig LatticeSig.

Import List.ListNotations.

Module Lattice (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: LATTICE V I J D R X.
  Lemma solve_sound : forall (s : spec V.t) rows lim f m ks v,
    spec_ok s = true -> lattice_spec s = true -> rows_ok s rows = true ->
    lookup_kind (tables s) f = Some (OLat m) ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) f (map Val ks) (Some (Val v)) ->
    exists w ws, assigned V.prim s (rows_in rows) f ks w /\
      Forall (assigned V.prim s (rows_in rows) f ks) ws /\ v = fold_left (V.merge m) ws w.
  Proof.
  Admitted. (* STUB *)

  Lemma solve_complete : forall (s : spec V.t) rows lim db f m ks w,
    spec_ok s = true -> lattice_spec s = true -> rows_ok s rows = true ->
    lookup_kind (tables s) f = Some (OLat m) ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    assigned V.prim s (rows_in rows) f ks w ->
    exists v, row (D.view db) f (map Val ks) (Some (Val v)) /\ V.merge m w v = v.
  Proof.
  Admitted. (* STUB *)
End Lattice.
