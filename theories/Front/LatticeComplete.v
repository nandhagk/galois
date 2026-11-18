(** * Completeness of lattice tables

    A saturated outcome is closed under the rules, and it keeps the input rows, so it holds
    every derived row. The rule of an assigning clause then fires on the rows of its premises,
    and its put is present, so the stored value is above the assigned one. The theorem
    instantiates its own plan [LatticeAssign] as [Assign].
    For example, a saturated run of upper bounds stores a bound at least as large as each
    derived bound.

    Builds on: the lattice signature, the runner facts, the lowering laws and the run
    contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig LatticeSig.

Import List.ListNotations.

Module LatticeAssign (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (LW : LOWER_LAWS) <: LATTICE_ASSIGN_PLAN V I J D R X.
  (* STUB: induction on [assigned]. The rule of an assigning clause matches in the closed view by
     [LW.query_body_matches] and [LW.checks_last_matches], and its present actions compute the
     values of the body and the head by [LW.query_body_lets] and [LW.build_pats_present_sound],
     so its put is present. *)
  Lemma lower_assigned : forall (s : spec V.t) (w : @view V.t) f ks v,
    spec_ok s = true -> closed V.prim V.merge (spec_program s) w ->
    (forall g, kind w g = lookup_kind (tables s) g) ->
    (forall g k o, row w g k o -> lookup_kind (tables s) g = Some ORel -> o = None) ->
    assigned V.prim s (view_rows w) f ks v ->
    exists m v', lookup_kind (tables s) f = Some (OLat m) /\
      row w f (map Val ks) (Some (Val v')) /\ V.merge m v v' = v'.
  Proof.
  Admitted. (* STUB *)
End LatticeAssign.

Module LatticeComplete (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    <: LATTICE_COMPLETE V I J D R X.
  Module Assign := LatticeAssign V I J D R X LW.

  Lemma solve_complete : forall (s : spec V.t) rows lim db f m ks w,
    spec_ok s = true -> lattice_spec s = true -> rows_ok s rows = true ->
    lookup_kind (tables s) f = Some (OLat m) ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    assigned V.prim s (rows_in rows) f ks w ->
    exists v, row (D.view db) f (map Val ks) (Some (Val v)) /\ V.merge m w v = v.
  Proof.
  Admitted. (* STUB *)
End LatticeComplete.
