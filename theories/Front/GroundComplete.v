(** * Completeness of saturated ground runs

    A saturated outcome of a ground specification represents both sides of every instance,
    because it builds them in one class ([GroundBuild.v]). Two represented congruent terms
    share a class, because the model of the classes satisfies the specification, congruent
    terms have one meaning in it, and its valuation separates distinct classes. The theorems
    take on purpose the plans of the other files, which [Ground.v] instantiates.
    For example, a saturated run of Steensgaard's program puts [Deref (Cell x)] and [Cell a] in
    one class when they are congruent and represented.

    Builds on: the ground signature, the runner facts and the plans of the ground theorems. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig CongruenceRefSig GroundSig.

Import List.ListNotations.

Module GroundComplete (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PD : GROUND_DENOTE_PLAN V) (PC : GROUND_CLASS_PLAN V I J D R X)
    (PS : GROUND_SATISFIES_PLAN V I J D R X) (PB : GROUND_BUILD_PLAN V I J D R X)
    <: GROUND_COMPLETE V I J D R X.
  Lemma solve_complete : forall (s : spec V.t) rows lim db i j t u,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    represents (D.view db) (Id i) t -> represents (D.view db) (Id j) u ->
    congruent V.prim s (rows_in rows) t u -> same (D.view db) i j.
  Proof.
  Admitted. (* STUB *)

  Lemma solve_builds : forall (s : spec V.t) rows lim db c e l r tl tr,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    In c (clauses s) -> head c = Unify l r ->
    Forall (input_premise V.prim (rows_in rows) e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    (exists i, represents (D.view db) (Id i) tl) /\ (exists j, represents (D.view db) (Id j) tr).
  Proof.
  Admitted. (* STUB *)
End GroundComplete.
