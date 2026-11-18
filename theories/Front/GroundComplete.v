(** * Completeness of saturated ground runs

    A saturated outcome of a ground specification builds both sides of every instance in one
    class, because its rules are closed. The body of an instance holds in the input rows, which
    the outcome keeps, so the rule of the clause matches and its actions are present. Two
    represented congruent terms then share a class, because the model of the classes satisfies
    the specification, congruent terms have one meaning in it, and its valuation separates
    distinct classes. The theorem instantiates its own plan [GroundBuild], and it takes on
    purpose the plans of the other files, which [Ground.v] instantiates.
    For example, a saturated run of Steensgaard's program puts [Deref (Cell x)] and [Cell a] in
    one class when they are congruent and represented.

    Builds on: the ground signature, the runner facts, the lowering laws and the run
    contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig CongruenceRefSig GroundSig.

Import List.ListNotations.

Module GroundBuild (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    <: GROUND_BUILD_PLAN V I J D R X.
  Lemma instance_built : forall (s : spec V.t) rows lim db c e l r tl tr,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    In c (clauses s) -> head c = Unify l r ->
    Forall (input_premise V.prim (rows_in rows) e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    exists i j, represents (D.view db) (Id i) tl /\ represents (D.view db) (Id j) tr /\
      same (D.view db) i j.
  Proof.
  Admitted. (* STUB *)
End GroundBuild.

Module GroundComplete (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PD : GROUND_DENOTE_PLAN V) (PC : GROUND_CLASS_PLAN V I J D R X)
    (PS : GROUND_SATISFIES_PLAN V I J D R X) <: GROUND_COMPLETE V I J D R X.
  Module P := GroundBuild V I J D R X F LW.

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
