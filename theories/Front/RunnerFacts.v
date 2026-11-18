(** * Facts of the runner

    The facts that every theorem about a run needs. The seed of a specification that passes its
    checks holds exactly its input rows, as rows of values without output, and the run
    contracts of the engine apply to it. A model of the input rows satisfies the seed, every
    outcome keeps the input rows, and a lookup says whether a database has a row. The timed
    runner is in [RunnerTime.v].
    For example, [seed_rows] says that the seed of [Path.program] on the edges 1 to 2 and 2 to 3
    holds exactly the two edge rows.

    Builds on: the runner signature and the engine contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig.

Import List.ListNotations.

Module RunnerFacts (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: RUNNER_FACTS V I J D R X.
  Lemma plan_ok : forall (s : spec V.t), spec_ok s = true ->
    R.plans_ok (spec_program s) (R.plan (spec_program s)).
  Proof.
  Admitted. (* STUB *)

  Lemma seed_rows : forall (s : spec V.t) rows r k o,
    spec_ok s = true -> rows_ok s rows = true ->
    row (D.view (X.seed (spec_program s) rows)) r k o <->
      o = None /\ exists vs, k = map Val vs /\ In (r, vs) rows.
  Proof.
  Admitted. (* STUB *)

  Lemma seed_ready : forall (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    D.wf (X.seed (spec_program s) rows) /\ D.canonical (X.seed (spec_program s) rows) /\
    R.loaded (spec_program s) (R.plan (spec_program s)) (X.seed (spec_program s) rows) /\
    R.no_ids (X.seed (spec_program s) rows).
  Proof.
  Admitted. (* STUB *)

  Lemma holds_spec : forall db r vs, D.wf db ->
    X.holds r vs db = true <-> row (D.view db) r (map Val vs) None.
  Proof.
  Admitted. (* STUB *)

  Lemma seed_sat : forall (s : spec V.t) rows (M : @model V.t) nu,
    spec_ok s = true -> rows_ok s rows = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    sat V.merge M nu (D.view (X.seed (spec_program s) rows)).
  Proof.
  Admitted. (* STUB *)

  Lemma solve_keeps : forall (s : spec V.t) rows lim r vs,
    spec_ok s = true -> rows_ok s rows = true -> In (r, vs) rows ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) r (map Val vs) None.
  Proof.
  Admitted. (* STUB *)
End RunnerFacts.
