(** * Relational exactness

    The run contracts of the engine and the lowering laws give relational exactness. A row of
    an outcome has a derivation of the lowered program from the seed, and [lower_sound] turns
    it into a derived row. A saturated outcome is closed under the rules and keeps the input
    rows, so [lower_closed] puts every derived row in it. The runner facts give the seed, and
    the theorem has no plan of its own.
    For example, a saturated run of [Path.program] holds a path exactly when [path] holds.

    Builds on: the relational signature, the runner facts, the lowering laws and the run
    contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig RelationalSig.

Import List.ListNotations.

Module Relational (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    <: RELATIONAL V I J D R X.
  Lemma solve_sound : forall (s : spec V.t) rows lim r k o,
    spec_ok s = true -> relational s = true -> rows_ok s rows = true ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) r k o ->
    o = None /\ exists vs, k = map Val vs /\ derived V.prim s (rows_in rows) r vs.
  Proof.
  Admitted. (* STUB *)

  Lemma solve_complete : forall (s : spec V.t) rows lim db r vs,
    spec_ok s = true -> relational s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    derived V.prim s (rows_in rows) r vs -> row (D.view db) r (map Val vs) None.
  Proof.
  Admitted. (* STUB *)

  Lemma solve_saturates : forall (s : spec V.t) rows lim,
    spec_ok s = true -> relational s = true -> prim_free (spec_program s) = true ->
    rows_ok s rows = true ->
    N.to_nat (max_iter lim) >=
      2 * R.herbrand (spec_program s) (X.seed (spec_program s) rows) + 3 ->
    fst (X.solve (spec_program s) rows lim) = Saturated.
  Proof.
  Admitted. (* STUB *)
End Relational.
