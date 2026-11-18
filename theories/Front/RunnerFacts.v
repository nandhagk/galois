(** * Facts of the runner

    The facts that every theorem about a run needs, and the timed runner. The seed of a
    specification that passes its checks holds exactly its input rows, as rows of values
    without output, and the run contracts of the engine apply to it. A model of the input rows
    satisfies the seed, every outcome keeps the input rows, and a lookup says whether a
    database has a row. The timed runner derives the time function of each operation, and
    seeding and solving pay for their parts.
    For example, [seed_rows] says that the seed of [Path.program] on the edges 1 to 2 and 2 to 3
    holds exactly the two edge rows.

    Builds on: the runner signature, the runner and the engine contracts. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig Runner.

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

Module RunnerT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) <: RUNNER_T V I J D R.
  Include Runner V I J D R.
  TimeFun put_row.
  TimeFun seed.
  TimeFun solve.
  TimeFun holds.
  TimeFun add_term.
  TimeFun add_terms.
  TimeFun saturate.
  TimeFun same_cell.
  TimeFun equal.
  Definition c_runner : N := 1. (* STUB *)

  Lemma T_seed_le : forall B U (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    (D.ids (seed (spec_program s) rows) <= B)%N -> D.unit (seed (spec_program s) rows) <= U ->
    (T_seed (spec_program s) rows <=
      R.T_plan (spec_program s) + R.T_load (spec_program s) (R.plan (spec_program s)) +
      c_runner * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (fold_right
          (fun row n => ((length (snd row) + 2) * (length (snd row) + 2) + n)%nat) 0%nat rows +
          1))%N.
  Proof.
  Admitted. (* STUB *)

  Lemma T_solve_split : forall p rows lim,
    (T_solve p rows lim <=
      T_seed p rows + R.T_plan p + R.T_run p (R.plan p) lim (seed p rows) + c_runner)%N.
  Proof.
  Admitted. (* STUB *)
End RunnerT.
