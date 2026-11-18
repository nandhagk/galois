(** * Relational exactness

    The seed of a run holds exactly its input rows, the run keeps a derivation for each of its
    rows, and a saturated run is closed, so it holds every derived row. The lowering laws turn
    derivations of the program into derived rows of the specification and back.
    For example, a saturated run of [Path.program] holds a path exactly when [path] holds.

    Builds on: the relational signature, the lowering laws and the run contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig Lower RunnerSig RelationalSig.

Import List.ListNotations.

Module RelationalPlan (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: RELATIONAL_PLAN V I J D R X.
  Lemma seed_rows : forall (s : spec V.t) rows r k o,
    spec_ok s = true -> rows_ok s rows = true ->
    row (D.view (X.seed (spec_program s) rows)) r k o <->
      o = None /\ exists vs, k = map Val vs /\ In (r, vs) rows.
  Proof.
  Admitted. (* STUB *)

  Lemma seed_ready : forall (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    D.wf (X.seed (spec_program s) rows) /\
    R.loaded (spec_program s) (R.plan (spec_program s)) (X.seed (spec_program s) rows) /\
    R.no_ids (X.seed (spec_program s) rows).
  Proof.
  Admitted. (* STUB *)

  Lemma plan_ok : forall (s : spec V.t), spec_ok s = true ->
    R.plans_ok (spec_program s) (R.plan (spec_program s)).
  Proof.
  Admitted. (* STUB *)
End RelationalPlan.

Module Relational (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: RELATIONAL V I J D R X.
  Module P := RelationalPlan V I J D R X.

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

  Lemma holds_spec : forall db r vs, D.wf db ->
    X.holds r vs db = true <-> exists o, row (D.view db) r (map Val vs) o.
  Proof.
  Admitted. (* STUB *)
End Relational.
