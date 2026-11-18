(** * Relational exactness

    A run of a relational specification computes exactly its derived rows. Every row of every
    outcome is derived from the input rows ([solve_sound]), a saturated outcome holds every
    derived row ([solve_complete]), and enough iterations saturate a specification without
    primitives ([solve_saturates]). With the glue lemma of a derived program, these give the
    exactness of the inductive that the program is read from.
    For example, Andersen's [solve_exact] is [solve_sound], [solve_complete] and
    [Andersen.may_points_spec].

    Builds on: the specifications, the runner and the run contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig.

Import List.ListNotations.

Module Type RELATIONAL (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** Every row of every outcome is a derived row of values. *)
  Parameter solve_sound : forall (s : spec V.t) rows lim r k o,
    spec_ok s = true -> relational s = true -> rows_ok s rows = true ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) r k o ->
    o = None /\ exists vs, k = map Val vs /\ derived V.prim s (rows_in rows) r vs.
  (** A saturated outcome holds every derived row. *)
  Parameter solve_complete : forall (s : spec V.t) rows lim db r vs,
    spec_ok s = true -> relational s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    derived V.prim s (rows_in rows) r vs -> row (D.view db) r (map Val vs) None.
  (** A run with at least the Herbrand budget of its seed saturates a specification without
      primitives. *)
  Parameter solve_saturates : forall (s : spec V.t) rows lim,
    spec_ok s = true -> relational s = true -> prim_free (spec_program s) = true ->
    rows_ok s rows = true ->
    N.to_nat (max_iter lim) >=
      2 * R.herbrand (spec_program s) (X.seed (spec_program s) rows) + 3 ->
    fst (X.solve (spec_program s) rows lim) = Saturated.
  (** A lookup reads whether a well-formed database holds a row of values. *)
  Parameter holds_spec : forall db r vs, D.wf db ->
    X.holds r vs db = true <-> exists o, row (D.view db) r (map Val vs) o.
End RELATIONAL.

(** * Proof plan *)

Module Type RELATIONAL_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** The seed holds exactly the input rows. *)
  Parameter seed_rows : forall (s : spec V.t) rows r k o,
    spec_ok s = true -> rows_ok s rows = true ->
    row (D.view (X.seed (spec_program s) rows)) r k o <->
      o = None /\ exists vs, k = map Val vs /\ In (r, vs) rows.
  (** The seed is well formed, loaded with the planned program, and has no identifier. *)
  Parameter seed_ready : forall (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    D.wf (X.seed (spec_program s) rows) /\
    R.loaded (spec_program s) (R.plan (spec_program s)) (X.seed (spec_program s) rows) /\
    R.no_ids (X.seed (spec_program s) rows).
  (** The planned program of a well-sorted specification passes its plan check. *)
  Parameter plan_ok : forall (s : spec V.t), spec_ok s = true ->
    R.plans_ok (spec_program s) (R.plan (spec_program s)).
End RELATIONAL_PLAN.
