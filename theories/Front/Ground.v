(** * Ground equational exactness

    Soundness reads class equalities in the exact model of the reference closure, which every
    run keeps. Completeness reads congruences in the model of a saturated outcome's classes.
    For example, a saturated run of Steensgaard's program puts [Deref (Cell x)] and [Cell a] in
    one class exactly when they are congruent.

    Builds on: the ground signature, the exact model and the run contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig CongruenceRefSig GroundSig.

Import List.ListNotations.

Module GroundPlan (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: GROUND_PLAN V I J D R X.
  Lemma model_valid : forall (s : spec V.t) I (M : @model V.t),
    ground s = true -> satisfies V.prim V.merge M s I ->
    valid_sorted V.prim V.merge M (spec_program s).
  Proof.
  Admitted. (* STUB *)

  Lemma seed_sat : forall (s : spec V.t) rows (M : @model V.t) nu,
    spec_ok s = true -> rows_ok s rows = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    sat V.merge M nu (D.view (X.seed (spec_program s) rows)).
  Proof.
  Admitted. (* STUB *)

  Lemma saturated_model : forall (s : spec V.t) rows lim db,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    exists (M : @model V.t) nu, satisfies V.prim V.merge M s (rows_in rows) /\
      sat V.merge M nu (D.view db) /\ (forall i j, nu i = nu j -> same (D.view db) i j).
  Proof.
  Admitted. (* STUB *)
End GroundPlan.

Module Ground (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (CR : CONGRUENCE_REF V) <: GROUND V I J D R X.
  Module P := GroundPlan V I J D R X.

  Lemma solve_sound : forall (s : spec V.t) rows lim i j t u,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    represents (D.view (snd (X.solve (spec_program s) rows lim))) (Id i) t ->
    represents (D.view (snd (X.solve (spec_program s) rows lim))) (Id j) u ->
    same (D.view (snd (X.solve (spec_program s) rows lim))) i j ->
    congruent V.prim s (rows_in rows) t u.
  Proof.
  Admitted. (* STUB *)

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

  Lemma solve_saturates : forall (s : spec V.t) rows,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    exists n, forall lim, N.to_nat (max_iter lim) >= n -> N.to_nat (max_ids lim) >= n ->
      fst (X.solve (spec_program s) rows lim) = Saturated.
  Proof.
  Admitted. (* STUB *)
End Ground.
