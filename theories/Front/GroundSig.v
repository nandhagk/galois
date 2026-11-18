(** * Ground equational exactness

    A run of a ground specification computes exactly the congruence of its instances on the
    terms that it represents. Two represented terms in one class of any outcome are congruent
    ([solve_sound]), two represented congruent terms share a class of a saturated outcome
    ([solve_complete]), a saturated outcome represents each side of every instance
    ([solve_builds]), and enough iterations and identifiers saturate the run
    ([solve_saturates]). With the glue lemma of a derived program, these give the exactness of
    its equational inductive.
    For example, Steensgaard's [solve_exact] follows from them and
    [pointer_congruence_congruent].

    Builds on: the specifications, the runner, the exact model and the run contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig CongruenceRefSig.

Import List.ListNotations.

Module Type GROUND (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** Two represented terms in one class of any outcome are congruent. *)
  Parameter solve_sound : forall (s : spec V.t) rows lim i j t u,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    represents (D.view (snd (X.solve (spec_program s) rows lim))) (Id i) t ->
    represents (D.view (snd (X.solve (spec_program s) rows lim))) (Id j) u ->
    same (D.view (snd (X.solve (spec_program s) rows lim))) i j ->
    congruent V.prim s (rows_in rows) t u.
  (** Two represented congruent terms share a class of a saturated outcome. *)
  Parameter solve_complete : forall (s : spec V.t) rows lim db i j t u,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    represents (D.view db) (Id i) t -> represents (D.view db) (Id j) u ->
    congruent V.prim s (rows_in rows) t u -> same (D.view db) i j.
  (** A saturated outcome represents both sides of every instance whose body holds in the
      input rows. *)
  Parameter solve_builds : forall (s : spec V.t) rows lim db c e l r tl tr,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    In c (clauses s) -> head c = Unify l r ->
    Forall (input_premise V.prim (rows_in rows) e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    (exists i, represents (D.view db) (Id i) tl) /\ (exists j, represents (D.view db) (Id j) tr).
  (** Enough iterations and identifiers saturate a run of a ground specification. *)
  Parameter solve_saturates : forall (s : spec V.t) rows,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    exists n, forall lim, N.to_nat (max_iter lim) >= n -> N.to_nat (max_ids lim) >= n ->
      fst (X.solve (spec_program s) rows lim) = Saturated.
End GROUND.

(** * Proof plan *)

Module Type GROUND_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** A model of a ground specification validates the rules of its lowered program. *)
  Parameter model_valid : forall (s : spec V.t) I (M : @model V.t),
    ground s = true -> satisfies V.prim V.merge M s I ->
    valid_sorted V.prim V.merge M (spec_program s).
  (** A model of the input rows satisfies the seed under any valuation. *)
  Parameter seed_sat : forall (s : spec V.t) rows (M : @model V.t) nu,
    spec_ok s = true -> rows_ok s rows = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    sat V.merge M nu (D.view (X.seed (spec_program s) rows)).
  (** The classes of a saturated outcome form a model of the specification whose valuation
      separates distinct classes. *)
  Parameter saturated_model : forall (s : spec V.t) rows lim db,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    exists (M : @model V.t) nu, satisfies V.prim V.merge M s (rows_in rows) /\
      sat V.merge M nu (D.view db) /\ (forall i j, nu i = nu j -> same (D.view db) i j).
End GROUND_PLAN.
