(** * Equality saturation

    Equality saturation adds some terms to the seed of a specification and runs its rules on
    the engine, one rule for each clause. Every outcome keeps every model of the
    specification, so two represented terms in one class have equal meanings in every model
    ([saturate_sound]). Any meaning that each rewrite preserves, such as an evaluator, is
    therefore preserved by every equality that saturation finds. The cell of each added term
    represents it ([saturate_represents]), so [equal] is sound ([equal_sound]). At saturation,
    a rewrite step from a represented term reaches a term of the same class
    ([saturate_closed]).
    For example, a model that evaluates arithmetic satisfies the commutativity of addition, so
    [Add a b] and [Add b a] share a class only when their values are equal.

    Builds on: the specifications, their lowering, the runner and the run contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig.

Import List.ListNotations.

Module Type REWRITE (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** Two represented terms in one class of any outcome have equal meanings in every model of
      the specification and its input rows. *)
  Parameter saturate_sound : forall (s : spec V.t) rows es lim st db cs i j t u
      (M : @model V.t),
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) ->
    represents (D.view db) (Id i) t -> represents (D.view db) (Id j) u ->
    same (D.view db) i j -> denote M t = denote M u.
  (** The cell of each added term represents it in every outcome. *)
  Parameter saturate_represents : forall (s : spec V.t) rows es lim st db cs n e c,
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) ->
    nth_error es n = Some e -> nth_error cs n = Some c -> represents (D.view db) c e.
  (** At saturation, a rewrite step from a represented term reaches a term of its class. *)
  Parameter saturate_closed : forall (s : spec V.t) rows es lim db cs i t u,
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    represents (D.view db) (Id i) t -> rewrite_step V.prim s (rows_in rows) t u ->
    represents (D.view db) (Id i) u.
  (** Saturation says that two terms are equal only when they have equal meanings in every
      model of the specification and its input rows. *)
  Parameter equal_sound : forall (s : spec V.t) rows lim t u (M : @model V.t),
    spec_ok s = true -> rows_ok s rows = true -> term_ok s t = true -> term_ok s u = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    X.equal (spec_program s) rows lim t u = true -> denote M t = denote M u.
End REWRITE.

(** * Proof plan *)

Module Type REWRITE_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** A model of a specification validates the rules of its lowered program. *)
  Parameter model_valid : forall (s : spec V.t) I (M : @model V.t),
    satisfies V.prim V.merge M s I -> valid_sorted V.prim V.merge M (spec_program s).
  (** Adding well-sorted terms to a satisfied database keeps it satisfied under a valuation
      that agrees on the old identifiers and gives each added cell the meaning of its term. *)
  Parameter add_terms_sat : forall (s : spec V.t) es db cs db' (M : @model V.t) nu,
    D.wf db -> forallb (term_ok s) es = true -> X.add_terms es db = (cs, db') ->
    sat V.merge M nu (D.view db) ->
    exists nu', (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view db') /\ Forall2 (fun c e => den nu' c = denote M e) cs es.
  (** A represented instance of a pattern matches the query atoms of the pattern under an
      environment that binds each variable at a table position to a cell that represents its
      value, and the term of the pattern to the class of the instance. *)
  Parameter query_pat_complete : forall db next (p : pat V.t) e t i,
    D.wf db -> D.canonical db -> pat_term V.prim e p = Some t ->
    represents (D.view db) (Id i) t ->
    exists env, matches V.prim (D.view db) (fst (fst (query_pat next p))) env /\
      term_value env (snd (fst (query_pat next p))) (Id (D.repr db i)) /\
      (forall x u, In x (pat_bound p) -> e x = Some u ->
        exists c, env x = Some c /\ represents (D.view db) c u).
End REWRITE_PLAN.
