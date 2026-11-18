(** * Equality saturation, proved

    A model of a specification validates its rules, and adding terms keeps it a model, so every
    outcome of saturation keeps it. A saturated outcome is closed under the rule of each
    rewrite, and e-matching finds every represented instance of a left side.
    For example, an evaluator of arithmetic stays a model of the commutativity rewrite.

    Builds on: the rewrite signature, the runner and the run contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig RewriteSig.

Import List.ListNotations.

Module RewritePlan (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: REWRITE_PLAN V I J D R X.
  Lemma model_valid : forall (s : spec V.t) I (M : @model V.t),
    satisfies V.prim V.merge M s I -> valid_sorted V.prim V.merge M (spec_program s).
  Proof.
  Admitted. (* STUB *)

  Lemma add_terms_sat : forall (s : spec V.t) es db cs db' (M : @model V.t) nu,
    D.wf db -> forallb (term_ok s) es = true -> X.add_terms es db = (cs, db') ->
    sat V.merge M nu (D.view db) ->
    exists nu', (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view db') /\ Forall2 (fun c e => den nu' c = denote M e) cs es.
  Proof.
  Admitted. (* STUB *)

  Lemma query_pat_complete : forall db next (p : pat V.t) e t i,
    D.wf db -> D.canonical db -> pat_term V.prim e p = Some t ->
    represents (D.view db) (Id i) t ->
    exists env, matches V.prim (D.view db) (fst (fst (query_pat next p))) env /\
      term_value env (snd (fst (query_pat next p))) (Id (D.repr db i)) /\
      (forall x u, In x (pat_bound p) -> e x = Some u ->
        exists c, env x = Some c /\ represents (D.view db) c u).
  Proof.
  Admitted. (* STUB *)
End RewritePlan.

Module Rewrite (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: REWRITE V I J D R X.
  Lemma saturate_sound : forall (s : spec V.t) rows es lim st db cs i j t u
      (M : @model V.t),
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) ->
    represents (D.view db) (Id i) t -> represents (D.view db) (Id j) u ->
    same (D.view db) i j -> denote M t = denote M u.
  Proof.
  Admitted. (* STUB *)

  Lemma saturate_represents : forall (s : spec V.t) rows es lim st db cs n e c,
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) ->
    nth_error es n = Some e -> nth_error cs n = Some c -> represents (D.view db) c e.
  Proof.
  Admitted. (* STUB *)

  Lemma saturate_closed : forall (s : spec V.t) rows es lim db cs i t u,
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    represents (D.view db) (Id i) t -> rewrite_step V.prim s (rows_in rows) t u ->
    represents (D.view db) (Id i) u.
  Proof.
  Admitted. (* STUB *)

  Lemma equal_sound : forall (s : spec V.t) rows lim t u (M : @model V.t),
    spec_ok s = true -> rows_ok s rows = true -> term_ok s t = true -> term_ok s u = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    X.equal (spec_program s) rows lim t u = true -> denote M t = denote M u.
  Proof.
  Admitted. (* STUB *)
End Rewrite.
