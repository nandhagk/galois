(** * Adding terms to a database

    Adding well-sorted terms to a database loaded with the planned program makes or reuses
    one constructor row for each application, so the database stays well formed and loaded,
    keeps its rows, and gains cells that represent the terms. A model of the database stays a
    model, with each added cell meaning its term.
    For example, adding [Add (Num 1) (Num 2)] makes the rows of [Num 1], [Num 2] and the sum.

    Builds on: the rewrite signature and the database contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig RewriteSig.

Import List.ListNotations.

Module RewriteTerms (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: REWRITE_TERMS_PLAN V I J D R X.
  Lemma add_terms_sat : forall (s : spec V.t) es db cs db' (M : @model V.t) nu,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    forallb (term_ok s) es = true -> X.add_terms es db = (cs, db') ->
    sat V.merge M nu (D.view db) ->
    exists nu', (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view db') /\ Forall2 (fun c e => den nu' c = denote M e) cs es.
  Proof.
  Admitted. (* STUB *)

  Lemma add_terms_ready : forall (s : spec V.t) es db cs db',
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    forallb (term_ok s) es = true -> X.add_terms es db = (cs, db') ->
    D.wf db' /\ R.loaded (spec_program s) (R.plan (spec_program s)) db' /\
    (forall f k o, row (D.view db) f k o -> row (D.view db') f k o) /\
    Forall2 (represents (D.view db')) cs es.
  Proof.
  Admitted. (* STUB *)
End RewriteTerms.
