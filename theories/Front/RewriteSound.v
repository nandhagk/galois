(** * Soundness of equality saturation

    A model of a specification validates its rules, and adding terms keeps it a model, so
    every outcome of saturation keeps it. The cells of the added terms represent them in every
    outcome, so [equal] is sound. The theorem takes on purpose the plan of [RewriteTerms.v],
    which [Rewrite.v] instantiates.
    For example, an evaluator of arithmetic stays a model of the commutativity rewrite.

    Builds on: the rewrite signature, the runner facts, the lowering laws and the run
    contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig RewriteSig.

Import List.ListNotations.

Module RewriteSound (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PT : REWRITE_TERMS_PLAN V I J D R X) <: REWRITE_SOUND V I J D R X.
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

  Lemma equal_sound : forall (s : spec V.t) rows lim t u (M : @model V.t),
    spec_ok s = true -> rows_ok s rows = true -> term_ok s t = true -> term_ok s u = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    X.equal (spec_program s) rows lim t u = true -> denote M t = denote M u.
  Proof.
  Admitted. (* STUB *)
End RewriteSound.
