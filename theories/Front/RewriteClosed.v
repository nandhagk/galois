(** * Closure of a saturated outcome under rewrite steps

    A saturated outcome is closed under the rule of each rewrite. A rewrite step from a
    represented term has a body that holds in the input rows, which the outcome keeps, and a
    left side that the term matches, so the rule fires on the class of the term. Its actions
    are then present, so they build the right side and join it with the class. The theorem takes
    on purpose the plans of [RewriteTerms.v] and [RewriteMatch.v], which [Rewrite.v]
    instantiates.
    For example, at saturation the class of [Add a b] also represents [Add b a] under the
    commutativity rewrite.

    Builds on: the rewrite signature, the runner facts, the lowering laws and the run
    contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig RewriteSig.

Import List.ListNotations.

Module RewriteClosed (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PT : REWRITE_TERMS_PLAN V I J D R X) (PM : REWRITE_MATCH_PLAN V I J D R X)
    <: REWRITE_CLOSED V I J D R X.
  Lemma saturate_closed : forall (s : spec V.t) rows es lim db cs i t u,
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    represents (D.view db) (Id i) t -> rewrite_step V.prim s (rows_in rows) t u ->
    represents (D.view db) (Id i) u.
  Proof.
  Admitted. (* STUB *)
End RewriteClosed.
