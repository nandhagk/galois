(** * Derived rows of a saturated outcome with equations

    A saturated outcome is closed under every rule, also when the specification has equations,
    and its relation rows have no output. The lowering law [lower_closed] then puts every row
    derived from the rows of the outcome in the outcome. The outcome keeps the input rows, so it
    holds every row derived from them ([saturate_rows_complete]). A rewrite step whose premises
    read derived rows therefore reads rows of the outcome, and the closure of
    [REWRITE_READ_CLOSED] applies to it ([saturate_derived_closed]). The theorems take the plan
    of [RewriteTerms.v] and the closure of [RewriteReadClosed.v] as parameters.

    For example, a saturated outcome of constant propagation with rewrites stores [known 1 5]
    when [known 1 5] is a derived row, so it joins [Mul (Ref 1) (Ref 2)] with
    [Scale 5 (Ref 2)].

    Builds on: the signature of rewrites that read rows, the meaning of equations that read
    rows, the facts of specifications, the runner facts, the lowering laws, the plan of added
    terms and the run contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts SpecLattice SpecReads LowerSig RunnerSig
  LatticeReadSig RewriteSig RewriteReadSig.

Import List.ListNotations.

Module RewriteReadRows (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PT : REWRITE_TERMS_PLAN V I J D R X) (RC : REWRITE_READ_CLOSED V I J D R X)
    <: REWRITE_READ_ROWS V I J D R X.
  (* STUB: [X.saturate_unfold] with [F.seed_ready], [F.plan_ok] and [PT.add_terms_ready] gives
     a well-formed and loaded database before the run, and [R.run_closed] and [R.run_wf] give a
     closed and loaded outcome. [loaded] gives [view_sorted], so a row of a relation has no
     output. [F.saturate_keeps] puts the input rows in the outcome, [derived_mono] moves the
     derived row to the rows of the outcome, and [LW.lower_closed] stores it. *)
  Lemma saturate_rows_complete : forall (s : spec V.t) rows es lim db cs r vs,
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    derived V.prim s (rows_in rows) r vs -> row (D.view db) r (map Val vs) None.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [read_step_mono] moves the step to the rows of the outcome by
     [saturate_rows_complete], and to its stored values, because [no_values] holds of no
     value. [RC.saturate_reads_closed] concludes. *)
  Lemma saturate_derived_closed : forall (s : spec V.t) rows es lim db cs i t u,
    spec_ok s = true -> value_tables s = true -> rows_ok s rows = true ->
    forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    represents (D.view db) (Id i) t ->
    read_step V.prim s (derived V.prim s (rows_in rows)) no_values t u ->
    represents (D.view db) (Id i) u.
  Proof.
  Admitted. (* STUB *)
End RewriteReadRows.
