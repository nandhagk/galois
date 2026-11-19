(** * Closure of a saturated outcome under rewrites that read rows

    A saturated outcome is closed under the rule of each rewrite. A rewrite step whose premises
    read the rows and the stored values of the outcome has a body whose query matches there, and
    a left side that the represented term matches, so the rule fires on the class of the term.
    Its actions are then present, so they build the right side and join it with the class. The
    proof is the one of [RewriteClosed.v], with the queries of bodies whose reads see the stored
    values of [LatticeReadSig.v] in place of the queries of bodies that read input rows. The
    theorem takes the plans of [LatticeReadQueries.v], [RewriteTerms.v], [RewriteMatch.v],
    [RewriteReadValues.v] and [RewriteReadSorts.v] as parameters.

    For example, when the outcome stores the row [known 1 5], the class of
    [Mul (Ref 1) (Ref 2)] also represents [Scale 5 (Ref 2)].

    Builds on: the signature of rewrites that read rows and its plans, the plans of lattice
    reads and of rewrites, the runner facts, the lowering laws and the run contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecLattice SpecReads LowerSig RunnerSig LatticeReadSig
  RewriteSig RewriteReadSig.

Import List.ListNotations.

Module RewriteReadClosed (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (LQ : LATTICE_READ_QUERY_PLAN) (PT : REWRITE_TERMS_PLAN V I J D R X)
    (PM : REWRITE_MATCH_PLAN V I J D R X) (RV : REWRITE_READ_VALUES_PLAN)
    (RS : REWRITE_READ_SORTS_PLAN V) <: REWRITE_READ_CLOSED V I J D R X.
  (* STUB: [X.saturate_unfold] with [F.seed_ready] and [PT.add_terms_ready] gives a well-formed
     and loaded database before the run, and [R.run_closed] and [R.run_wf] give a closed,
     well-formed and canonical outcome. [RV.read_premise_values] reads the body of the step
     under [literal_env e], and [LQ.query_body_stored_matches], [PM.query_pat_complete] and
     [LW.checks_last_matches] match the query of [clause_rule c] on the class of the term. The
     closed outcome makes its actions present, [LQ.query_body_stored_lets] and
     [LW.build_pats_represents] build the right side, and [RS.read_right_app] makes it an
     application, which the union joins with the class. *)
  Lemma saturate_reads_closed : forall (s : spec V.t) rows es lim db cs i t u,
    spec_ok s = true -> value_tables s = true -> rows_ok s rows = true ->
    forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    represents (D.view db) (Id i) t ->
    read_step V.prim s (view_rows (D.view db)) (stored_at (D.view db)) t u ->
    represents (D.view db) (Id i) u.
  Proof.
  Admitted. (* STUB *)
End RewriteReadClosed.
