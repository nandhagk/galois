(** * The model of the classes of an outcome

    The classes of an outcome of a ground specification, extended freely to all terms, are a
    model that satisfies the outcome when each identifier means the class of its
    representative. An outcome holds the input rows, which are relation rows of values, and
    the rows of constructors, whose keys are canonical. It holds no lattice value, because the
    rules of a ground specification put no row, and so every run keeps the model with one
    element in which no lattice value holds.
    For example, the row [Cell 7 -> 3] of an outcome makes [Cell 7] mean the class of 3.

    Builds on: the ground signature, the runner facts, the lowering laws and the run
    contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig CongruenceRefSig GroundSig.

Import List.ListNotations.

Module GroundClasses (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    <: GROUND_CLASS_PLAN V I J D R X.
  Include GROUND_SPEC V I D.

  (* STUB: a model of one point that holds only the input rows satisfies the specification, so
     [LW.lower_valid] and [R.run_sat], from the seed by [F.seed_sat], make every row of the
     outcome an input row or a row with a class output. *)
  Lemma outcome_rows : forall (s : spec V.t) rows lim st db f k o,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (st, db) -> row (D.view db) f k o ->
    (o = None /\ exists vs, k = map Val vs /\ In (f, vs) rows) \/ (exists i, o = Some (Id i)).
  Proof.
  Admitted. (* STUB *)

  (* STUB: directly. The outcome is well formed and canonical by [R.run_wf], so a relation row
     holds by its own key and a constructor row by [D.old_row]. [outcome_rows] leaves no lattice
     row, and [D.same_repr] gives the equalities. *)
  Lemma class_sat : forall (s : spec V.t) rows lim st db,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (st, db) ->
    sat V.merge (class_model db) (class_nu db) (D.view db).
  Proof.
  Admitted. (* STUB *)

  Lemma class_nu_same : forall db i j, D.wf db -> class_nu db i = class_nu db j ->
    same (D.view db) i j.
  Proof.
  Admitted. (* STUB *)
End GroundClasses.
