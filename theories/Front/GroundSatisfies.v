(** * The model of the classes satisfies a ground specification

    The model of the classes of a saturated outcome is a model of the specification and its
    input rows. The input rows are rows of the outcome, and a body that holds in the model
    reads input rows, so the rule of its clause has built both sides in one class, which the
    model reads as one class.
    For example, an address constraint [Addr x a] makes [Deref (Cell x)] and [Cell a] mean one
    class.

    Builds on: the ground signature, the runner facts and the plan that builds instances. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig CongruenceRefSig GroundSig.

Import List.ListNotations.

Module GroundSatisfies (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X)
    (B : GROUND_BUILD_PLAN V I J D R X) <: GROUND_SATISFIES_PLAN V I J D R X.
  Include GROUND_SPEC V I D.

  Lemma class_satisfies : forall (s : spec V.t) rows lim db,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    satisfies V.prim V.merge (class_model db) s (rows_in rows).
  Proof.
  Admitted. (* STUB *)
End GroundSatisfies.
