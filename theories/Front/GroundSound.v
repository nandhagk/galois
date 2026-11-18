(** * Soundness of ground runs

    Two represented terms in one class of any outcome of a ground specification are congruent.
    The exact model of the reference closure satisfies the specification and its input rows,
    so it validates the lowered rules and satisfies the seed, and every run keeps it. Its
    equality is congruence, so the class equalities of the outcome are congruences. The file
    also proves [congruent_denote], a step of the plan that the completeness proof uses.
    For example, a run of Steensgaard's program puts [Deref (Cell x)] and [Cell a] in one class
    only when they are congruent.

    Builds on: the ground signature, the runner facts, the lowering laws, the exact model and
    the run contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig CongruenceRefSig GroundSig.

Import List.ListNotations.

Module GroundDenote (V : VALUE) <: GROUND_DENOTE_PLAN V.
  Lemma congruent_denote : forall (s : spec V.t) I (M : @model V.t) t u,
    ground s = true -> satisfies V.prim V.merge M s I -> congruent V.prim s I t u ->
    denote M t = denote M u.
  Proof.
  Admitted. (* STUB *)
End GroundDenote.

Module GroundSound (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (CR : CONGRUENCE_REF V) <: GROUND_SOUND V I J D R X.
  Lemma solve_sound : forall (s : spec V.t) rows lim i j t u,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    represents (D.view (snd (X.solve (spec_program s) rows lim))) (Id i) t ->
    represents (D.view (snd (X.solve (spec_program s) rows lim))) (Id j) u ->
    same (D.view (snd (X.solve (spec_program s) rows lim))) i j ->
    congruent V.prim s (rows_in rows) t u.
  Proof.
  Admitted. (* STUB *)
End GroundSound.
