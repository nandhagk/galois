(** * Exactness of the unification-based pointer analysis

    The congruence of the derived unification program adds no equation to the source
    congruence, and a saturated run answers the points-to query exactly. The law module
    [Steensgaard] includes the base of [Steensgaard.v] and adds these two laws.
    For example, a saturated run answers [true] for [x] and [a] only when an address
    constraint, or a chain of constraints, makes [Deref (Cell x)] and [Cell a] congruent.

    Main results
    - [pointer_congruence_back] The congruence of the derived program adds no equation to the
      source congruence.
    - [solve_exact] Saturated query answers are exactly the source congruence approximation.

    Builds on: SteensgaardSig, the base of the Steensgaard driver, the runner facts and the
    ground theorems. *)

From Stdlib Require Import List PArith NArith Bool.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig CongruenceRefSig GroundSig.
From Galois.Clients Require Import AndersenSig SteensgaardSig Steensgaard.
Import List.ListNotations.

Module SteensgaardBack.
  (* STUB: an induction on [congruent] with the invariant that two related terms are equal,
     or are the encodings of two terms that [pointer_congruence] relates, or are applications
     of one constructor to related arguments. A literal is related only to itself, the
     encoding is injective, [Cell_code] differs from [Deref_code], and every clause side is
     the encoding of a [Cell] or [Deref] term over input values. *)
  Lemma pointer_congruence_back : forall prim q t u,
    congruent prim Unification.spec (Unification.inputs q)
      (Unification.encode_pointer_term t) (Unification.encode_pointer_term u) ->
    pointer_congruence q t u.
  Proof. Admitted. (* STUB *)
End SteensgaardBack.

Module Steensgaard (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (G : GROUND V I J D R X)
    <: STEENSGAARD V I J D R.
  Include SteensgaardBase V I J D R X F G.
  Include SteensgaardBack.

  (* STUB: a positive answer gives two represented terms in one class by [points_spec],
     [G.solve_sound] makes them congruent, and [pointer_congruence_back] gives the source
     congruence. The converse is [solve_covers]. *)
  Lemma solve_exact : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof. Admitted. (* STUB *)
End Steensgaard.
