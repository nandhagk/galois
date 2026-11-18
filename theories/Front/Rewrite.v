(** * Soundness of rewriting

    A model of a specification satisfies each lowered rewrite and rule, so saturation keeps it.
    For example, an evaluator of arithmetic stays a model of the commutativity rewrite.

    Builds on: the rewrite signature and the saturation contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Egraph Require Import Syntax CompileSig SaturateSig.
From Galois.Front Require Import Spec LowerSig RewriteSig.

Import List.ListNotations.

Module RewritePlan (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (E : RUN V I J D) (C : COMPILE V) (S : SATURATE V I J D E C)
    <: REWRITE_PLAN V I J D E C S.
  Lemma satisfies_model_ok : forall (s : spec V.t) (M : @model V.t),
    satisfies V.prim V.merge M s no_rows ->
    S.model_ok M (tables s) (spec_rewrites s) (spec_rules s).
  Proof.
  Admitted. (* STUB *)
End RewritePlan.

Module Rewrite (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (E : RUN V I J D) (C : COMPILE V) (S : SATURATE V I J D E C) <: REWRITE V I J D E C S.
  Lemma saturate_sound : forall (s : spec V.t) es lim st db cs i j t u (M : @model V.t),
    satisfies V.prim V.merge M s no_rows ->
    S.saturate (tables s) (spec_rewrites s) (spec_rules s) lim es = inr (st, db, cs) ->
    represents (D.view db) (Id i) t -> represents (D.view db) (Id j) u ->
    same (D.view db) i j -> denote M t = denote M u.
  Proof.
  Admitted. (* STUB *)
End Rewrite.
