(** * Soundness of rewriting

    Equality saturation with the rewrites and rules of a specification keeps every model of
    it. Two represented terms in one class of any outcome have equal meanings in every model
    of the specification ([saturate_sound]). So any meaning that each rewrite preserves, such
    as an evaluator, is preserved by every equality that saturation finds.
    For example, a model that evaluates arithmetic satisfies the commutativity of addition, so
    [Add a b] and [Add b a] share a class only when their values are equal.

    Builds on: the specifications, their lowering and the saturation contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Egraph Require Import Syntax CompileSig SaturateSig.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

(** No input rows. *)
Definition no_rows {V} (r : positive) (vs : list V) : Prop := False.

Module Type REWRITE (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (E : RUN V I J D) (C : COMPILE V) (S : SATURATE V I J D E C).
  (** Two represented terms in one class of any outcome have equal meanings in every model
      of the specification. *)
  Parameter saturate_sound : forall (s : spec V.t) es lim st db cs i j t u (M : @model V.t),
    satisfies V.prim V.merge M s no_rows ->
    S.saturate (tables s) (spec_rewrites s) (spec_rules s) lim es = inr (st, db, cs) ->
    represents (D.view db) (Id i) t -> represents (D.view db) (Id j) u ->
    same (D.view db) i j -> denote M t = denote M u.
End REWRITE.

Module Type REWRITE_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (E : RUN V I J D) (C : COMPILE V) (S : SATURATE V I J D E C).
  (** A model of a specification is a model of its lowered rewrites and rules. *)
  Parameter satisfies_model_ok : forall (s : spec V.t) (M : @model V.t),
    satisfies V.prim V.merge M s no_rows ->
    S.model_ok M (tables s) (spec_rewrites s) (spec_rules s).
End REWRITE_PLAN.
