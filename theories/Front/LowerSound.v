(** * Soundness of the lowering

    A row that the lowered program of a well-sorted relational specification derives is a
    derived row of the specification. A derivation through the rule of a clause matches its
    premises and computes its head, and the rule is scoped, so the values that its actions
    compute do not change what its query matched.
    For example, a derivation of [path 1 3] through the rule of [path_step] reads rows that the
    specification derives, so [path 1 3] is derived.

    Builds on: the lowering signature, through its pattern laws and its plan. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerSound (PV : LOWER_VALUES) (PS : LOWER_PLAN) <: LOWER_SOUND.
  Lemma lower_sound : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r k,
    check_program (spec_program s) = true -> relational_fragment (spec_program s) = true ->
    (forall r' k' o', row w0 r' k' o' ->
      In r' (inputs s) /\ o' = None /\ exists vs, k' = map Val vs) ->
    derives prim (spec_program s) w0 r k ->
    exists vs, k = map Val vs /\ derived prim s (view_rows w0) r vs.
  Proof.
  Admitted. (* STUB *)
End LowerSound.
