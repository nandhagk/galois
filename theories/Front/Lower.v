(** * Lowering laws

    The lowered program of a relational specification derives exactly its derived rows from a
    view of input rows. [lower_sound] follows a derivation of the program back to clauses of
    the specification, and [lower_complete] fires the rule of each clause.
    For example, the rule of [May_copy] fires on a copy row and a points-to row.

    Builds on: the lowering, the specifications and the engine models. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerLaws <: LOWER_LAWS.
  Lemma lower_sound : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r k,
    relational_fragment (spec_program s) = true ->
    (forall r' k' o', row w0 r' k' o' ->
      In r' (inputs s) /\ o' = None /\ exists vs, k' = map Val vs) ->
    derives prim (spec_program s) w0 r k ->
    exists vs, k = map Val vs /\ derived prim s (view_rows w0) r vs.
  Proof.
  Admitted. (* STUB *)

  Lemma lower_complete : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r vs,
    relational_fragment (spec_program s) = true ->
    derived prim s (view_rows w0) r vs -> derives prim (spec_program s) w0 r (map Val vs).
  Proof.
  Admitted. (* STUB *)
End LowerLaws.
