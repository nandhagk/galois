(** * Completeness of the lowering

    The lowered program of a relational specification derives each derived row, because the
    rule of a clause fires on the rows of its premises and builds the values of its head. A
    view that the rules of a well-sorted specification close holds each row derived from its
    own rows, for the same reason.
    For example, the rule of [path_step] derives [path 1 3] from the rows [path 1 2] and
    [edge 2 3].

    Builds on: the lowering signature, through its pattern laws and the facts of bodies. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerComplete (PV : LOWER_VALUES) (PB : LOWER_BODY) <: LOWER_COMPLETE.
  Lemma lower_complete : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r vs,
    relational_fragment (spec_program s) = true ->
    derived prim s (view_rows w0) r vs -> derives prim (spec_program s) w0 r (map Val vs).
  Proof.
  Admitted. (* STUB *)

  (* STUB: induction on the derivation. The query of the rule of a clause matches by
     [PB.query_body_matches] and [PB.checks_last_matches], its definitions compute the values
     of the equations by [PB.query_body_lets], and its head actions compute the values of the
     head by [PV.build_pats_present_sound], so the closed view holds the row. *)
  Lemma lower_closed : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (s : spec V) (w : @view V) r vs,
    check_program (spec_program s) = true -> closed prim merge (spec_program s) w ->
    (forall f k o, row w f k o -> lookup_kind (tables s) f = Some ORel -> o = None) ->
    derived prim s (view_rows w) r vs -> view_rows w r vs.
  Proof.
  Admitted. (* STUB *)
End LowerComplete.
