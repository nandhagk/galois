(** * Views closed under the lowered rules

    A view that the rules of a well-sorted specification close, and whose relation rows have
    no output, holds each row derived from its own rows. The rule of a clause matches the rows
    of its premises, and its actions are present, so they compute the values of its head.
    The completeness of the lowered program is in [LowerCompleteness.v].
    For example, a view that the rule of [path_step] closes holds [path 1 3] when it holds the
    rows [path 1 2] and [edge 2 3].

    Builds on: the lowering signature, through its pattern laws and the facts of bodies. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerComplete (PV : LOWER_VALUES) (PB : LOWER_BODY) <: LOWER_CLOSED.
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
