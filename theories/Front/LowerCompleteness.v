(** * Completeness of the lowering

    The lowered program of a relational specification derives each derived row, because the
    rule of a clause fires on the rows of its premises and builds the values of its head.
    For example, the rule of [path_step] derives [path 1 3] from the rows [path 1 2] and
    [edge 2 3].

    Builds on: the lowering signature, through its pattern laws. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerCompleteness (PV : LOWER_VALUES) <: LOWER_COMPLETENESS.
  (* STUB: induction on [derived]. Each premise of the clause gives a derivation of the rows
     that its query atoms read, and [PV.build_pats_derivation] passes the derivation through
     the actions that build the head. *)
  Lemma lower_complete : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r vs,
    relational_fragment (spec_program s) = true ->
    derived prim s (view_rows w0) r vs -> derives prim (spec_program s) w0 r (map Val vs).
  Proof.
  Admitted. (* STUB *)
End LowerCompleteness.
