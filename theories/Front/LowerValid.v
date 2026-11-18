(** * Models validate the lowered rules

    A model of a well-sorted specification that passes the kind check validates the rules of
    its lowered program on well-sorted environments. The query of a rule holds in the model
    exactly when the premises of its clause hold, and its actions build the meanings of the
    head, which the model makes true.
    For example, a model in which addition commutes validates the rule that joins [Add a b]
    with [Add b a].

    Builds on: the lowering signature, through its pattern laws and its plan. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model Sorts.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Module LowerValid (PV : LOWER_VALUES) (PM : LOWER_MODELS) (PS : LOWER_PLAN) <: LOWER_VALID.
  Lemma lower_valid : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (s : spec V) I (M : @model V),
    check_program (spec_program s) = true -> kinds_ok s = true ->
    satisfies prim merge M s I -> valid_sorted prim merge M (spec_program s).
  Proof.
  Admitted. (* STUB *)
End LowerValid.
