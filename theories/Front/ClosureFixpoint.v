(** * The classes of the reference closure are a fixed point

    The passes of [classes] stop when one merges nothing, and every other pass merges two
    classes, so it lowers the number of classes. The fuel of one pass for each position of the
    universe therefore suffices, and a pass on the classes merges nothing.
    For example, with the equations [a = b], [f(a) = c] and [f(b) = d], the first pass merges
    [f(a)] with [f(b)], and the second pass merges nothing, so the passes stop.

    Builds on: the reference closure signature. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import ClosureSig.

Import List.ListNotations.

Module ClosureFixpoint (V : VALUE) <: CLOSURE_FIXPOINT V.
  Lemma classes_closed : forall eqs,
    pass V.eqb (universe V.eqb eqs) (classes V.eqb eqs) = classes V.eqb eqs.
  Proof.
  Admitted. (* STUB *)
End ClosureFixpoint.
