(** * Index layer headers

    These headers pass engine dependencies at the layer each client needs.
    Operations and contracts are placeholders for task 5.3.

    For example, a timed index takes a bundled VALUE_T dependency.
    Builds on: ValueSig. *)

From Argent Require Import Time.

From Galois.Egglog Require Import ValueSig.

Module Type INDEX_OPS (V : VALUE_OPS).
  Parameter t : Type.
End INDEX_OPS.

Module Type INDEX_SPEC (V : VALUE_OPS)
    (Import X : INDEX_OPS V).
End INDEX_SPEC.

Module Type INDEX_LAWS (V : VALUE)
    (Import X : INDEX_OPS V).
End INDEX_LAWS.

Module Type INDEX (V : VALUE) :=
  INDEX_OPS V <+ INDEX_SPEC V <+ INDEX_LAWS V.

Module Type INDEX_TIME (V : VALUE_T)
    (Import X : INDEX V).
End INDEX_TIME.

Module Type INDEX_T (V : VALUE_T) :=
  INDEX V <+ INDEX_TIME V.

Module Type INDEX_PLAN (V : VALUE_T)
    (Import X : INDEX_T V).
End INDEX_PLAN.

Module Type INDEX_ALL (V : VALUE_T) :=
  INDEX_T V <+ INDEX_PLAN V.
