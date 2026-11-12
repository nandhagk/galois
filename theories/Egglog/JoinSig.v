(** * Join layer headers

    These headers pass engine dependencies at the layer each client needs.
    Operations and contracts are placeholders for task 5.3.

    For example, a timed join takes a bundled VALUE_T dependency.
    Builds on: ValueSig and IndexSig. *)

From Argent Require Import Time.

From Galois.Egglog Require Import ValueSig IndexSig.

Module Type JOIN_OPS (V : VALUE_OPS) (I : INDEX_OPS V).
  Parameter t : Type.
End JOIN_OPS.

Module Type JOIN_SPEC (V : VALUE_OPS) (I : INDEX_OPS V)
    (Import X : JOIN_OPS V I).
End JOIN_SPEC.

Module Type JOIN_LAWS (V : VALUE) (I : INDEX V)
    (Import X : JOIN_OPS V I).
End JOIN_LAWS.

Module Type JOIN (V : VALUE) (I : INDEX V) :=
  JOIN_OPS V I <+ JOIN_SPEC V I <+ JOIN_LAWS V I.

Module Type JOIN_TIME (V : VALUE_T) (I : INDEX_T V)
    (Import X : JOIN V I).
End JOIN_TIME.

Module Type JOIN_T (V : VALUE_T) (I : INDEX_T V) :=
  JOIN V I <+ JOIN_TIME V I.

Module Type JOIN_PLAN (V : VALUE_T) (I : INDEX_T V)
    (Import X : JOIN_T V I).
End JOIN_PLAN.

Module Type JOIN_ALL (V : VALUE_T) (I : INDEX_T V) :=
  JOIN_T V I <+ JOIN_PLAN V I.
