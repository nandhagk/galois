(** * Database layer headers

    These headers pass engine dependencies at the layer each client needs.
    Operations and contracts are placeholders for task 5.3, and the plan waits for task 5.4.

    For example, a timed database takes a bundled VALUE_T dependency.
    Builds on: ValueSig and IndexSig. *)

From Argent Require Import Time.

From Galois.Egglog Require Import ValueSig IndexSig.

Module Type DATABASE_OPS (V : VALUE_OPS) (I : INDEX_OPS V).
  Parameter t : Type.
End DATABASE_OPS.

Module Type DATABASE_SPEC (V : VALUE_OPS) (I : INDEX_OPS V)
    (Import X : DATABASE_OPS V I).
End DATABASE_SPEC.

Module Type DATABASE_LAWS (V : VALUE) (I : INDEX V)
    (Import X : DATABASE_OPS V I).
End DATABASE_LAWS.

Module Type DATABASE (V : VALUE) (I : INDEX V) :=
  DATABASE_OPS V I <+ DATABASE_SPEC V I <+ DATABASE_LAWS V I.

Module Type DATABASE_TIME (V : VALUE_T) (I : INDEX_T V)
    (Import X : DATABASE V I).
End DATABASE_TIME.

Module Type DATABASE_T (V : VALUE_T) (I : INDEX_T V) :=
  DATABASE V I <+ DATABASE_TIME V I.

Module Type DATABASE_PLAN (V : VALUE_T) (I : INDEX_T V)
    (Import X : DATABASE_T V I).
End DATABASE_PLAN.

Module Type DATABASE_ALL (V : VALUE_T) (I : INDEX_T V) :=
  DATABASE_T V I <+ DATABASE_PLAN V I.

