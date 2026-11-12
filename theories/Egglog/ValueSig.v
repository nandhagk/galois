(** * Engine value layer headers

    These headers separate executable engine values from their laws and time contracts.
    Engine operations and contracts are placeholders for task 5.3.

    For example, an index can take VALUE_OPS before merge laws are supplied.
    Builds on: KeySig. *)

From Argent Require Import Time.

From Galois.Base Require Import KeySig.

Module Type VALUE_OPS.
  Include KEY_OPS.
End VALUE_OPS.

Module Type VALUE_SPEC (Import V : VALUE_OPS).
  Include KEY_SPEC V.
End VALUE_SPEC.

Module Type VALUE_LAWS (Import V : VALUE_OPS).
  Include KEY_LAWS V.
End VALUE_LAWS.

Module Type VALUE := VALUE_OPS <+ VALUE_SPEC <+ VALUE_LAWS.

Module Type VALUE_TIME (Import V : VALUE).
  Include KEY_TIME V.
End VALUE_TIME.

Module Type VALUE_T := VALUE <+ VALUE_TIME.

Module Type VALUE_PLAN (Import V : VALUE_T).
End VALUE_PLAN.

Module Type VALUE_ALL := VALUE_T <+ VALUE_PLAN.
