(** * Engine values

    Values provide primitive evaluation and idempotent commutative merges.
    For example, an analysis value can merge two facts about one function output.
    Builds on: KeySig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time.
From Galois.Base Require Import KeySig.

Module Type VALUE_OPS.
  Include KEY_OPS.
  Parameter prim : positive -> list t -> option t.
  Parameter merge : positive -> t -> t -> t.
End VALUE_OPS.

Module Type VALUE_SPEC (Import V : VALUE_OPS).
  Include KEY_SPEC V.
End VALUE_SPEC.

Module Type VALUE_LAWS (Import V : VALUE_OPS).
  Include KEY_LAWS V.
  (** Merge order does not affect the value. *)
  Parameter merge_comm : forall m a b, merge m a b = merge m b a.
  (** Grouping merges does not affect the value. *)
  Parameter merge_assoc : forall m a b c,
    merge m a (merge m b c) = merge m (merge m a b) c.
  (** Merging a value with itself leaves it unchanged. *)
  Parameter merge_idem : forall m a, merge m a a = a.
End VALUE_LAWS.

Module Type VALUE := VALUE_OPS <+ VALUE_SPEC <+ VALUE_LAWS.

Module Type VALUE_TIME (Import V : VALUE).
  Include KEY_TIME V.
  (* spec: prim_work *)
  Parameter prim_work : positive -> list t -> N.
  Parameter T_prim : positive -> list t -> N.
  Parameter T_merge : positive -> t -> t -> N.
  Parameter c_val : N.
  (** Primitive evaluation pays for its declared work. *)
  Parameter T_prim_le : forall p xs,
    (T_prim p xs <= c_val * (prim_work p xs + 1))%N.
  (** Merging pays for both encoded values. *)
  Parameter T_merge_le : forall m a b,
    (T_merge m a b <= c_val * N.of_nat (bits a + bits b + 1))%N.
End VALUE_TIME.

Module Type VALUE_T := VALUE <+ VALUE_TIME.

Module Type VALUE_PLAN (Import V : VALUE_T).
End VALUE_PLAN.

Module Type VALUE_ALL := VALUE_T <+ VALUE_PLAN.
