(** * Key signatures

    Keys have injective positive encodings and a reflected equality test.
    For example, positive keys can use the identity encoding.
    Builds on: Stdlib binary arithmetic and Argent time interfaces. *)

From Stdlib Require Import PArith Bool.
From Argent Require Import Time.

Module Type TYPE.
  Parameter t : Type.
End TYPE.

Module Type KEY_OPS.
  Parameter t : Type.
  Parameter encode : t -> positive.
  Parameter eqb : t -> t -> bool.
End KEY_OPS.

Module Type KEY_SPEC (Import K : KEY_OPS).
  Definition bits (k : t) : nat := Pos.size_nat (encode k).
End KEY_SPEC.

Module Type KEY_LAWS (Import K : KEY_OPS).
  (** Equal encodings identify the same key. *)
  Parameter encode_inj : forall a b, encode a = encode b -> a = b.
  (** The Boolean test decides key equality. *)
  Parameter eqb_spec : forall a b, reflect (a = b) (eqb a b).
End KEY_LAWS.

Module Type KEY := KEY_OPS <+ KEY_SPEC <+ KEY_LAWS.

Module Type KEY_TIME (Import K : KEY).
  Parameter T_encode : t -> nat.
  Parameter T_eqb : t -> t -> nat.
  Parameter c_key : nat.
  (** Encoding takes time bounded by the key bit length. *)
  Parameter T_encode_le : forall k, T_encode k <= c_key * (bits k + 1).
  (** Equality testing takes time bounded by the first key bit length. *)
  Parameter T_eqb_le : forall a b, T_eqb a b <= c_key * (bits a + 1).
End KEY_TIME.

Module Type KEY_T := KEY <+ KEY_TIME.
