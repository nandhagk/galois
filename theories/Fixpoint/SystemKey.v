(** * Keys supplied by systems

    System adapters expose inline codes through the shared key interface.
    For example, a system key uses its existing code for both encoding and equality.
    Builds on: Base.KeySig and Fixpoint.SystemSig. *)

From Stdlib Require Import Bool PArith.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.

Module SystemKeyCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: KEY_OPS.
  Definition t := S.key.
  Definition encode := S.key_code.
  Definition eqb (a b : t) : bool := Pos.eqb (encode a) (encode b).
End SystemKeyCode.

Module SystemKey (L : LATTICE) (S : SYSTEM L) <: KEY.
  Include SystemKeyCode L S.
  Include KEY_SPEC.

  (** The adapter inherits the system's injective encoding. *)
  Theorem encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    exact S.key_code_inj.
  Qed.

  (** Equality of codes decides equality of system keys. *)
  Theorem eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros a b.
    unfold eqb.
    destruct (Pos.eqb_spec (encode a) (encode b)) as [Hcode | Hcode].
    - apply ReflectT.
      exact (encode_inj a b Hcode).
    - apply ReflectF.
      intro Heq.
      apply Hcode.
      now subst b.
  Qed.
End SystemKey.

(** Row operations use codes whose injectivity is scoped to each program's listed rows.
    A [KEY] adapter on all rows needs global injectivity in addition to [LOCAL_LAWS]. *)
Module SystemRowCode (L : LATTICE_OPS) (S : LOCAL_SYSTEM_OPS L) <: KEY_OPS.
  Definition t := S.row.
  Definition encode := S.row_code.
  Definition eqb (a b : t) : bool := Pos.eqb (encode a) (encode b).
End SystemRowCode.

(** A timed key adapter must bound both calls to [key_code] in [eqb].
    [SYSTEM_TIME] bounds the second call by the second key's size.
    [KEY_TIME] requires a bound using the first key's size alone. *)
