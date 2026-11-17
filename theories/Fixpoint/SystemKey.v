(** * Keys supplied by systems

    System adapters expose inline codes through the shared key interface.
    For example, a system key uses its existing code for both encoding and equality.

    Main results
    - [encode_inj] Distinct keys have distinct inline codes.
    - [eqb_spec] Equality of codes decides equality of system keys.

    Builds on: Base.KeySig and Fixpoint.SystemSig. *)

From Stdlib Require Import Bool PArith NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.

Module SystemKeyCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: KEY_OPS.
  Definition t := S.key.
  Definition encode := S.key_code.
  Definition eqb := S.key_eqb.
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
    exact S.key_eqb_spec.
  Qed.
End SystemKey.

(** Row operations use codes whose injectivity is scoped to each program's listed rows.
    A [KEY] adapter on all rows needs global injectivity in addition to [LOCAL_LAWS]. *)
Module SystemRowCode (L : LATTICE_OPS) (S : LOCAL_SYSTEM_OPS L) <: KEY_OPS.
  Definition t := S.row.
  Definition encode := S.row_code.
  Definition eqb (a b : t) : bool := Pos.eqb (encode a) (encode b).
End SystemRowCode.

Module SystemKeyT (L : LATTICE_T) (S : SYSTEM_T L) <: KEY_T.
  Include SystemKey L S.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := S.c_sys + 1.

  (** Encoding uses the system's code budget. *)
  Lemma T_encode_le : forall x,
    (T_encode x <= c_key * N.of_nat (bits x + 1))%N.
  Proof.
    intro x. pose proof (S.T_key_code_le x) as Hencode.
    unfold c_key, bits, encode, S.key_bits in *.
    time_unfold T_encode. rewrite Nat2N.inj_add in *. nia.
  Qed.

  (** Equality uses the system's first-operand budget. *)
  Lemma T_eqb_le : forall a b,
    (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof.
    intros a b. pose proof (S.T_key_eqb_le a b) as Hcompare.
    unfold c_key, bits, encode, S.key_bits in *.
    time_unfold T_eqb. rewrite Nat2N.inj_add in *. nia.
  Qed.
End SystemKeyT.
