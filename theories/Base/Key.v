(** * Key implementations

    Scalar keys use positive encodings and reflected equality.
    For example, the positive key uses its value as its encoding.
    Builds on: Stdlib binary arithmetic and Argent time interfaces. *)

From Stdlib Require Import Bool NArith PArith ZArith Lia.
From Argent Require Import Time.
From Galois.Base Require Import KeySig.
From Stdlib Require Import List.
From Galois.Base Require Import Code.

Module PosKeyCode <: KEY_OPS.
  Definition t := positive.
  Definition encode (x : t) := x.
  Definition eqb := Pos.eqb.
End PosKeyCode.

Module NKeyCode <: KEY_OPS.
  Definition t := N.
  Definition encode := N.succ_pos.
  Definition eqb := N.eqb.
End NKeyCode.

Module ZKeyCode <: KEY_OPS.
  Definition t := Z.
  Definition encode (z : t) := match z with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
  Definition eqb := Z.eqb.
End ZKeyCode.

Module NatKeyCode <: KEY_OPS.
  Definition t := nat.
  Definition encode := Pos.of_succ_nat.
  Definition eqb := Nat.eqb.
End NatKeyCode.

Module BoolKeyCode <: KEY_OPS.
  Definition t := bool.
  Definition encode (b : t) := if b then xO xH else xH.
  Definition eqb := Bool.eqb.
End BoolKeyCode.

Module UnitKeyCode <: KEY_OPS.
  Definition t := unit.
  Definition encode (_ : t) := xH.
  Definition eqb (_ _ : t) := true.
End UnitKeyCode.

Module PairKeyCode (A B : KEY_OPS) <: KEY_OPS.
  Definition t := (A.t * B.t)%type.
  Definition encode := pair_code A.encode B.encode.
  Definition eqb (x y : t) := andb (A.eqb (fst x) (fst y)) (B.eqb (snd x) (snd y)).
End PairKeyCode.

Module SumKeyCode (A B : KEY_OPS) <: KEY_OPS.
  Definition t := (A.t + B.t)%type.
  Definition encode := sum_code A.encode B.encode.
  Definition eqb (x y : t) :=
    match x, y with
    | inl a, inl b => A.eqb a b
    | inr a, inr b => B.eqb a b
    | _, _ => false
    end.
End SumKeyCode.

Module OptionKeyCode (K : KEY_OPS) <: KEY_OPS.
  Definition t := option K.t.
  Definition encode := option_code K.encode.
  Definition eqb (x y : t) :=
    match x, y with
    | None, None => true
    | Some a, Some b => K.eqb a b
    | _, _ => false
    end.
End OptionKeyCode.

Module ListKeyCode (K : KEY_OPS) <: KEY_OPS.
  Definition t := list K.t.
  Definition encode := list_code K.encode.
  Fixpoint eqb (x y : t) : bool :=
    match x, y with
    | nil, nil => true
    | a :: x, b :: y => andb (K.eqb a b) (eqb x y)
    | _, _ => false
    end.
End ListKeyCode.
