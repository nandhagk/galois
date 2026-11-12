(** * Relational keys

    Relational keys distinguish signed literals and a producer's temporary variable.
    For example, positive and negative occurrences of x have different encodings.
    Builds on: KeySig and the core OptionKey towers in Key. *)

From Stdlib Require Import PArith Bool.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig Key.

Module Bool.
  TimeFun Bool.eqb.
End Bool.
Import Bool.

Module LitKeyCode (X : KEY_OPS) <: KEY_OPS.
  Definition t := (X.t * bool)%type.
  Definition encode (x : t) : positive :=
    if snd x then xI (X.encode (fst x)) else xO (X.encode (fst x)).
  Definition eqb (x y : t) : bool :=
    Bool.eqb (snd x) (snd y) && X.eqb (fst x) (fst y).
End LitKeyCode.

Module LitKey (X : KEY) <: KEY.
  Include LitKeyCode X.
  Include KEY_SPEC.
  (** The sign bit and the variable encoding determine the literal. *)
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. Admitted.
  (** Literal equality compares the sign and the variable. *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. Admitted.
End LitKey.

(** The temporary variable uses the absent branch of the core option encoding. *)
Module TmpKeyCode (X : KEY_OPS) := OptionKeyCode X.

Module TmpKey (X : KEY) := OptionKey X.

