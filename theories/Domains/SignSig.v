(** * Signed sign payload interfaces

    Three flags describe negative, zero and positive signed word values.
    For example, enabling zero and positive describes nonnegative signed values.
    Builds on: WordSig. *)

From Stdlib Require Import ZArith List Bool.
From Argent Require Import BigO.
From Galois.Domains Require Import WordSig.

Record sgn : Type := Sgn {
  neg : bool;
  zero : bool;
  pos : bool
}.

Module Type SIGN_OPS (L : WORD_LANGUAGE_OPS).
  Include WORD_PAYLOAD_OPS L with Definition p := sgn.
  Parameter sign_not sign_neg : sgn -> sgn.
  Parameter sign_and sign_or sign_xor : sgn -> sgn -> sgn.
End SIGN_OPS.

Module Type SIGN_SPEC (L : WORD_LANGUAGE_OPS) (Import S : SIGN_OPS L).
  Definition sign_gamma (w : positive) (a : sgn) (z : Z) : Prop :=
    if (L.signed w z <? 0)%Z then neg a = true
    else if (L.signed w z =? 0)%Z then zero a = true else pos a = true.
  Definition sign_level (a : sgn) : nat :=
    (if neg a then 1 else 0) + (if zero a then 1 else 0) + (if pos a then 1 else 0).
End SIGN_SPEC.

Module Type SIGN (L : WORD_LANGUAGE) :=
  SIGN_OPS L <+ SIGN_SPEC L <+ WORD_PAYLOAD_LAWS L.

Module Type SIGN_TIME (L : WORD_LANGUAGE_T) (Import S : SIGN L).
  Include WORD_PAYLOAD_TIME L S.
  Parameter T_sign_not T_sign_neg : sgn -> N.
  Parameter T_sign_and T_sign_or T_sign_xor : sgn -> sgn -> N.
  Parameter c_sign : N.
  (** Sign negation charges a constant number of flag operations. *)
  Parameter T_sign_not_le : forall a, (T_sign_not a <= c_sign)%N.
  (** Arithmetic negation charges a constant number of flag operations. *)
  Parameter T_sign_neg_le : forall a, (T_sign_neg a <= c_sign)%N.
  (** Sign conjunction charges a constant number of flag operations. *)
  Parameter T_sign_and_le : forall a b, (T_sign_and a b <= c_sign)%N.
  (** Sign disjunction charges a constant number of flag operations. *)
  Parameter T_sign_or_le : forall a b, (T_sign_or a b <= c_sign)%N.
  (** Sign exclusive disjunction charges a constant number of flag operations. *)
  Parameter T_sign_xor_le : forall a b, (T_sign_xor a b <= c_sign)%N.
  (** Word payload size uses the tagged width. *)
  Parameter psize_width : forall w a, psize w a = Pos.to_nat w.
End SIGN_TIME.

Module Type SIGN_T (L : WORD_LANGUAGE_T) := SIGN L <+ SIGN_TIME L.

Module Type SIGN_PLAN (L : WORD_LANGUAGE_T) (Import S : SIGN_T L).
  Parameter k_sign : N.
  (** Payload concretization reads the sign flags. *)
  Parameter F1_gamma : forall w a z, pgamma w a z <-> sign_gamma w a z.
  (** Sign height is at most three. *)
  Parameter F2_level : forall a, sign_level a <= 3.
  (** Bitwise negation retains every normalized concrete result. *)
  Parameter F3_sign_not_sound : forall w a x, L.is_word w x -> pgamma w a x ->
    pgamma w (sign_not a) (L.wrap w (Z.lnot x)).
  (** Arithmetic negation retains every normalized concrete result. *)
  Parameter F4_sign_neg_sound : forall w a x, L.is_word w x -> pgamma w a x ->
    pgamma w (sign_neg a) (L.wrap w (- x)).
  (** Bitwise conjunction retains every normalized concrete result. *)
  Parameter F5_sign_and_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_and a b) (L.wrap w (Z.land x y)).
  (** Bitwise disjunction retains every normalized concrete result. *)
  Parameter F6_sign_or_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_or a b) (L.wrap w (Z.lor x y)).
  (** Bitwise exclusive disjunction retains every normalized concrete result. *)
  Parameter F7_sign_xor_sound : forall w a b x y,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    pgamma w (sign_xor a b) (L.wrap w (Z.lxor x y)).
  (** Flag inclusion takes a constant number of Boolean operations. *)
  Parameter T1_pleb : forall w a b, (T_pleb w a b <= k_sign)%N.
  (** Flag join takes a constant number of Boolean operations. *)
  Parameter T2_pjoin : forall w a b, (T_pjoin w a b <= k_sign)%N.
  (** Flag meet takes a constant number of Boolean operations. *)
  Parameter T3_pmeet : forall w a b, (T_pmeet w a b <= k_sign)%N.
End SIGN_PLAN.

Module Type SIGN_ALL (L : WORD_LANGUAGE_T) := SIGN_T L <+ SIGN_PLAN L.

Module Type SIGN_TABLE (L : WORD_LANGUAGE) (S : SIGN L) := WORD_TABLE L S.
Module Type SIGN_TABLE_TIME (L : WORD_LANGUAGE_T) (S : SIGN_T L)
    (Import T : SIGN_TABLE L S).
  Include WORD_TABLE_TIME L S T.
  Parameter c_sign_table : N.
  (** Sign table dispatch has the published constant entry bound. *)
  Parameter T_sign_entry_le : forall o rw xs, (T_wfwd o rw xs <= c_sign_table)%N.
End SIGN_TABLE_TIME.
Module Type SIGN_TABLE_T (L : WORD_LANGUAGE_T) (S : SIGN_T L) :=
  SIGN_TABLE L S <+ SIGN_TABLE_TIME L S.
