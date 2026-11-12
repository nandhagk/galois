(** * Congruence payload interfaces

    Congruences describe residue classes of normalized words.
    For example, modulus two and residue zero describe even words.
    Builds on: WordSig. *)

From Stdlib Require Import ZArith List.
From Argent Require Import Std BigO.
From Galois.Domains Require Import WordSig.

Inductive congr : Type :=
  | CBot
  | C (m r : Z).

Module Type CONGRUENCE_OPS (L : WORD_LANGUAGE_OPS).
  Include WORD_PAYLOAD_OPS L with Definition p := congr.
  Parameter congr_norm : positive -> congr -> congr.
  Parameter congr_neg : positive -> congr -> congr.
  Parameter congr_add congr_sub congr_mul congr_shl congr_urem :
    positive -> congr -> congr -> congr.
  Parameter congr_project : positive -> positive -> congr -> congr.
End CONGRUENCE_OPS.

Module Type CONGRUENCE_SPEC (L : WORD_LANGUAGE_OPS) (Import D : CONGRUENCE_OPS L).
  Definition congr_gamma (w : positive) (a : congr) (z : Z) : Prop :=
    match a with
    | CBot => False
    | C m r => (0 <= z < 2 ^ Zpos w)%Z /\ (m | z - r)%Z
    end.
  Definition canonical (w : positive) (a : congr) : Prop :=
    match a with
    | CBot => True
    | C m r => (m = 0 /\ 0 <= r < 2 ^ Zpos w)%Z \/ (0 < m /\ 0 <= r < m)%Z
    end.
  Definition modulus_divides (w : positive) (a : congr) : Prop :=
    match a with CBot => True | C m _ => m = 0%Z \/ (m | 2 ^ Zpos w)%Z end.
  Definition congr_wrank (w : positive) (a : congr) : nat :=
    match a with
    | CBot => 0
    | C m _ => Pos.to_nat w + 2 - Z.to_nat (Z.log2 m)
    end.
End CONGRUENCE_SPEC.

Module Type CONGRUENCE (L : WORD_LANGUAGE) :=
  CONGRUENCE_OPS L <+ CONGRUENCE_SPEC L <+ WORD_PAYLOAD_LAWS L.

Module Type CONGRUENCE_TIME (L : WORD_LANGUAGE_T) (Import D : CONGRUENCE L).
  Include WORD_PAYLOAD_TIME L D.
  Parameter T_congr_norm T_congr_neg : positive -> congr -> nat.
  Parameter T_congr_add T_congr_sub T_congr_mul T_congr_shl T_congr_urem :
    positive -> congr -> congr -> nat.
  Parameter T_congr_project : positive -> positive -> congr -> nat.
  Parameter c_congruence : nat.
  (** Payload size uses the tagged width. *)
  Parameter psize_width : forall w a, psize w a = Pos.to_nat w.
  (** Normalization has the published quadratic arithmetic bound. *)
  Parameter T_congr_norm_le : forall w a,
    T_congr_norm w a <= c_congruence * (Pos.to_nat w + 1) ^ 2.
  (** Negation has the published quadratic arithmetic bound. *)
  Parameter T_congr_neg_le : forall w a,
    T_congr_neg w a <= c_congruence * (Pos.to_nat w + 1) ^ 2.
  (** Addition has the published quadratic arithmetic bound. *)
  Parameter T_congr_add_le : forall w a b,
    T_congr_add w a b <= c_congruence * (Pos.to_nat w + 1) ^ 2.
  (** Subtraction has the published quadratic arithmetic bound. *)
  Parameter T_congr_sub_le : forall w a b,
    T_congr_sub w a b <= c_congruence * (Pos.to_nat w + 1) ^ 2.
  (** Multiplication has the published quadratic arithmetic bound. *)
  Parameter T_congr_mul_le : forall w a b,
    T_congr_mul w a b <= c_congruence * (Pos.to_nat w + 1) ^ 2.
  (** Shift transfer has the published quadratic arithmetic bound. *)
  Parameter T_congr_shl_le : forall w a b,
    T_congr_shl w a b <= c_congruence * (Pos.to_nat w + 1) ^ 2.
  (** Remainder transfer has the published quadratic arithmetic bound. *)
  Parameter T_congr_urem_le : forall w a b,
    T_congr_urem w a b <= c_congruence * (Pos.to_nat w + 1) ^ 2.
  (** Projection charges both source and target widths. *)
  Parameter T_congr_project_le : forall source target a,
    T_congr_project source target a <=
    c_congruence * (Pos.to_nat source + Pos.to_nat target + 1) ^ 2.
  (** Congruence multiplication has the published quadratic width bound. *)
  Parameter mul_bigO : bigO (fun _ => True)
    (fun x : positive * (congr * congr) => (Pos.to_nat (fst x) + 1) ^ 2)
    (fun x => T_congr_mul (fst x) (fst (snd x)) (snd (snd x))).
End CONGRUENCE_TIME.

Module Type CONGRUENCE_T (L : WORD_LANGUAGE_T) :=
  CONGRUENCE L <+ CONGRUENCE_TIME L.

Module Type CONGRUENCE_PLAN (L : WORD_LANGUAGE_T) (Import D : CONGRUENCE_T L).
  Parameter k_congr_gcd k_congr_crt k_congr_transfer : nat.
  (** Payload concretization agrees with residue-class membership. *)
  Parameter F1_gamma : forall w a z, pgamma w a z <-> congr_gamma w a z.
  (** Normalization keeps precisely the same represented integers. *)
  Parameter F2_norm_gamma : forall w a z,
    pgamma w (congr_norm w a) z <-> pgamma w a z.
  (** Normalization produces a canonical representation. *)
  Parameter F3_norm_canonical : forall w a, canonical w (congr_norm w a).
  (** Normalization is idempotent. *)
  Parameter F4_norm_idempotent : forall w a,
    congr_norm w (congr_norm w a) = congr_norm w a.
  (** Chinese remainder meet retains each shared integer. *)
  Parameter F5_crt_meet_sound : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  (** Negation retains wrapped concrete negation. *)
  Parameter F6_congr_neg_sound : forall w a x,
    pgamma w a x -> pgamma w (congr_neg w a) (L.wrap w (- x)).
  (** Addition retains wrapped concrete addition. *)
  Parameter F7_congr_add_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_add w a b) (L.wrap w (x + y)).
  (** Subtraction retains wrapped concrete subtraction. *)
  Parameter F8_congr_sub_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_sub w a b) (L.wrap w (x - y)).
  (** Multiplication retains wrapped concrete multiplication. *)
  Parameter F9_congr_mul_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_mul w a b) (L.wrap w (x * y)).
  (** Projection retains truncations to smaller widths. *)
  Parameter F10_congr_project_sound : forall source target a x,
    (target <= source)%positive -> pgamma source a x ->
    pgamma target (congr_project source target a) (L.wrap target x).
  (** Shift transfer retains the wrapped concrete shift. *)
  Parameter F11_congr_shl_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y ->
    pgamma w (congr_shl w a b) (L.wrap w (Z.shiftl x y)).
  (** Remainder transfer retains every defined unsigned remainder. *)
  Parameter F12_congr_urem_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> y <> 0%Z ->
    pgamma w (congr_urem w a b) (L.wrap w (Z.modulo x y)).
  (** The requested congruence rank is bounded by width plus two. *)
  Parameter F13_wrank_le : forall w a, congr_wrank w a <= Pos.to_nat w + 2.
  (** Gcd-based joining has the published quadratic arithmetic bound. *)
  Parameter T1_join : forall w a b,
    T_pjoin w a b <= k_congr_gcd * (Pos.to_nat w + 1) ^ 2.
  (** Chinese remainder meet has the published quadratic arithmetic bound. *)
  Parameter T2_meet : forall w a b,
    T_pmeet w a b <= k_congr_crt * (Pos.to_nat w + 1) ^ 2.
End CONGRUENCE_PLAN.

Module Type CONGRUENCE_ALL (L : WORD_LANGUAGE_T) :=
  CONGRUENCE_T L <+ CONGRUENCE_PLAN L.

Module Type CONGRUENCE_TABLE (L : WORD_LANGUAGE) (D : CONGRUENCE L) := WORD_TABLE L D.
Module Type CONGRUENCE_TABLE_T (L : WORD_LANGUAGE_T) (D : CONGRUENCE_T L) := WORD_TABLE_T L D.
