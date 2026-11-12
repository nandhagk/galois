(** * Circular interval payload interfaces

    Circular intervals describe inclusive arcs across the unsigned and signed poles.
    For example, the eight-bit arc from 250 to 3 contains zero.
    Builds on: WordSig and the bit-vector word operations. *)

From Stdlib Require Import ZArith List.
From Argent Require Import Time Std BigO.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import WordSig.

Local Open Scope nat_scope.

Inductive wrapped : Type :=
  | WBot
  | WFull
  | WItv (lo hi : Z).

(** Arc storage charges the raw endpoint bit lengths. *)
Definition wrapped_bits (a : wrapped) : nat :=
  match a with
  | WBot | WFull => 0
  | WItv lo hi => Z.size_nat lo + Z.size_nat hi
  end.

Module Type WRAPPED_OPS (L : WORD_LANGUAGE_OPS).
  Include WORD_PAYLOAD_OPS L with Definition p := wrapped with Definition pwparam := unit.
  Parameter wrapped_norm wrapped_double wrapped_neg wrapped_not : positive -> wrapped -> wrapped.
  Parameter wrapped_add wrapped_sub wrapped_mul wrapped_udiv wrapped_urem :
    positive -> wrapped -> wrapped -> wrapped.
  Parameter wrapped_split : positive -> wrapped -> list (Z * Z).
End WRAPPED_OPS.

Module Type WRAPPED_SPEC (L : WORD_LANGUAGE_OPS) (Import W : WRAPPED_OPS L).
  Definition offset (w : positive) (origin x : Z) : Z := ((x - origin) mod Word.modulus w)%Z.
  Definition card (w : positive) (a : wrapped) : Z :=
    match a with
    | WBot => 0%Z
    | WFull => Word.modulus w
    | WItv lo hi => (offset w lo hi + 1)%Z
    end.
  Definition arc_gamma (w : positive) (a : wrapped) (z : Z) : Prop :=
    match a with
    | WBot => False
    | WFull => Word.is_word w z
    | WItv lo hi => Word.is_word w z /\ (offset w lo z <= offset w lo hi)%Z
    end.
  Definition size_rank (w : positive) (n : Z) : nat :=
    Z.to_nat (if (n =? 0)%Z then (Zpos w + 2)%Z else
      if (n =? Word.modulus w)%Z then 0%Z else (Zpos w + 1 - Z.log2 n)%Z).
End WRAPPED_SPEC.

Module Type WRAPPED_CORE (L : WORD_LANGUAGE) :=
  WRAPPED_OPS L <+ WRAPPED_SPEC L <+ WORD_PAYLOAD_LAWS L.

Module Type WRAPPED_LAWS (L : WORD_LANGUAGE) (Import W : WRAPPED_CORE L).
  (** Payload concretization is clockwise arc membership. *)
  Parameter gamma_arc : forall w a z, pgamma w a z <-> arc_gamma w a z.
  (** Arithmetic negation retains each concrete result. *)
  Parameter wrapped_neg_sound : forall w a x z, L.is_word w x -> pgamma w a x ->
    L.eval_op Op.bvneg ((w, x) :: nil) = Some (w, z) -> pgamma w (wrapped_neg w a) z.
  (** Addition retains each concrete result. *)
  Parameter wrapped_add_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvadd ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (wrapped_add w a b) z.
  (** Subtraction retains each concrete result. *)
  Parameter wrapped_sub_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvsub ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (wrapped_sub w a b) z.
  (** Multiplication retains each concrete result. *)
  Parameter wrapped_mul_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvmul ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (wrapped_mul w a b) z.
End WRAPPED_LAWS.

Module Type WRAPPED (L : WORD_LANGUAGE) := WRAPPED_CORE L <+ WRAPPED_LAWS L.


Module Type WRAPPED_TIME (L : WORD_LANGUAGE_T) (Import W : WRAPPED L).
  Include WORD_PAYLOAD_TIME L W.
  Parameter T_wrapped_norm T_wrapped_double T_wrapped_neg T_wrapped_not :
    positive -> wrapped -> N.
  Parameter T_wrapped_add T_wrapped_sub T_wrapped_mul T_wrapped_udiv T_wrapped_urem :
    positive -> wrapped -> wrapped -> N.
  Parameter T_wrapped_split : positive -> wrapped -> N.
  Parameter c_wrapped : N.
  (** Normalization charges the raw endpoints and the output width. *)
  Parameter T_wrapped_norm_le : forall w a, (T_wrapped_norm w a <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  (** Circular expansion charges normalized endpoint arithmetic. *)
  Parameter T_wrapped_double_le : forall w a, (T_wrapped_double w a <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  (** Arithmetic negation charges normalized endpoint arithmetic. *)
  Parameter T_wrapped_neg_le : forall w a, (T_wrapped_neg w a <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  (** Bitwise negation charges normalized endpoint arithmetic. *)
  Parameter T_wrapped_not_le : forall w a, (T_wrapped_not w a <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  (** Circular multiplication charges quadratic width arithmetic and raw endpoints. *)
  Parameter T_wrapped_mul_le : forall w a b, (T_wrapped_mul w a b <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  (** Circular addition charges its two raw arcs and output width. *)
  Parameter T_wrapped_add_le : forall w a b, (T_wrapped_add w a b <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  (** Circular subtraction charges its two raw arcs and output width. *)
  Parameter T_wrapped_sub_le : forall w a b, (T_wrapped_sub w a b <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  (** Splitting charges endpoint normalization at both poles. *)
  Parameter T_wrapped_split_le : forall w a, (T_wrapped_split w a <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a))%N.
  (** Unsigned division charges quadratic width arithmetic. *)
  Parameter T_wrapped_udiv_le : forall w a b, (T_wrapped_udiv w a b <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  (** Unsigned remainder charges quadratic width arithmetic. *)
  Parameter T_wrapped_urem_le : forall w a b, (T_wrapped_urem w a b <=
    c_wrapped * N.of_nat ((Pos.to_nat w + 1) ^ 2 + wrapped_bits a + wrapped_bits b))%N.
  (** Circular multiplication has the published quadratic asymptotic work. *)
  Parameter mul_bigO : bigO (fun _ => True)
    (fun x : positive * (wrapped * wrapped) => N.of_nat
      ((Pos.to_nat (fst x) + 1) ^ 2 +
       wrapped_bits (fst (snd x)) + wrapped_bits (snd (snd x))))
    (fun x => T_wrapped_mul (fst x) (fst (snd x)) (snd (snd x))).
  (** Arc payload size charges width and raw endpoint storage. *)
  Parameter psize_bits : forall w a, psize w a = Pos.to_nat w + wrapped_bits a + 1.
  (** Every arithmetic result the table reads has endpoints within the width. *)
  Parameter wrapped_result_bits : forall w a b,
    wrapped_bits (wrapped_add w a b) <= 2 * Pos.to_nat w /\
    wrapped_bits (wrapped_sub w a b) <= 2 * Pos.to_nat w /\
    wrapped_bits (wrapped_mul w a b) <= 2 * Pos.to_nat w /\
    wrapped_bits (wrapped_neg w a) <= 2 * Pos.to_nat w.
  (** Split pieces have endpoints within the width. *)
  Parameter wrapped_split_bits : forall w a lo hi, In (lo, hi) (wrapped_split w a) ->
    Z.size_nat lo + Z.size_nat hi <= 2 * Pos.to_nat w.
End WRAPPED_TIME.

Module Type WRAPPED_T (L : WORD_LANGUAGE_T) := WRAPPED L <+ WRAPPED_TIME L.

Module Type WRAPPED_PLAN (L : WORD_LANGUAGE_T) (Import W : WRAPPED_T L).
  Parameter mul_piece : positive -> (Z * Z) -> (Z * Z) -> wrapped.
  Parameter T_mul_piece : positive -> (Z * Z) -> (Z * Z) -> N.
  Parameter k_split k_mul_piece : N.
  (** Cardinality lies between zero and the word modulus. *)
  Parameter F2_card : forall w a, (0 <= card w a <= Word.modulus w)%Z.
  (** Pole splitting produces at most four pieces. *)
  Parameter F3_split_len : forall w a, length (wrapped_split w a) <= 4.
  (** Every arc member belongs to one ordinary split interval. *)
  Parameter F4_split_covers : forall w a z, pgamma w a z ->
    exists lo hi, In (lo, hi) (wrapped_split w a) /\ (lo <= z <= hi)%Z.
  (** Multiplication pieces retain each pair of represented endpoints. *)
  Parameter F5_mul_piece : forall w lo hi lo' hi' x y,
    (lo <= x <= hi)%Z -> (lo' <= y <= hi')%Z ->
    pgamma w (mul_piece w (lo, hi) (lo', hi')) (L.wrap w (x * y)).
  (** Widening retains a contained candidate and otherwise expands the old arc first. *)
  Parameter F7_widen : forall q w a b, pwiden q w a b =
    if pleb w b a then a else pjoin w (wrapped_double w a) b.
  (** Expansion triples cardinality until the circle is full. *)
  Parameter F8_double_card : forall w a,
    card w (wrapped_double w a) = Z.min (Word.modulus w) (3 * card w a)%Z.
  (** Expansion contains the old arc. *)
  Parameter F8a_double_contains : forall w a, pleb w a (wrapped_double w a) = true.
  (** Cardinality is monotone in the payload order. *)
  Parameter F8b_card_mono : forall w a b, pleb w a b = true -> (card w a <= card w b)%Z.
  (** Rank gives full circles zero credit and bottom width plus two credits. *)
  Parameter F9_rank : forall q w a, pwrank q w a = size_rank w (card w a).
  (** The logarithmic credit is bounded by width plus two. *)
  Parameter F10_rank_bound : forall q w a, pwrank q w a <= Pos.to_nat w + 2.
  (** Each multiplication piece has a quadratic endpoint budget. *)
  Parameter T1_mul_piece : forall w lo hi lo' hi',
    (T_mul_piece w (lo, hi) (lo', hi') <= k_mul_piece * N.of_nat
      ((Pos.to_nat w + Z.size_nat lo + Z.size_nat hi + Z.size_nat lo' + Z.size_nat hi' + 1)
        ^ 2))%N.
End WRAPPED_PLAN.

Module Type WRAPPED_ALL (L : WORD_LANGUAGE_T) := WRAPPED_T L <+ WRAPPED_PLAN L.
Module Type WRAPPED_TABLE (L : WORD_LANGUAGE) (W : WRAPPED L) := WORD_TABLE L W.
Module Type WRAPPED_TABLE_T (L : WORD_LANGUAGE_T) (W : WRAPPED_T L) := WORD_TABLE_T L W.
