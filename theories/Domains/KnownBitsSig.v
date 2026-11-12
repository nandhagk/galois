(** * Known-bit payload interfaces

    Two masks record known zero and one bits, including contradictory bottom facts.
    For example, Tnum 1 0 requires a clear low bit.
    Builds on: WordSig and the bit-vector word operations. *)

From Stdlib Require Import ZArith List Bool.
From Argent Require Import Time Std BigO.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import WordSig.
Local Open Scope nat_scope.

Record tnum : Type := Tnum {
  zeros : Z;
  ones : Z
}.

TimeFun zeros.
TimeFun ones.

Inductive mulchoice : Type :=
  | MulLow
  | MulStages
  | MulAcc
  | MulBoth.

Definition tnum_wrap (w : positive) (z : Z) : Z := Z.land z (Z.ones (Zpos w)).
TimeFun tnum_wrap.

Module Type TNUM_CONFIG.
  Parameter multiplier : mulchoice.
End TNUM_CONFIG.

(** Raw masks contribute their stored bit lengths to arithmetic work. *)
Definition tnum_bits (a : tnum) : nat := Z.size_nat (zeros a) + Z.size_nat (ones a).

Module Type KNOWN_BITS_OPS (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG).
  Include WORD_PAYLOAD_OPS L with Definition p := tnum with Definition pwparam := unit.
  Parameter tnum_normalise tnum_not tnum_neg : positive -> tnum -> tnum.
  Parameter tnum_add tnum_sub tnum_and tnum_or tnum_xor tnum_mul :
    positive -> tnum -> tnum -> tnum.
  Parameter tnum_mul_with : mulchoice -> positive -> tnum -> tnum -> tnum.
  Parameter tnum_variable : Op.op -> positive -> tnum -> tnum -> tnum.
End KNOWN_BITS_OPS.

Module Type KNOWN_BITS_SPEC (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG)
    (Import K : KNOWN_BITS_OPS L C).
  Definition tnum_gamma (w : positive) (a : tnum) (z : Z) : Prop :=
    Z.land z (L.wrap w (zeros a)) = 0%Z /\
    Z.land (L.wrap w (ones a)) (Z.lnot z) = 0%Z.
  Definition consistent (w : positive) (a : tnum) : Prop :=
    Z.land (L.wrap w (zeros a)) (L.wrap w (ones a)) = 0%Z.
  Definition known_count (w : positive) (a : tnum) : nat :=
    length (filter (fun i => Z.testbit (Z.lor (zeros a) (ones a)) (Z.of_nat i))
      (seq 0 (Pos.to_nat w))).
End KNOWN_BITS_SPEC.

Module Type KNOWN_BITS_CORE (L : WORD_LANGUAGE) (C : TNUM_CONFIG) :=
  KNOWN_BITS_OPS L C <+ KNOWN_BITS_SPEC L C <+ WORD_PAYLOAD_LAWS L.

Module Type KNOWN_BITS_LAWS (L : WORD_LANGUAGE) (C : TNUM_CONFIG)
    (Import K : KNOWN_BITS_CORE L C).
  (** Widening keeps an already contained raw mask and otherwise joins. *)
  Parameter F_pwiden : forall q w a b,
    pwiden q w a b = if pleb w b a then a else pjoin w a b.
  (** Multiplication uses the fixed configuration of the extracted program. *)
  Parameter multiplier_selected : forall w a b,
    tnum_mul w a b = tnum_mul_with C.multiplier w a b.
  (** Payload concretization is the zero-mask and one-mask meaning. *)
  Parameter gamma_tnum : forall w a z, pgamma w a z <-> tnum_gamma w a z.
  (** Bitwise negation retains each concrete result. *)
  Parameter tnum_not_sound : forall w a x z, L.is_word w x -> pgamma w a x ->
    L.eval_op Op.bvnot ((w, x) :: nil) = Some (w, z) -> pgamma w (tnum_not w a) z.
  (** Arithmetic negation retains each concrete result. *)
  Parameter tnum_neg_sound : forall w a x z, L.is_word w x -> pgamma w a x ->
    L.eval_op Op.bvneg ((w, x) :: nil) = Some (w, z) -> pgamma w (tnum_neg w a) z.
  (** Addition retains each concrete result. *)
  Parameter tnum_add_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvadd ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_add w a b) z.
  (** Subtraction retains each concrete result. *)
  Parameter tnum_sub_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvsub ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_sub w a b) z.
  (** Conjunction retains each concrete result. *)
  Parameter tnum_and_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvand ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_and w a b) z.
  (** Disjunction retains each concrete result. *)
  Parameter tnum_or_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvor ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_or w a b) z.
  (** Exclusive disjunction retains each concrete result. *)
  Parameter tnum_xor_sound : forall w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvxor ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_xor w a b) z.
  (** Every multiplier choice retains each concrete product. *)
  Parameter tnum_mul_with_sound : forall choice w a b x y z,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op Op.bvmul ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_mul_with choice w a b) z.
  (** An unknown shift or rotation retains each concrete result. *)
  Parameter tnum_variable_sound : forall o w a b x y z,
    In o (Op.bvshl :: Op.bvlshr :: Op.bvashr :: Op.bvrotl :: Op.bvrotr :: nil) ->
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    L.eval_op o ((w, x) :: (w, y) :: nil) = Some (w, z) ->
    pgamma w (tnum_variable o w a b) z.
End KNOWN_BITS_LAWS.

Module Type KNOWN_BITS (L : WORD_LANGUAGE) (C : TNUM_CONFIG) :=
  KNOWN_BITS_CORE L C <+ KNOWN_BITS_LAWS L C.


Module Type KNOWN_BITS_TIME (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG)
    (Import K : KNOWN_BITS L C).
  Include WORD_PAYLOAD_TIME L K.
  Parameter T_tnum_normalise T_tnum_not T_tnum_neg : positive -> tnum -> N.
  Parameter T_tnum_add T_tnum_sub T_tnum_and T_tnum_or T_tnum_xor T_tnum_mul :
    positive -> tnum -> tnum -> N.
  Parameter T_tnum_mul_with : mulchoice -> positive -> tnum -> tnum -> N.
  Parameter T_tnum_variable : Op.op -> positive -> tnum -> tnum -> N.
  Parameter c_tnum : N.
  (** Normalization charges the width and the raw masks. *)
  Parameter T_tnum_normalise_le : forall w a, (T_tnum_normalise w a <=
    c_tnum * N.of_nat ((Pos.to_nat w + tnum_bits a + 1) ^ 2))%N.
  (** Bitwise negation charges the width and the raw masks. *)
  Parameter T_tnum_not_le : forall w a, (T_tnum_not w a <=
    c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
  (** Arithmetic negation charges the width and the raw masks. *)
  Parameter T_tnum_neg_le : forall w a, (T_tnum_neg w a <=
    c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + 1))%N.
  (** Addition charges the width and both raw masks linearly. *)
  Parameter T_tnum_add_le : forall w a b, (T_tnum_add w a b <=
    c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  (** Subtraction charges the width and both raw masks linearly. *)
  Parameter T_tnum_sub_le : forall w a b, (T_tnum_sub w a b <=
    c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  (** Conjunction charges the width and both raw masks linearly. *)
  Parameter T_tnum_and_le : forall w a b, (T_tnum_and w a b <=
    c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  (** Disjunction charges the width and both raw masks linearly. *)
  Parameter T_tnum_or_le : forall w a b, (T_tnum_or w a b <=
    c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  (** Exclusive disjunction charges the width and both raw masks linearly. *)
  Parameter T_tnum_xor_le : forall w a b, (T_tnum_xor w a b <=
    c_tnum * N.of_nat (Pos.to_nat w + tnum_bits a + tnum_bits b + 1))%N.
  (** Every multiplier choice uses at most width-many linear-width stages. *)
  Parameter T_tnum_mul_with_le : forall choice w a b, (T_tnum_mul_with choice w a b <=
    c_tnum * N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
  (** Configured multiplication has the same quadratic width budget. *)
  Parameter T_tnum_mul_le : forall w a b, (T_tnum_mul w a b <=
    c_tnum * N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
  (** Unknown shifts and rotations enumerate at most width-many stages. *)
  Parameter T_tnum_variable_le : forall o w a b, (T_tnum_variable o w a b <=
    c_tnum * N.of_nat ((Pos.to_nat w + 1) ^ 2 + tnum_bits a + tnum_bits b))%N.
  (** Configured multiplication has quadratic asymptotic width work. *)
  Parameter mul_bigO : bigO (fun _ => True)
    (fun x : positive * (tnum * tnum) => N.of_nat ((Pos.to_nat (fst x) + 1) ^ 2 +
      tnum_bits (fst (snd x)) + tnum_bits (snd (snd x))))
    (fun x => T_tnum_mul (fst x) (fst (snd x)) (snd (snd x))).
  (** Payload size includes the width and the stored mask bits. *)
  Parameter psize_bits : forall w a, psize w a = Pos.to_nat w + tnum_bits a + 1.
  (** Every unary operation returns masks within the width. *)
  Parameter tnum_unary_bits : forall w a,
    tnum_bits (tnum_not w a) <= 2 * Pos.to_nat w /\
    tnum_bits (tnum_neg w a) <= 2 * Pos.to_nat w /\
    tnum_bits (tnum_normalise w a) <= 2 * Pos.to_nat w.
  (** Every binary operation returns masks within the width. *)
  Parameter tnum_binary_bits : forall w a b,
    tnum_bits (tnum_add w a b) <= 2 * Pos.to_nat w /\
    tnum_bits (tnum_sub w a b) <= 2 * Pos.to_nat w /\
    tnum_bits (tnum_and w a b) <= 2 * Pos.to_nat w /\
    tnum_bits (tnum_or w a b) <= 2 * Pos.to_nat w /\
    tnum_bits (tnum_xor w a b) <= 2 * Pos.to_nat w /\
    tnum_bits (tnum_mul w a b) <= 2 * Pos.to_nat w.
  (** Each multiplier choice and each unknown shift returns masks within the width. *)
  Parameter tnum_stage_bits : forall choice o w a b,
    tnum_bits (tnum_mul_with choice w a b) <= 2 * Pos.to_nat w /\
    tnum_bits (tnum_variable o w a b) <= 2 * Pos.to_nat w.
End KNOWN_BITS_TIME.

Module Type KNOWN_BITS_T (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG) :=
  KNOWN_BITS L C <+ KNOWN_BITS_TIME L C.

Module Type KNOWN_BITS_PLAN (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG)
    (Import K : KNOWN_BITS_T L C).
  Parameter mul_step : positive -> tnum -> tnum -> Z * tnum -> (Z * tnum) + tnum.
  Parameter T_mul_step : positive -> tnum -> tnum -> Z * tnum -> N.
  Parameter acc_step : positive -> tnum -> tnum -> Z * tnum -> (Z * tnum) + tnum.
  Parameter T_acc_step : positive -> tnum -> tnum -> Z * tnum -> N.
  Parameter k_mul_step : N.
  (** The mask agrees with the modular word reduction. *)
  Parameter F0_tnum_wrap : forall w z, tnum_wrap w z = L.wrap w z.
  (** Remaining widening credit counts known positions at nonbottoms. *)
  Parameter F3_rank : forall q w a, pis_bot w a = false -> pwrank q w a = known_count w a.
  (** At most one fact per position contributes nonbottom widening credit. *)
  Parameter F4_rank_bound : forall q w a, pis_bot w a = false -> pwrank q w a <= Pos.to_nat w.
  (** The stage invariant relates an accumulated prefix to its remaining product. *)
  Parameter F7_mul_step : forall w a b x y i r,
    L.is_word w x -> L.is_word w y -> pgamma w a x -> pgamma w b y ->
    (0 <= i < Zpos w)%Z -> pgamma w r (L.wrap w (x * (y mod 2 ^ i))) ->
    match mul_step w a b (i, r) with
    | inl (j, s) => j = (i + 1)%Z /\ pgamma w s (L.wrap w (x * (y mod 2 ^ j)))
    | inr s => pgamma w s (L.wrap w (x * y))
    end.
  (** A stage step keeps its accumulator within the width. *)
  Parameter F8_mul_step_bits : forall w a b i r j s,
    mul_step w a b (i, r) = inl (j, s) -> tnum_bits s <= 2 * Pos.to_nat w.
  (** An accumulating step keeps its accumulator within the width. *)
  Parameter F9_acc_step_bits : forall w a b i r j s,
    acc_step w a b (i, r) = inl (j, s) -> tnum_bits s <= 2 * Pos.to_nat w.
  (** The mask reads the width once and the raw integer once. *)
  Parameter T0_tnum_wrap : forall w z,
    (T_tnum_wrap w z <= k_mul_step * N.of_nat (Pos.to_nat w + Z.size_nat z + 1))%N.
  (** One staged product step charges its index, accumulator and raw masks. *)
  Parameter T1_mul_step : forall w a b i r, (T_mul_step w a b (i, r) <= k_mul_step *
    N.of_nat (Pos.to_nat w + Z.size_nat i + tnum_bits a + tnum_bits b + tnum_bits r + 1))%N.
  (** One accumulating step charges the width, its index and its accumulator. *)
  Parameter T2_acc_step : forall w a b i r, (T_acc_step w a b (i, r) <= k_mul_step *
    N.of_nat (Pos.to_nat w + Z.size_nat i + tnum_bits a + tnum_bits b + tnum_bits r + 1))%N.
End KNOWN_BITS_PLAN.

Module Type KNOWN_BITS_ALL (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG) :=
  KNOWN_BITS_T L C <+ KNOWN_BITS_PLAN L C.

Module Type KNOWN_BITS_TABLE (L : WORD_LANGUAGE) (C : TNUM_CONFIG)
    (K : KNOWN_BITS L C) := WORD_TABLE L K.
Module Type KNOWN_BITS_TABLE_T (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG)
    (K : KNOWN_BITS_T L C) := WORD_TABLE_T L K.
