(** * Fixed numeric helper bodies

    This file spells out the integer, word and known-bit helpers used by domain models.
    For example, a known-bit emptiness test executes both wrapped masks before comparing.
    Builds on: SignedOperand, the fixed vocabulary and DomainsKnownBits. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsKnownBits.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.

Definition domain_run (A : Type) : Type := A * audit_trace unit.

Definition domain_bind {A B} (first : domain_run A) (next : A -> domain_run B)
    : domain_run B :=
  let '(a, first_trace) := first in
  let '(b, next_trace) := next a in (b, first_trace ++ next_trace).

Notation "x <- first ;; next" := (domain_bind first (fun x => next))
  (at level 100, first at next level, right associativity).

Definition domain_return {A} (site : nat) (payload : list N) (value : A) : domain_run A :=
  (value, [AuditConstruct site payload]).

Definition domain_tell (events : audit_trace unit) : domain_run unit := (tt, events).

Definition domain_case {A} (site : nat) (payload : list N) (body : domain_run A)
    : domain_run A := (fst body, AuditCase site payload :: snd body).

(** Integer primitive identifiers fix their operation, with actual signed operands. *)
Inductive domain_zop : Type :=
  | DzAdd
  | DzSub
  | DzMul
  | DzDiv
  | DzMod
  | DzAnd
  | DzOr
  | DzXor
  | DzMin
  | DzMax
  | DzPow.

Definition domain_zop_site (op : domain_zop) : nat :=
  match op with
  | DzAdd => 200 | DzSub => 201 | DzMul => 202 | DzDiv => 203 | DzMod => 204
  | DzAnd => 205 | DzOr => 206 | DzXor => 207 | DzMin => 208 | DzMax => 209
  | DzPow => 210
  end%nat.

Definition domain_z (op : domain_zop) (a b : Z) : domain_run Z :=
  let out := match op with
    | DzAdd => (a + b)%Z | DzSub => (a - b)%Z | DzMul => (a * b)%Z
    | DzDiv => (a / b)%Z | DzMod => (a mod b)%Z | DzAnd => Z.land a b
    | DzOr => Z.lor a b | DzXor => Z.lxor a b | DzMin => Z.min a b
    | DzMax => Z.max a b | DzPow => (a ^ b)%Z
    end in
  (out, [scalar_z (domain_zop_site op) a b]).

Definition domain_not (a : Z) : domain_run Z :=
  (Z.lnot a, [AuditArithmetic 211 [count_zencode a]]).

Definition domain_compare (strict : bool) (a b : Z) : domain_run bool :=
  (if strict then (a <? b)%Z else (a <=? b)%Z,
    [scalar_z (if strict then 212 else 213)%nat a b]).

Definition domain_equal (a b : Z) : domain_run bool :=
  ((a =? b)%Z, [scalar_z 214 a b]).

Definition domain_testbit (a index : Z) : domain_run bool :=
  (Z.testbit a index, [scalar_z 215 a index]).

Definition domain_b2z (b : bool) : domain_run Z :=
  (Z.b2z b, [AuditCase 223 [if b then 1%N else 0%N]]).

Definition domain_modulus (w : width) : domain_run Z := domain_z DzPow 2 (Z.pos w).

Definition domain_wrap (w : width) (a : Z) : domain_run Z :=
  m <- domain_modulus w ;; domain_z DzMod a m.

Definition domain_wnot (w : width) (a : Z) : domain_run Z :=
  m <- domain_modulus w ;;
  upper <- domain_z DzSub m 1 ;;
  value <- domain_wrap w a ;; domain_z DzSub upper value.

Definition domain_word_bits (op : domain_zop) (w : width) (a b : Z) : domain_run Z :=
  lhs <- domain_wrap w a ;;
  rhs <- domain_wrap w b ;; domain_z op lhs rhs.

Definition domain_zeros (a : tnum) : domain_run Z :=
  (zeros a, [AuditCase 216 [count_zencode (zeros a)]]).

Definition domain_ones (a : tnum) : domain_run Z :=
  (ones a, [AuditCase 217 [count_zencode (ones a)]]).

Definition domain_tnum (z o : Z) : domain_run tnum :=
  domain_return 218 [count_zencode z; count_zencode o] (Tnum z o).

Definition domain_const (w : width) (a : Z) : domain_run tnum :=
  z <- domain_wnot w a ;;
  o <- domain_wrap w a ;; domain_tnum z o.

Definition domain_normalise (w : width) (a : tnum) : domain_run tnum :=
  za <- domain_zeros a ;;
  z <- domain_wrap w za ;;
  oa <- domain_ones a ;;
  o <- domain_wrap w oa ;; domain_tnum z o.

Definition domain_tnum_bits (op : domain_zop) (w : width) (a b : tnum)
    : domain_run tnum :=
  za <- domain_zeros a ;;
  zb <- domain_zeros b ;;
  z <- domain_word_bits op w za zb ;;
  oa <- domain_ones a ;;
  ob <- domain_ones b ;;
  o <- domain_word_bits op w oa ob ;; domain_tnum z o.

Definition domain_min (w : width) (a : tnum) : domain_run Z :=
  o <- domain_ones a ;; domain_wrap w o.

Definition domain_max (w : width) (a : tnum) : domain_run Z :=
  z <- domain_zeros a ;; domain_wnot w z.

Definition domain_mask (w : width) (a : tnum) : domain_run Z :=
  z <- domain_zeros a ;;
  o <- domain_ones a ;;
  combined <- domain_word_bits DzOr w z o ;; domain_wnot w combined.

Definition domain_empty (w : width) (a : tnum) : domain_run bool :=
  z <- domain_zeros a ;;
  o <- domain_ones a ;;
  overlap <- domain_word_bits DzAnd w z o ;;
  zero <- domain_equal overlap 0 ;;
  (negb zero, [AuditCase 219 [if zero then 1%N else 0%N]]).

Definition domain_bottom (w : width) : domain_run tnum :=
  m1 <- domain_modulus w ;;
  z <- domain_z DzSub m1 1 ;;
  m2 <- domain_modulus w ;;
  o <- domain_z DzSub m2 1 ;; domain_tnum z o.

Definition domain_subset (w : width) (a b : Z) : domain_run bool :=
  lhs <- domain_word_bits DzAnd w a b ;;
  rhs <- domain_wrap w a ;; domain_equal lhs rhs.

Definition domain_order (w : width) (a b : tnum) : domain_run bool :=
  zb <- domain_zeros b ;;
  za <- domain_zeros a ;;
  z <- domain_subset w zb za ;;
  ob <- domain_ones b ;;
  oa <- domain_ones a ;;
  o <- domain_subset w ob oa ;;
  (z && o, [AuditCase 220 [if z then 1%N else 0%N; if o then 1%N else 0%N]]).

(** Both carry streams and both unknown masks are evaluated in their literal source order. *)
Definition domain_uncertain (w : width) (a b : tnum) (initial : bool) : domain_run Z :=
  amin <- domain_min w a ;;
  bmin <- domain_min w b ;;
  sum_min <- domain_z DzAdd amin bmin ;;
  low_carry <- domain_b2z initial ;;
  low <- domain_z DzAdd sum_min low_carry ;;
  amax <- domain_max w a ;;
  bmax <- domain_max w b ;;
  sum_max <- domain_z DzAdd amax bmax ;;
  high_carry <- domain_b2z initial ;;
  high <- domain_z DzAdd sum_max high_carry ;;
  different <- domain_z DzXor low high ;;
  ma <- domain_mask w a ;;
  mb <- domain_mask w b ;;
  masks <- domain_z DzOr ma mb ;; domain_z DzOr different masks.

Definition domain_adc (w : width) (a b : tnum) (initial : bool) : domain_run tnum :=
  amin <- domain_min w a ;;
  bmin <- domain_min w b ;;
  sum <- domain_z DzAdd amin bmin ;;
  carry <- domain_b2z initial ;;
  value <- domain_z DzAdd sum carry ;;
  mask <- domain_uncertain w a b initial ;;
  either <- domain_z DzOr value mask ;;
  neg <- domain_not either ;;
  z <- domain_wrap w neg ;;
  nm <- domain_not mask ;;
  both <- domain_z DzAnd value nm ;;
  o <- domain_wrap w both ;; domain_tnum z o.

(** A word shift follows the actual cutoff, power, product and wrapping branches. *)
Definition domain_wshl (w : width) (a amount : Z) : domain_run Z :=
  first_amount <- domain_wrap w amount ;;
  oversized <- domain_compare false (Z.pos w) first_amount ;;
  domain_case 221 [if oversized then 1%N else 0%N]
    (if oversized then domain_return 222 [] 0%Z else
      x <- domain_wrap w a ;;
      second_amount <- domain_wrap w amount ;;
      power <- domain_z DzPow 2 second_amount ;;
      product <- domain_z DzMul x power ;; domain_wrap w product).

(** Mapping two endpoints retains the duplicated source evaluation of the shift function. *)
Definition domain_shift (w : width) (amount : Z) (a : tnum) : domain_run tnum :=
  first_max <- domain_max w a ;;
  first_amount <- domain_z DzMin amount (Z.pos w) ;;
  first <- domain_wshl w first_max first_amount ;;
  z <- domain_wnot w first ;;
  second_min <- domain_min w a ;;
  second_amount <- domain_z DzMin amount (Z.pos w) ;;
  second <- domain_wshl w second_min second_amount ;;
  o <- domain_wrap w second ;; domain_tnum z o.

(** Shared natural arithmetic sites have explicit prices, without importing scalar algorithms. *)
Definition domain_auxiliary_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditArithmetic site [a] =>
    if Nat.eqb site 0 || Nat.eqb site 1 then audit_binary_weight (Z.of_N a) 0%Z
    else if Nat.eqb site 7 || Nat.eqb site 64 then
      audit_unary_conversion_weight (audit_z_bits (Z.of_N a))
    else if Nat.eqb site 46 then audit_unary_conversion_weight (audit_z_bits(count_zdecode a))
    else if Nat.eqb site 41 || Nat.eqb site 43 then S(N.to_nat a) else 1%nat
  | AuditArithmetic site [a;b] =>
    if Nat.eqb site 3 then audit_multiply_weight (Z.of_N a)(Z.of_N b)
    else if Nat.eqb site 4 || Nat.eqb site 5 then audit_divide_weight (Z.of_N a)(Z.of_N b)
    else if Nat.eqb site 42 || Nat.eqb site 82 then audit_divide_weight(count_zdecode
      a)(count_zdecode b)
    else if Nat.eqb site 44 || Nat.eqb site 60 || Nat.eqb site 63 then
      audit_binary_weight(count_zdecode a)(count_zdecode b)
    else if Nat.eqb site 65 then audit_multiply_weight(count_zdecode a)(count_zdecode b)
    else if Nat.eqb site 45 then (S(N.to_nat a)+audit_divide_weight(count_zdecode b)(2^Z.of_N
      a))%nat
    else audit_binary_weight (Z.of_N a)(Z.of_N b)
  | _ => 1%nat end.

(** Primitive costs are fixed, positive, and retain numeric shift or exponent sizes. *)
Definition domain_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditArithmetic site [a; b] =>
    if Nat.eqb site 202 then audit_multiply_weight (count_zdecode a) (count_zdecode b)
    else if Nat.eqb site 203 || Nat.eqb site 204 then
      audit_divide_weight (count_zdecode a) (count_zdecode b)
    else if Nat.eqb site 210 then
      (1 + audit_z_bits (count_zdecode a) *
        S (Z.to_nat (Z.max 0 (count_zdecode b))))%nat
    else if (200 <=? site)%nat && (site <=? 215)%nat then
      audit_binary_weight (count_zdecode a) (count_zdecode b)
    else domain_auxiliary_frame_weight event
  | AuditArithmetic 211 [a] => S (audit_z_bits (count_zdecode a))
  | _ => domain_auxiliary_frame_weight event
  end.

Definition domain_work (events : audit_trace unit) : nat :=
  fold_right (fun event total => (domain_frame_weight event + total)%nat) 0%nat events.

(** Binary iteration executes both halves and retains every terminal source test. *)
Fixpoint domain_piter {A} (fuel : positive) (body : A -> domain_run A) (state : A)
    : domain_run A :=
  domain_case 224 [N.pos fuel]
    (match fuel with
    | xH => body state
    | xO p => mid <- domain_piter p body state ;; domain_piter p body mid
    | xI p => mid1 <- domain_piter p body state ;;
      mid2 <- domain_piter p body mid1 ;; body mid2
    end).

Definition domain_iter {A} (fuel : N) (body : A -> domain_run A) (state : A)
    : domain_run A :=
  domain_case 225 [fuel]
    (match fuel with
    | N0 => (state, [])
    | Npos p => domain_piter p body state
    end).

(** Helper erasure fixes concrete result identities before any whole-operation bound. *)
Definition domain_helpers_erases_type : Prop :=
  (forall w a, fst (domain_empty w a) = tnum_empty w a) /\
  (forall w a b initial, fst (domain_adc w a b initial) = tnum_adc w a b initial) /\
  (forall w amount a, fst (domain_shift w amount a) = tnum_scalar bvshl w amount a) /\
  (forall w a b, fst (domain_order w a b) = leb (tnum_lattice w) a b).

(** Every shared public helper names its exact existing result, independently of any cost bound. *)
Definition domain_helpers_full_erases_type : Prop :=
 (forall w, fst(domain_modulus w)=modulus w) /\
 (forall w z, fst(domain_wrap w z)=wrap w z) /\
 (forall w z, fst(domain_wnot w z)=wnot w z) /\
 (forall w z, fst(domain_const w z)=tnum_const w z) /\
 (forall w a, fst(domain_normalise w a)=tnum_normalise w a) /\
 (forall w a, fst(domain_min w a)=tnum_min w a) /\
 (forall w a, fst(domain_max w a)=tnum_max w a) /\
 (forall w a, fst(domain_mask w a)=tnum_mask w a) /\
 (forall w, fst(domain_bottom w)=bot(tnum_lattice w)) /\
 (forall w a b, fst(domain_tnum_bits DzAnd w a b)=tnum_join w a b) /\
 (forall w a b, fst(domain_tnum_bits DzOr w a b)=tnum_meet w a b) /\
 domain_helpers_erases_type.
