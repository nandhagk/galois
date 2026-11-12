(** * Range-based bit-vector safety checks

    Checks use unsigned and signed range queries to exclude concrete arithmetic errors.
    For example, a divisor range above zero excludes division by zero.
    Builds on: ChecksSig, BitsLang and ValueSig. *)

From Stdlib Require Import ZArith List Bool.
From Argent Require Import Time Std BigO.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig ValueSig BitsLang.
From Galois.Alarms Require Import ChecksSig.
Import List.ListNotations.

Local Open Scope nat_scope.

Inductive kind : Type :=
  | DivZero
  | Overflow (o : Op.op) (signed : bool)
  | Bounds
  | NullDeref.

Module NumU <: NUM_VIEW BitsLang.
  Definition num (c : word) : Z := snd c.
End NumU.

Module NumS <: NUM_VIEW BitsLang.
  Definition num (c : word) : Z := Word.signed (fst c) (snd c).
End NumS.

(** Finite range endpoints contribute their stored bit lengths. *)
Definition range_bits (r : bnd * bnd) : nat :=
  (match fst r with Fin z => Z.size_nat z | _ => 0 end) +
  (match snd r with Fin z => Z.size_nat z | _ => 0 end).

Module Type BITS_RANGE_OPS (V : VALUE_DOMAIN_OPS BitsLangCode).
  Parameter range : V.t -> bnd * bnd.
End BITS_RANGE_OPS.

Module Type BITS_RANGE_T (N : NUM_VIEW BitsLang) (V : VALUE_DOMAIN_T BitsLangT).
  Include RANGE_QUERY BitsLang N V.
  Parameter T_range : V.t -> N.
  Parameter c_range : N.
  (** A range query reads the queried value once. *)
  Parameter T_range_le : forall a, (T_range a <= c_range * N.of_nat (V.size a + 1))%N.
  (** Queried endpoints fit the size of the queried value. *)
  Parameter range_bits_le : forall a,
    (N.of_nat (range_bits (range a)) <= c_range * N.of_nat (V.size a + 1))%N.
End BITS_RANGE_T.

Module Type BITS_WIDTH_OPS (V : VALUE_DOMAIN_OPS BitsLangCode).
  Parameter width : V.t -> option positive.
End BITS_WIDTH_OPS.

Module Type BITS_WIDTH (V : VALUE_DOMAIN BitsLang).
  Include BITS_WIDTH_OPS V.
  (** A reported width is the width of every represented word. *)
  Parameter width_sound : forall a w c, width a = Some w -> V.gamma a c -> fst c = w.
End BITS_WIDTH.

Module Type BITS_WIDTH_T (V : VALUE_DOMAIN_T BitsLangT).
  Include BITS_WIDTH V.
  Parameter T_width : V.t -> N.
  Parameter c_width : N.
  (** The width query reads the queried value once. *)
  Parameter T_width_le : forall a, (T_width a <= c_width * N.of_nat (V.size a + 1))%N.
  (** A reported width fits the size of the queried value. *)
  Parameter width_size : forall a w, width a = Some w -> Pos.to_nat w <= V.size a.
End BITS_WIDTH_T.

(** Zero membership reads inclusive range endpoints. *)
Definition range_zero (r : bnd * bnd) : bool :=
  (match fst r with NegInf => true | Fin z => (z <=? 0)%Z | PosInf => false end) &&
  (match snd r with NegInf => false | Fin z => (0 <=? z)%Z | PosInf => true end).
TimeFun range_zero.

(** Strict endpoint comparison handles both infinities. *)
Definition bound_lt (a b : bnd) : bool :=
  match a, b with
  | NegInf, NegInf | PosInf, _ | _, NegInf => false
  | NegInf, _ | _, PosInf => true
  | Fin x, Fin y => (x <? y)%Z
  end.
TimeFun bound_lt.

(** A range is nonnegative when its lower endpoint proves nonnegativity. *)
Definition range_nonnegative (r : bnd * bnd) : bool :=
  match fst r with
  | NegInf => false
  | Fin z => (0 <=? z)%Z
  | PosInf => true
  end.
TimeFun range_nonnegative.

(** Endpoint arithmetic of the mathematical result over two finite ranges. *)
Definition range_result (o : Op.op) (x y : bnd * bnd) : option (Z * Z) :=
  match x, y with
  | (Fin a, Fin b), (Fin c, Fin d) =>
    match o with
    | bvadd => Some (a + c, b + d)%Z
    | bvsub => Some (a - d, b - c)%Z
    | bvmul => Some (Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d)),
        Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d)))%Z
    | _ => None
    end
  | _, _ => None
  end.
TimeFun range_result.

(** A result range fits the unsigned or signed view of its width. *)
Definition range_fits (s : bool) (w : positive) (r : Z * Z) : bool :=
  if s then (- Word.half w <=? fst r)%Z && (snd r <? Word.half w)%Z
  else (0 <=? fst r)%Z && (snd r <? Word.modulus w)%Z.
TimeFun range_fits.

Module Type BITS_CHECKS_OPS (V : VALUE_DOMAIN_OPS BitsLangCode)
    (Q QS : BITS_RANGE_OPS V) (W : BITS_WIDTH_OPS V).
  Include CHECKS_OPS BitsLangCode V with Definition kd := kind.
End BITS_CHECKS_OPS.

Module Type BITS_CHECKS_BASE (V : VALUE_DOMAIN BitsLang)
    (Q : RANGE_QUERY BitsLang NumU V) (QS : RANGE_QUERY BitsLang NumS V) (W : BITS_WIDTH V) :=
  BITS_CHECKS_OPS V Q QS W <+ CHECKS_LAWS BitsLang V.

Module Type BITS_CHECKS_LAWS (V : VALUE_DOMAIN BitsLang)
    (Q : RANGE_QUERY BitsLang NumU V) (QS : RANGE_QUERY BitsLang NumS V) (W : BITS_WIDTH V)
    (Import C : BITS_CHECKS_BASE V Q QS W).
  (* spec: mathematical_result *)
  Parameter mathematical_result : Op.op -> bool -> word -> word -> option Z.
  (** Division is safe exactly when its divisor is nonzero. *)
  Parameter safe_divzero : forall d, safe DivZero [d] <-> snd d <> 0%Z.
  (** Dereference is safe exactly when its pointer is nonzero. *)
  Parameter safe_null : forall p, safe NullDeref [p] <-> snd p <> 0%Z.
  (** Bounds safety uses a nonnegative index strictly below the concrete length. *)
  Parameter safe_bounds : forall i len, safe Bounds [i; len] <-> (0 <= snd i < snd len)%Z.
  (** Overflow safety compares the mathematical result with the operand width's view. *)
  Parameter safe_overflow : forall o s a b,
    safe (Overflow o s) [a; b] <-> fst a = fst b /\
      exists z, mathematical_result o s a b = Some z /\
      (if s then (- Word.half (fst a) <= z < Word.half (fst a))%Z
       else (0 <= z < Word.modulus (fst a))%Z).
  (** Mathematical addition uses the selected unsigned or signed operand view. *)
  Parameter result_add : forall s a b, mathematical_result bvadd s a b =
    Some ((if s then NumS.num a else NumU.num a) +
      (if s then NumS.num b else NumU.num b))%Z.
  (** Mathematical subtraction uses the selected operand view. *)
  Parameter result_sub : forall s a b, mathematical_result bvsub s a b =
    Some ((if s then NumS.num a else NumU.num a) -
      (if s then NumS.num b else NumU.num b))%Z.
  (** Mathematical multiplication uses the selected operand view. *)
  Parameter result_mul : forall s a b, mathematical_result bvmul s a b =
    Some ((if s then NumS.num a else NumU.num a) *
      (if s then NumS.num b else NumU.num b))%Z.
  (** A divisor may be zero exactly when its unsigned range includes zero. *)
  Parameter may_fail_divzero : forall d, may_fail DivZero [d] = range_zero (Q.range d).
  (** Null checking uses the same zero membership test. *)
  Parameter may_fail_null : forall p, may_fail NullDeref [p] = range_zero (Q.range p).
  (** Bounds checking compares the worst index with the least possible length. *)
  Parameter may_fail_bounds : forall i len, may_fail Bounds [i; len] =
    negb (range_nonnegative (Q.range i) && bound_lt (snd (Q.range i)) (fst (Q.range len))).
  (** Mathematical results exist only for addition, subtraction and multiplication. *)
  Parameter result_other : forall o s a b,
    ~ In o (bvadd :: bvsub :: bvmul :: nil) -> mathematical_result o s a b = None.
  (** Overflow checking alarms unless the widths agree and the result range fits. *)
  Parameter may_fail_overflow : forall o s a b, may_fail (Overflow o s) [a; b] =
    match W.width a, W.width b,
      range_result o (if s then QS.range a else Q.range a)
        (if s then QS.range b else Q.range b) with
    | Some w, Some v, Some r => negb (Pos.eqb w v && range_fits s w r)
    | _, _, _ => true
    end.
  (** Every other kind or arity reports a possible error. *)
  Parameter may_fail_other : forall k xs,
    match k, xs with
    | DivZero, [_] | NullDeref, [_] | Bounds, [_; _] | Overflow _ _, [_; _] => True
    | _, _ => may_fail k xs = true
    end.
End BITS_CHECKS_LAWS.

Module Type BITS_CHECKS (V : VALUE_DOMAIN BitsLang)
    (Q : RANGE_QUERY BitsLang NumU V) (QS : RANGE_QUERY BitsLang NumS V) (W : BITS_WIDTH V) :=
  BITS_CHECKS_BASE V Q QS W <+ BITS_CHECKS_LAWS V Q QS W.

Module Type BITS_CHECKS_TIME (V : VALUE_DOMAIN_T BitsLangT)
    (Q : BITS_RANGE_T NumU V) (QS : BITS_RANGE_T NumS V) (W : BITS_WIDTH_T V)
    (Import C : BITS_CHECKS V Q QS W).
  Include CHECKS_TIME BitsLangT V C.
  Parameter c_bits_checks : N.
  (** A zero check charges its query and the finite endpoint comparisons. *)
  Parameter T_divzero_le : forall d, (T_may_fail DivZero [d] <= c_bits_checks *
    (Q.T_range d + N.of_nat (range_bits (Q.range d) + 1)))%N.
  (** A null check charges its query and the finite endpoint comparisons. *)
  Parameter T_null_le : forall d, (T_may_fail NullDeref [d] <= c_bits_checks *
    (Q.T_range d + N.of_nat (range_bits (Q.range d) + 1)))%N.
  (** A bounds check charges both queries and all compared finite endpoints. *)
  Parameter T_bounds_le : forall i len, (T_may_fail Bounds [i; len] <= c_bits_checks *
    (Q.T_range i + Q.T_range len +
      N.of_nat (range_bits (Q.range i) + range_bits (Q.range len) + 1)))%N.
  (** Check work squares the operand sizes, for the endpoint products of overflow. *)
  Parameter work_sizes : forall k xs, work k xs =
    (fold_right Nat.add 0%nat (map V.size xs) + length xs + 1) ^ 2.
End BITS_CHECKS_TIME.

Module Type BITS_CHECKS_T (V : VALUE_DOMAIN_T BitsLangT)
    (Q : BITS_RANGE_T NumU V) (QS : BITS_RANGE_T NumS V) (W : BITS_WIDTH_T V) :=
  BITS_CHECKS V Q QS W <+ BITS_CHECKS_TIME V Q QS W.

Module Type BITS_CHECKS_PLAN (V : VALUE_DOMAIN_T BitsLangT)
    (Q : BITS_RANGE_T NumU V) (QS : BITS_RANGE_T NumS V) (W : BITS_WIDTH_T V)
    (Import C : BITS_CHECKS_T V Q QS W).
  Parameter k_bits_checks : N.
  (** Excluding zero from a containing range excludes a zero divisor. *)
  Parameter F1_zero : forall a c, V.gamma a c -> range_zero (Q.range a) = false ->
    snd c <> 0%Z.
  (** Ordered abstract endpoints imply concrete bounds safety. *)
  Parameter F2_bounds : forall a b i len, V.gamma a i -> V.gamma b len ->
    range_nonnegative (Q.range a) = true ->
    bound_lt (snd (Q.range a)) (fst (Q.range b)) = true -> (0 <= snd i < snd len)%Z.
  (** The generated zero-membership clock charges its finite endpoints. *)
  Parameter T1_zero : forall r, (T_range_zero r <=
    k_bits_checks * N.of_nat (range_bits r + 1))%N.
End BITS_CHECKS_PLAN.

Module Type BITS_CHECKS_ALL (V : VALUE_DOMAIN_T BitsLangT)
    (Q : BITS_RANGE_T NumU V) (QS : BITS_RANGE_T NumS V) (W : BITS_WIDTH_T V) :=
  BITS_CHECKS_T V Q QS W <+ BITS_CHECKS_PLAN V Q QS W.
