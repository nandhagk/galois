(** * Interval backward operations

    Result assumptions refine comparisons and nonwrapping arithmetic.
    For example, equality to one refines both operands of an equality test.
    Builds on: IntervalOps and fixed-width word operators. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import IntervalOps ThresholdsSig IntervalSig ValueSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module IntervalBackCode (T : THRESHOLDS_OPS).
  Include IntervalOpsCode T.
Definition interval_is_point (i : itv) (z : Z) : bool :=
  match interval_finite i with
  | Some (lo, hi) => Z.eqb lo z && Z.eqb hi z
  | None => false
  end.

Definition interval_assume_pair (o : op) (w : width) (a b q : itv) : itv * itv :=
  match o with
  | bveq => if interval_is_point q 1 then interval_assume_equal a b
            else if interval_is_point q 0 then interval_assume_neq a b else (a, b)
  | bvne => if interval_is_point q 0 then interval_assume_equal a b
            else if interval_is_point q 1 then interval_assume_neq a b else (a, b)
  | bvult => if interval_is_point q 1 then interval_assume_ult a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ule b a)
             else (a, b)
  | bvule => if interval_is_point q 1 then interval_assume_ule a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ult b a)
             else (a, b)
  | bvslt => if interval_is_point q 1 then interval_assume_signed w true true a b
             else if interval_is_point q 0 then interval_assume_signed w true false a b
             else (a, b)
  | bvsle => if interval_is_point q 1 then interval_assume_signed w false true a b
             else if interval_is_point q 0 then interval_assume_signed w false false a b
             else (a, b)
  | bvadd => interval_assume_add w a b q
  | bvsub => interval_assume_sub a b q
  | _ => (a, b)
  end.

  Definition interval_bwd1 rw q (xs : list (width * itv)) : list itv :=
    match xs with
    | [(w, a)] => [interval_assume_rewrap rw (interval_clip w a) q]
    | _ => []
    end.
  Definition interval_bwd2 o (_ : width) q (xs : list (width * itv)) : list itv :=
    match xs with
    | [(wa, a); (wb, b)] =>
      let refined := interval_assume_pair o wa (interval_clip wa a) (interval_clip wb b) q in
      [fst refined; snd refined]
    | _ => []
    end.
End IntervalBackCode.
