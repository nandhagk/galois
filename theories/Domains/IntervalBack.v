(** * Interval backward operations

    Result assumptions refine comparisons and nonwrapping arithmetic.
    For example, equality to one refines both operands of an equality test.
    Builds on: IntervalOps and fixed-width word operators. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import IntervalOps ThresholdsSig IntervalSig ValueSig WordSig.
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

Module IntervalPayloadCode (L : WORD_LANGUAGE_OPS) (T : THRESHOLDS_OPS)
    <: (WORD_PAYLOAD_OPS L with Definition p := itv).
  Include IntervalOpsCode T.
  Definition p := itv.
  Definition pleb (_ : positive) a b := interval_leb a b.
  Definition pjoin (_ : positive) a b := interval_join a b.
  Definition pmeet (_ : positive) a b := interval_meet a b.
  Definition pbot (_ : positive) := IBot.
  Definition ptop w := interval_top w.
  Definition pis_bot w a := match interval_clip w a with IBot => true | _ => false end.
  Definition pconst w z := interval_const w z.
  Definition ppoint w a := interval_singleton (interval_clip w a).
End IntervalPayloadCode.

Module IntervalWordTableCode (L : WORD_LANGUAGE_OPS) (T : THRESHOLDS_OPS)
    (D : WORD_PAYLOAD_OPS L with Definition p := itv) <: WORD_TABLE_OPS L D.
  Include IntervalBackCode T.
  Definition wfwd (o : L.op) (rw : positive) (xs : list (positive * D.p)) : option D.p :=
    match o, xs with
    | (bvnot | bvneg | bvclz | bvctz | bvpopcnt | bvzext _ | bvtrunc _ | bvsext _),
        [(w, a)] =>
      let a := interval_clip w a in
      Some (match o with
        | bvnot => interval_not rw a
        | bvneg => interval_neg rw a
        | bvclz | bvctz | bvpopcnt => interval_counts rw
        | bvzext _ | bvtrunc _ => interval_rewrap rw a
        | _ => interval_sext rw w a
        end)
    | (bvadd | bvsub | bvmul | bvudiv | bvurem | bvsdiv | bvsrem | bvsmod |
       bvand | bvor | bvxor | bvshl | bvlshr | bvashr | bveq | bvne |
       bvult | bvule | bvslt | bvsle | bvconcat), [(wa, a); (wb, b)] =>
      let a := interval_clip wa a in
      let b := interval_clip wb b in
      Some (match o with
        | bvadd => interval_add rw a b | bvsub => interval_sub rw a b
        | bvmul => interval_mul rw a b | bvudiv => interval_udiv rw a b
        | bvurem => interval_urem rw a b | bvsdiv => interval_sdiv rw a b
        | bvsrem => interval_srem rw a b | bvsmod => interval_smod rw a b
        | bvand => interval_and rw a b | bvor | bvxor => interval_or_xor rw a b
        | bvshl => interval_shl rw a b | bvlshr => interval_lshr rw a b
        | bvashr => interval_ashr rw a b | bveq => interval_eq a b
        | bvne => interval_bool_not (interval_eq a b) | bvult => interval_ult a b
        | bvule => interval_ule a b | bvslt => interval_signed_compare wa true a b
        | bvsle => interval_signed_compare wa false a b
        | _ => interval_concat rw wb a b
        end)
    | bvite, [_; (wa, a); (wb, b)] =>
      Some (interval_join (interval_clip wa a) (interval_clip wb b))
    | _, _ => None
    end.
  Definition wbwd (o : L.op) (rw : positive) (q : D.p)
      (xs : list (positive * D.p)) : option (list D.p) :=
    match o, xs with
    | (bvzext _ | bvtrunc _), [_] => Some (interval_bwd1 rw q xs)
    | (bveq | bvne | bvult | bvule | bvslt | bvsle | bvadd | bvsub), [_; _] =>
      Some (interval_bwd2 o rw q xs)
    | _, _ => None
    end.
End IntervalWordTableCode.
