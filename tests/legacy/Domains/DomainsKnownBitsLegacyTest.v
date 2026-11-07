(** * Differential mask and multiplier fixtures

    The new mask operations and multipliers are compared with their legacy implementations.
    For example, nonconstant low-zero multiplication keeps the legacy trailing-zero result.
    Builds on: new and legacy known-bit multiplication and signed-half reduction. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsTnum DomainsTnumArith DomainsTnumMul
  DomainsSignedBounds DomainsNumeric DomainsKnownBits.
From GaloisLegacy.Bits Require BitsOp.
From GaloisLegacy.Domains Require DomainsNumeric DomainsKnownBits DomainsKnownBitsFast
  DomainsSignedBounds.
Import List.ListNotations.

Module OldBits := GaloisLegacy.Domains.DomainsKnownBits.
Module OldMul := GaloisLegacy.Domains.DomainsKnownBitsFast.
Module OldBounds := GaloisLegacy.Domains.DomainsSignedBounds.
Module OldNumeric := GaloisLegacy.Domains.DomainsNumeric.
Module OldOp := GaloisLegacy.Bits.BitsOp.

Local Open Scope Z_scope.

Definition legacy_tnum (a : tnum) : OldBits.tnum := OldBits.Tnum (zeros a) (ones a).

Definition legacy_tnum_agrees (a : tnum) (b : OldBits.tnum) : bool :=
  (zeros a =? OldBits.zeros b) && (ones a =? OldBits.ones b).

Definition legacy_mul_fixtures (w : width) : list tnum :=
  [tnum_top; tnum_const w 0; tnum_const w 1; tnum_const w (-1);
   Tnum 1 0; Tnum 0 1; Tnum 1 1; Tnum (-2) 256; Tnum 3 0; Tnum 28 1].

Definition legacy_mul_comparison (w : width) : bool :=
  forallb (fun a => forallb (fun b =>
    legacy_tnum_agrees (tnum_mul w a b) (OldBits.tnum_mul w (legacy_tnum a) (legacy_tnum b)) &&
    legacy_tnum_agrees (tnum_mul_stages w a b)
      (OldMul.tnum_mul_precise w (legacy_tnum a) (legacy_tnum b)) &&
    legacy_tnum_agrees (tnum_add w a b)
      (OldBits.tnum_add w (legacy_tnum a) (legacy_tnum b)) &&
    legacy_tnum_agrees (tnum_sub w a b)
      (OldBits.tnum_sub w (legacy_tnum a) (legacy_tnum b)))
    (legacy_mul_fixtures w)) (legacy_mul_fixtures w).

Example legacy_multipliers_widths_one_four_eight :
  forallb legacy_mul_comparison [1%positive; 4%positive; 8%positive] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition legacy_half (h : sb_half) : OldBounds.sb_half :=
  match h with
  | SBEmpty => OldBounds.SBEmpty
  | SBRange t lo hi => OldBounds.SBRange (legacy_tnum t) lo hi
  end.

Definition legacy_half_agrees (a : sb_half) (b : OldBounds.sb_half) : bool :=
  match a, b with
  | SBEmpty, OldBounds.SBEmpty => true
  | SBRange ta la ua, OldBounds.SBRange tb lb ub =>
    legacy_tnum_agrees ta tb && (la =? lb) && (ua =? ub)
  | _, _ => false
  end.

Definition legacy_reduction_comparison (w : width) : bool :=
  forallb (fun t => forallb (fun s => forallb (fun r =>
    let '(lo, hi) := r in
    legacy_half_agrees (sb_reduce_half w s (SBRange t lo hi))
      (OldBounds.sb_reduce_half w s (legacy_half (SBRange t lo hi))))
    [(0, modulus w - 1); (1, 6); (-5, modulus w + 4); (6, 1)])
    [false; true]) (legacy_mul_fixtures w).

Example legacy_reduction_widths_one_four_eight :
  forallb legacy_reduction_comparison [1%positive; 4%positive; 8%positive] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Fixpoint legacy_payloads_agree (xs : list tnum) (ys : list OldBits.tnum) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => legacy_tnum_agrees x y && legacy_payloads_agree xs ys
  | _, _ => false
  end.

Definition legacy_test_operators : list op :=
  [bvnot; bvneg; bvclz; bvctz; bvpopcnt; bvadd; bvsub; bvmul; bvudiv; bvurem;
   bvsdiv; bvsrem; bvsmod; bvand; bvor; bvxor; bvshl; bvlshr; bvashr; bvrotl; bvrotr;
   bveq; bvne; bvult; bvule; bvslt; bvsle; bvite; bvzext 1%positive; bvsext 1%positive;
   bvtrunc 1%positive; bvextract 0 0; bvconcat].

Definition legacy_operator (o : op) : OldOp.op :=
  match o with
  | bvnot => OldOp.bvnot
  | bvneg => OldOp.bvneg
  | bvclz => OldOp.bvclz
  | bvctz => OldOp.bvctz
  | bvpopcnt => OldOp.bvpopcnt
  | bvadd => OldOp.bvadd
  | bvsub => OldOp.bvsub
  | bvmul => OldOp.bvmul
  | bvudiv => OldOp.bvudiv
  | bvurem => OldOp.bvurem
  | bvsdiv => OldOp.bvsdiv
  | bvsrem => OldOp.bvsrem
  | bvsmod => OldOp.bvsmod
  | bvand => OldOp.bvand
  | bvor => OldOp.bvor
  | bvxor => OldOp.bvxor
  | bvshl => OldOp.bvshl
  | bvlshr => OldOp.bvlshr
  | bvashr => OldOp.bvashr
  | bvrotl => OldOp.bvrotl
  | bvrotr => OldOp.bvrotr
  | bveq => OldOp.bveq
  | bvne => OldOp.bvne
  | bvult => OldOp.bvult
  | bvule => OldOp.bvule
  | bvslt => OldOp.bvslt
  | bvsle => OldOp.bvsle
  | bvite => OldOp.bvite
  | bvzext n => OldOp.bvzext n
  | bvsext n => OldOp.bvsext n
  | bvtrunc n => OldOp.bvtrunc n
  | bvextract hi lo => OldOp.bvextract hi lo
  | bvconcat => OldOp.bvconcat
  end.

Definition legacy_operator_comparison (w : width) (o : op) (a b : tnum) : bool :=
  let xs :=
    match arity o with
    | 1%nat => [(w, a)]
    | 2%nat => [(w, a); (w, b)]
    | _ => [(1%positive, a); (w, a); (w, b)]
    end in
  let rw := match result_width o (map fst xs) with Some r => r | None => w end in
  let oldxs := map (fun wp => (fst wp, legacy_tnum (snd wp))) xs in
  let oldop := legacy_operator o in
  legacy_tnum_agrees (pforward known_bits_classic_domain o xs rw)
    (OldNumeric.pforward OldBits.known_bits_domain oldop oldxs rw) &&
  legacy_tnum_agrees (pforward known_bits_domain o xs rw)
    (OldNumeric.pforward OldMul.known_bits_precise_domain oldop oldxs rw) &&
  legacy_payloads_agree (passume known_bits_classic_domain o xs rw a)
    (OldNumeric.passume OldBits.known_bits_domain oldop oldxs rw (legacy_tnum a)) &&
  legacy_payloads_agree (passume known_bits_domain o xs rw a)
    (OldNumeric.passume OldMul.known_bits_precise_domain oldop oldxs rw (legacy_tnum a)).

Definition legacy_all_operators_comparison (w : width) : bool :=
  forallb (fun o => forallb (fun a => forallb (legacy_operator_comparison w o a)
    (legacy_mul_fixtures w)) (legacy_mul_fixtures w)) legacy_test_operators.

Example legacy_full_known_bits_widths_one_four_eight :
  forallb legacy_all_operators_comparison [1%positive; 4%positive; 8%positive] = true.
Proof.
  vm_compute. reflexivity.
Qed.
