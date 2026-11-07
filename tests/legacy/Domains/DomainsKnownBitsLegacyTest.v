(** * Differential mask and multiplier fixtures

    The new mask operations and multipliers are compared with their legacy implementations.
    For example, nonconstant low-zero multiplication keeps the legacy trailing-zero result.
    Builds on: new and legacy known-bit multiplication and signed-half reduction. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsTnum DomainsTnumArith DomainsTnumMul
  DomainsSignedBounds.
From GaloisLegacy.Domains Require DomainsKnownBits DomainsKnownBitsFast DomainsSignedBounds.
Import List.ListNotations.

Module OldBits := GaloisLegacy.Domains.DomainsKnownBits.
Module OldMul := GaloisLegacy.Domains.DomainsKnownBitsFast.
Module OldBounds := GaloisLegacy.Domains.DomainsSignedBounds.

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
