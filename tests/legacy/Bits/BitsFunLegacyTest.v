(** * Word function agreement

    These computations compare the new word functions to the legacy definitions.
    For example, every pair of four-bit values exercises signed and unsigned division.
    Builds on: BitsFun and the legacy BitsFun. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import BitsFun.
From GaloisLegacy.Bits Require BitsFun.

Open Scope Z_scope.

Definition values4 : list Z := List.map Z.of_nat (List.seq 0 16).

Definition unary_agrees (x : Z) : bool :=
  Z.eqb (wnot 4%positive x) (GaloisLegacy.Bits.BitsFun.wnot 4%positive x) &&
  Z.eqb (wneg 4%positive x) (GaloisLegacy.Bits.BitsFun.wneg 4%positive x) &&
  Z.eqb (wclz 4%positive x) (GaloisLegacy.Bits.BitsFun.wclz 4%positive x) &&
  Z.eqb (wctz 4%positive x) (GaloisLegacy.Bits.BitsFun.wctz 4%positive x) &&
  Z.eqb (wpopcnt 4%positive x) (GaloisLegacy.Bits.BitsFun.wpopcnt 4%positive x).

Definition binary_agrees (x y : Z) : bool :=
  Z.eqb (wadd 4%positive x y) (GaloisLegacy.Bits.BitsFun.wadd 4%positive x y) &&
  Z.eqb (wsub 4%positive x y) (GaloisLegacy.Bits.BitsFun.wsub 4%positive x y) &&
  Z.eqb (wmul 4%positive x y) (GaloisLegacy.Bits.BitsFun.wmul 4%positive x y) &&
  Z.eqb (wand 4%positive x y) (GaloisLegacy.Bits.BitsFun.wand 4%positive x y) &&
  Z.eqb (wor 4%positive x y) (GaloisLegacy.Bits.BitsFun.wor 4%positive x y) &&
  Z.eqb (wxor 4%positive x y) (GaloisLegacy.Bits.BitsFun.wxor 4%positive x y) &&
  Z.eqb (wudiv 4%positive x y) (GaloisLegacy.Bits.BitsFun.wudiv 4%positive x y) &&
  Z.eqb (wurem 4%positive x y) (GaloisLegacy.Bits.BitsFun.wurem 4%positive x y) &&
  Z.eqb (wsdiv 4%positive x y) (GaloisLegacy.Bits.BitsFun.wsdiv 4%positive x y) &&
  Z.eqb (wsrem 4%positive x y) (GaloisLegacy.Bits.BitsFun.wsrem 4%positive x y) &&
  Z.eqb (wsmod 4%positive x y) (GaloisLegacy.Bits.BitsFun.wsmod 4%positive x y) &&
  Z.eqb (wshl 4%positive x y) (GaloisLegacy.Bits.BitsFun.wshl 4%positive x y) &&
  Z.eqb (wlshr 4%positive x y) (GaloisLegacy.Bits.BitsFun.wlshr 4%positive x y) &&
  Z.eqb (washr 4%positive x y) (GaloisLegacy.Bits.BitsFun.washr 4%positive x y) &&
  Z.eqb (wrotl 4%positive x y) (GaloisLegacy.Bits.BitsFun.wrotl 4%positive x y) &&
  Z.eqb (wrotr 4%positive x y) (GaloisLegacy.Bits.BitsFun.wrotr 4%positive x y) &&
  Bool.eqb (wult 4%positive x y) (GaloisLegacy.Bits.BitsFun.wult 4%positive x y) &&
  Bool.eqb (wule 4%positive x y) (GaloisLegacy.Bits.BitsFun.wule 4%positive x y) &&
  Bool.eqb (wslt 4%positive x y) (GaloisLegacy.Bits.BitsFun.wslt 4%positive x y) &&
  Bool.eqb (wsle 4%positive x y) (GaloisLegacy.Bits.BitsFun.wsle 4%positive x y).

Example word_functions_agree :
  List.forallb unary_agrees values4 &&
  List.forallb (fun x => List.forallb (binary_agrees x) values4) values4 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example popcount_width_ten_agrees :
  List.forallb
    (fun x => Z.eqb (wpopcnt 10%positive (Z.of_nat x))
      (GaloisLegacy.Bits.BitsFun.wpopcnt 10%positive (Z.of_nat x)))
    (List.seq 0 1024) = true.
Proof.
  vm_compute. reflexivity.
Qed.
