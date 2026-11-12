(** * Known-bit transfer observations

    Forward and backward operations retain their source mask observations.
    For example, an unknown shift count can retain several possible bits.
    Builds on: KnownBitsOps and KnownBitsBack. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import BitsLang KnownBitsSig KnownBits KnownBitsOps KnownBitsBack.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Stages <: TNUM_CONFIG.
  Definition multiplier := MulStages.
End Stages.
Module Masks := KnownBitsCode WordLanguageCode Stages.
Module Ops := KnownBitsOpsCode WordLanguageCode Stages Masks.
Module Table := KnownBitsTableCode WordLanguageCode Stages Masks.

Example variable_logical_shift :
  Ops.tnum_forward_raw bvshl [(8%positive, tnum_const 8%positive 1); (8%positive, Tnum 252 0)]
    8%positive = Tnum 240 0.
Proof. vm_compute. reflexivity. Qed.

Example variable_arithmetic_shift :
  Ops.tnum_forward_raw bvashr [(8%positive, tnum_const 8%positive 128); (8%positive, Tnum 252 0)]
    8%positive = Tnum 15 128.
Proof. vm_compute. reflexivity. Qed.

Example rotation_nonpower_width :
  Ops.tnum_forward_raw bvrotl [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 15 0)]
    5%positive = Tnum 28 0 /\
  Ops.tnum_forward_raw bvrotr [(5%positive, tnum_const 5%positive 1); (5%positive, Tnum 15 0)]
    5%positive = Tnum 14 0.
Proof. vm_compute. auto. Qed.

Example comparison_precision :
  Ops.tnum_forward_raw bvult [(8%positive, Tnum 128 0); (8%positive, tnum_const 8%positive 128)]
    1%positive = Tnum 0 1.
Proof. vm_compute. reflexivity. Qed.

Example backward_add :
  Table.wbwd bvadd 8%positive (tnum_const 8%positive 5)
    [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 1)] =
      Some [tnum_const 8%positive 4; tnum_const 8%positive 1].
Proof. vm_compute. reflexivity. Qed.
