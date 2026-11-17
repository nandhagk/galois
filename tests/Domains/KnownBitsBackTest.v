(** * Known-bit extraction table bounds

    Extraction offsets must be bounded before the table evaluates their arithmetic.
    For example, a one-bit operand cannot supply a bit at offset eight.
    Builds on: KnownBitsOps and the generated word-operation clocks. *)

From Stdlib Require Import ZArith NArith List Lia.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import BitsLang KnownBitsSig KnownBits KnownBitsOps KnownBitsBack.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Stages <: TNUM_CONFIG.
  Definition multiplier := MulStages.
End Stages.
Module Masks := KnownBitsT WordLanguageT Stages.
Module RawClocks := KnownBitsOpsClock WordLanguageT Stages Masks.

(** Converting a unary successor count visits every constructor. *)
Local Lemma successor_conversion_clock_lower : forall n,
  (N.of_nat n + 1 <= Op.Pos.T_of_succ_nat n)%N.
Proof.
  induction n as [|n IH]; time_unfold Op.Pos.T_of_succ_nat; time_cbn;
    rewrite ?Nat2N.inj_succ; lia.
Qed.

Module Table := KnownBitsTableT WordLanguageT Stages Masks.

(** The old unchecked forward value was Some (Tnum 1 0). *)
Example extraction_outside_operand_rejected :
  Table.wfwd (bvextract 0 8) 1%positive [(1%positive, tnum_top)] = None.
Proof. vm_compute; reflexivity. Qed.

Example backward_extraction_outside_operand_rejected :
  Table.wbwd (bvextract 0 8) 1%positive tnum_top [(1%positive, tnum_top)] = None.
Proof. vm_compute; reflexivity. Qed.

Example extraction_at_zero_preserved :
  Table.wfwd (bvextract 0 0) 1%positive [(1%positive, tnum_top)] = Some tnum_top.
Proof. vm_compute; reflexivity. Qed.

Example backward_extraction_at_zero_preserved :
  Table.wbwd (bvextract 0 0) 1%positive (tnum_const 1%positive 1)
    [(1%positive, tnum_top)] = Some [tnum_const 1%positive 1].
Proof. vm_compute; reflexivity. Qed.

(** Shared masks keep the exact arithmetic refinements specified by constant operands. *)
Example backward_shared_arithmetic :
  Table.wbwd bvand 8%positive (tnum_const 8%positive 15)
    [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 255)] =
      Some [tnum_const 8%positive 15; tnum_const 8%positive 255] /\
  Table.wbwd bvor 8%positive (tnum_const 8%positive 15)
    [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 0)] =
      Some [tnum_const 8%positive 15; tnum_const 8%positive 0] /\
  Table.wbwd bvxor 8%positive (tnum_const 8%positive 15)
    [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 3)] =
      Some [tnum_const 8%positive 12; tnum_const 8%positive 3] /\
  Table.wbwd bvadd 64%positive (tnum_const 64%positive 15)
    [(64%positive, tnum_top); (64%positive, tnum_const 64%positive 3)] =
      Some [tnum_const 64%positive 12; tnum_const 64%positive 3] /\
  Table.wbwd bvsub 8%positive (tnum_const 8%positive 15)
    [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 3)] =
      Some [tnum_const 8%positive 18; tnum_const 8%positive 3].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Shared source and result masks preserve resizing, extraction and concatenation. *)
Example backward_shared_projection :
  Table.wbwd (bvzext 4%positive) 8%positive (tnum_const 8%positive 5)
    [(4%positive, tnum_top)] = Some [tnum_const 4%positive 5] /\
  Table.wbwd (bvsext 4%positive) 8%positive (tnum_const 8%positive 253)
    [(4%positive, tnum_top)] = Some [tnum_const 4%positive 13] /\
  Table.wbwd (bvextract 7 4) 4%positive (tnum_const 4%positive 5)
    [(8%positive, tnum_top)] = Some [Tnum 160 80] /\
  Table.wbwd bvconcat 8%positive (tnum_const 8%positive 90)
    [(4%positive, tnum_top); (4%positive, tnum_top)] =
      Some [tnum_const 4%positive 5; tnum_const 4%positive 10].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Backward order bounds still retain every allowed low-nibble value. *)
Example backward_shared_order :
  Table.wbwd bvult 1%positive (tnum_const 1%positive 1)
    [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 16)] =
      Some [Tnum 240 0; tnum_const 8%positive 16] /\
  Table.wbwd bvule 1%positive (tnum_const 1%positive 1)
    [(8%positive, tnum_top); (8%positive, tnum_const 8%positive 15)] =
      Some [Tnum 240 0; tnum_const 8%positive 15].
Proof.
  vm_compute. split; reflexivity.
Qed.

(** One-bit, inconsistent and oversized masks keep their specified exact results. *)
Example backward_shared_boundary_masks :
  Table.wbwd bvnot 1%positive (tnum_const 1%positive 0)
    [(1%positive, tnum_top)] = Some [tnum_const 1%positive 1] /\
  Table.wbwd bvnot 8%positive (Tnum 7 7)
    [(8%positive, Tnum 7 7)] = Some [Tnum 7 7] /\
  Table.wbwd bvnot 8%positive (Tnum 511 256)
    [(8%positive, tnum_top)] = Some [Tnum 0 255].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Inverse variable shifts retain the common copied bits and the arithmetic sign bit. *)
Example backward_fast_variable_shifts :
  Table.wbwd bvshl 8%positive (tnum_const 8%positive 128)
    [(8%positive, tnum_top); (8%positive, Tnum 252 0)] =
      Some [Tnum 15 0; Tnum 252 0] /\
  Table.wbwd bvlshr 8%positive (tnum_const 8%positive 128)
    [(8%positive, tnum_top); (8%positive, Tnum 252 0)] =
      Some [Tnum 120 0; Tnum 252 0] /\
  Table.wbwd bvashr 8%positive (tnum_const 8%positive 128)
    [(8%positive, tnum_top); (8%positive, Tnum 252 0)] =
      Some [Tnum 120 128; Tnum 252 0].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** A possible shift by the width erases copied bits but keeps arithmetic sign information. *)
Example backward_fast_oversized_shift :
  Table.wbwd bvlshr 8%positive (tnum_const 8%positive 15)
    [(8%positive, tnum_top); (8%positive, Tnum 247 0)] =
      Some [tnum_top; Tnum 247 0] /\
  Table.wbwd bvashr 8%positive (tnum_const 8%positive 15)
    [(8%positive, tnum_top); (8%positive, Tnum 247 0)] =
      Some [Tnum 128 0; Tnum 247 0].
Proof.
  vm_compute. split; reflexivity.
Qed.

(** A zero rotation stride preserves the projected constant in both directions. *)
Example backward_fast_rotation_stop :
  Table.wbwd bvrotl 8%positive (tnum_const 8%positive 15)
    [(8%positive, tnum_top); (8%positive, Tnum 247 0)] =
      Some [tnum_const 8%positive 15; Tnum 247 0] /\
  Table.wbwd bvrotr 8%positive (tnum_const 8%positive 15)
    [(8%positive, tnum_top); (8%positive, Tnum 247 0)] =
      Some [tnum_const 8%positive 15; Tnum 247 0].
Proof.
  vm_compute. split; reflexivity.
Qed.

(** At width one, only arithmetic shifts and rotations retain the known result bit. *)
Example backward_fast_width_one :
  Table.wbwd bvshl 1%positive (tnum_const 1%positive 1)
    [(1%positive, tnum_top); (1%positive, tnum_top)] = Some [tnum_top; tnum_top] /\
  Table.wbwd bvashr 1%positive (tnum_const 1%positive 1)
    [(1%positive, tnum_top); (1%positive, tnum_top)] = Some [Tnum 0 1; tnum_top] /\
  Table.wbwd bvrotl 1%positive (tnum_const 1%positive 1)
    [(1%positive, tnum_top); (1%positive, tnum_top)] = Some [Tnum 0 1; tnum_top].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** A non-power-of-two width keeps every required rotation stage. *)
Example backward_fast_rotation_nonpower_width :
  Table.wbwd bvrotl 5%positive (tnum_const 5%positive 1)
    [(5%positive, tnum_top); (5%positive, Tnum 15 0)] = Some [Tnum 14 0; Tnum 15 0] /\
  Table.wbwd bvrotr 5%positive (tnum_const 5%positive 1)
    [(5%positive, tnum_top); (5%positive, Tnum 15 0)] = Some [Tnum 28 0; Tnum 15 0].
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Unknown rotations preserve an all-one 64-bit result through both inverse projections. *)
Example backward_fast_rotation_width_64 :
  Table.wbwd bvrotl 64%positive (Tnum 0 18446744073709551615)
    [(64%positive, tnum_top); (64%positive, tnum_top)] =
      Some [Tnum 0 18446744073709551615; tnum_top] /\
  Table.wbwd bvrotr 64%positive (Tnum 0 18446744073709551615)
    [(64%positive, tnum_top); (64%positive, tnum_top)] =
      Some [Tnum 0 18446744073709551615; tnum_top].
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Fast projection keeps the original observations on oversized and inconsistent masks. *)
Example backward_fast_raw_masks :
  Table.wbwd bvshl 8%positive (Tnum 511 256)
    [(8%positive, tnum_top); (8%positive, Tnum 256 0)] = Some [tnum_top; tnum_top] /\
  Table.wbwd bvashr 8%positive (Tnum 511 256)
    [(8%positive, tnum_top); (8%positive, Tnum 256 0)] = Some [Tnum 128 0; tnum_top] /\
  Table.wbwd bvlshr 8%positive (Tnum 7 7)
    [(8%positive, Tnum 7 7); (8%positive, Tnum 252 0)] = Some [Tnum 7 7; Tnum 252 0].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Rejected offsets have the same genuine clock, however large the offset is. *)
Example rejected_extraction_clock_constant : forall lo, (1 <= lo)%nat ->
  Table.T_wfwd (bvextract 0 lo) 1%positive [(1%positive, tnum_top)] =
  Table.T_wfwd (bvextract 0 1) 1%positive [(1%positive, tnum_top)].
Proof. intros [|lo] Hlo; [lia|reflexivity]. Qed.

Example rejected_backward_extraction_clock_constant : forall lo, (1 <= lo)%nat ->
  Table.T_wbwd (bvextract 0 lo) 1%positive tnum_top [(1%positive, tnum_top)] =
  Table.T_wbwd (bvextract 0 1) 1%positive tnum_top [(1%positive, tnum_top)].
Proof. intros [|lo] Hlo; [lia|reflexivity]. Qed.

Local Lemma offset_conversion_clock_lower : forall n,
  (N.of_nat n <= Op.Z.T_of_nat n)%N.
Proof.
  intros [|n]; time_unfold Op.Z.T_of_nat; time_cbn; [lia|].
  pose proof (successor_conversion_clock_lower n) as Hlower.
  rewrite ?Nat2N.inj_succ. lia.
Qed.

(** An unchecked extraction really pays for its arbitrary raw offset. *)
Local Lemma raw_extraction_clock_lower : forall lo,
  (N.of_nat lo <= RawClocks.T_tnum_forward_raw (bvextract 0 lo)
    [(1%positive, tnum_top)] 1%positive)%N.
Proof.
  intro lo. pose proof (offset_conversion_clock_lower lo) as Hlower.
  time_unfold RawClocks.T_tnum_forward_raw. time_cbn.
  time_unfold T_tnum_map. time_cbn. lia.
Qed.

(** No constant budget for fixed one-bit operands bounds all unchecked offsets. *)
Example unchecked_extraction_clock_unbounded : forall budget : N,
  exists lo, (budget < RawClocks.T_tnum_forward_raw (bvextract 0 lo)
    [(1%positive, tnum_top)] 1%positive)%N.
Proof.
  intro budget. exists (N.to_nat (N.succ budget)).
  pose proof (raw_extraction_clock_lower (N.to_nat (N.succ budget))) as Hlower.
  rewrite N2Nat.id in Hlower. lia.
Qed.
