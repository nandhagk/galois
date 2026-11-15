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
