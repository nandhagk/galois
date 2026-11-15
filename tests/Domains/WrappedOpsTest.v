(** * Circular transfer observations

    Circular transfers split operands at numeric poles before evaluation.
    For example, signed division can produce an arc that crosses zero.
    Builds on: WrappedOps and BitsLang. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import BitsLang WordSig ValueSig WrappedSig Wrapped WrappedOps Tagged.
Import List.ListNotations.
Local Open Scope Z_scope.
Module W := WrappedCode WordLanguageCode.
Module T := WrappedTableCode WordLanguageCode W.
Local Abbreviation w8 := 8%positive.
Local Abbreviation w1 := 1%positive.
Local Abbreviation w4 := 4%positive.
Local Abbreviation w16 := 16%positive.

Example signed_division_cross_zero :
  T.wfwd bvsdiv w8 [(w8, WItv 250 255); (w8, WItv 2 2)] = Some (WItv 253 0).
Proof. vm_compute. reflexivity. Qed.
Example signed_remainder_cross_zero :
  T.wfwd bvsrem w8 [(w8, WItv 250 255); (w8, WItv 2 2)] = Some (WItv 255 0).
Proof. vm_compute. reflexivity. Qed.
Example trunc_modular_span :
  T.wfwd (bvtrunc w4) w4 [(w8, WItv 250 255)] = Some (WItv 10 15).
Proof. vm_compute. reflexivity. Qed.
Example sign_extension :
  T.wfwd (bvsext w8) w16 [(w8, WItv 250 255)] = Some (WItv 65530 65535).
Proof. vm_compute. reflexivity. Qed.
Example assume_unsigned_true :
  T.wbwd bvult w1 (WItv 1 1) [(w8, WItv 0 20); (w8, WItv 10 10)] =
    Some [WItv 0 9; WItv 10 10].
Proof. vm_compute. reflexivity. Qed.
Example assume_modular_add :
  T.wbwd bvadd w8 (WItv 5 5) [(w8, WItv 250 3); (w8, WItv 10 10)] =
    Some [WItv 251 251; WItv 10 10].
Proof. vm_compute. reflexivity. Qed.
Example assume_trunc_fitting :
  T.wbwd (bvtrunc w4) w4 (WItv 3 5) [(w8, WItv 0 10)] = Some [WItv 3 5].
Proof. vm_compute. reflexivity. Qed.

Module RangePayload := Wrapped WordLanguage.
Module RangeTable := WrappedTable WordLanguage RangePayload.
Module RangeDomain := WordDomain WordLanguage RangePayload RangeTable.
Module Range := WrappedRange WordLanguage RangePayload RangeDomain.Domain.

Example unsigned_range_normalizes_endpoints :
  Range.range (TVal w8 (WItv 260 270)) = (Fin 4, Fin 14).
Proof. vm_compute. reflexivity. Qed.

Example unsigned_range_crosses_zero :
  Range.range (TVal w8 (WItv 250 3)) = (Fin 0, Fin 255).
Proof. vm_compute. reflexivity. Qed.

Example unsigned_range_negative_singleton :
  Range.range (TVal w8 (WItv (-1) (-1))) = (Fin 255, Fin 255).
Proof. vm_compute. reflexivity. Qed.

Example unsigned_range_full_arc :
  Range.range (TVal w8 (WItv 10 9)) = (Fin 0, Fin 255).
Proof. vm_compute. reflexivity. Qed.

Example unsigned_range_empty_payload :
  Range.range (TVal w8 WBot) = (PosInf, NegInf).
Proof. vm_compute. reflexivity. Qed.

Example unsigned_range_unknown_tag : Range.range TAny = (NegInf, PosInf).
Proof. vm_compute. reflexivity. Qed.
