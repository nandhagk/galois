(** * Value reducer observations

    Reducers exchange facts between tagged word payloads.
    For example, known low bits can refine an interval after a second exchange.
    Builds on: Reducers and the concrete word domains. *)

From Stdlib Require Import ZArith.
From Galois.Domains Require Import BitsLang ValueSig WordSig Tagged Harness Thresholds Interval IntervalBack
  WrappedSig Wrapped WrappedOps KnownBitsSig KnownBits KnownBitsBack CongruenceSig Congruence
  IntervalSig ReducersSig Reducers.
Local Open Scope Z_scope.

Module Config.
  Definition multiplier := MulLow.
End Config.
Module W := WrappedCode WordLanguageCode.
Module K := KnownBitsCode WordLanguageCode Config.
Module G := CongruenceCode WordLanguageCode.
Module Scalar := IntervalBaseCode ThresholdsCode.
Module I := IntervalPayloadCode WordLanguageCode ThresholdsCode Scalar.
Module WT := WrappedTableCode WordLanguageCode W.
Module KT := KnownBitsTableCode WordLanguageCode Config K.
Module GT := CongruenceTableCode WordLanguageCode G.
Module IT := IntervalWordTableCode WordLanguageCode ThresholdsCode Scalar I.
Module WB := TaggedCode WordLanguageCode W.
Module KB := TaggedCode WordLanguageCode K.
Module GB := TaggedCode WordLanguageCode G.
Module IB := TaggedCode WordLanguageCode I.
Module WTT := TaggedTableCode WordLanguageCode W WT.
Module KTT := TaggedTableCode WordLanguageCode K KT.
Module GTT := TaggedTableCode WordLanguageCode G GT.
Module ITT := TaggedTableCode WordLanguageCode I IT.
Module WD := HarnessCode BitsLangCode WB WTT.
Module KD := HarnessCode BitsLangCode KB KTT.
Module GD := HarnessCode BitsLangCode GB GTT.
Module ID := HarnessCode BitsLangCode IB ITT.
Module WR := WrappedBitsCode WordLanguageCode W K WD KD.
Module IR := IntervalCongrCode WordLanguageCode I G ID GD.
Module BR := IntervalBitsCode WordLanguageCode I K ID KD.

Example wrapped_first_pass :
  WR.reduce (TVal 4%positive (WItv 4 7), TVal 4%positive (Tnum 0 1)) =
    (TVal 4%positive (WItv 4 7), TVal 4%positive (Tnum 8 5)).
Proof. vm_compute. reflexivity. Qed.
Example wrapped_second_pass_refines :
  fst (WR.reduce (WR.reduce (TVal 4%positive (WItv 4 7), TVal 4%positive (Tnum 0 1)))) =
    TVal 4%positive (WItv 5 7).
Proof. vm_compute. reflexivity. Qed.
Example congruence_rounds_endpoints :
  fst (IR.to_left (TVal 8%positive (I (Fin 0) (Fin 10)), TVal 8%positive (C 4 1))) =
    TVal 8%positive (I (Fin 1) (Fin 9)).
Proof. vm_compute. reflexivity. Qed.
Example interval_bits_refines_lower :
  fst (BR.to_left (TVal 4%positive (I (Fin 0) (Fin 7)), TVal 4%positive (Tnum 0 1))) =
    TVal 4%positive (I (Fin 1) (Fin 7)).
Proof. vm_compute. reflexivity. Qed.
Example mismatched_widths_unchanged :
  WR.reduce (TVal 4%positive (WItv 4 7), TVal 8%positive (Tnum 0 1)) =
    (TVal 4%positive (WItv 4 7), TVal 8%positive (Tnum 0 1)).
Proof. vm_compute. reflexivity. Qed.

Module WF := Wrapped WordLanguage.
Module KF := KnownBits WordLanguage Config.
Module GF := Congruence WordLanguage.
Module SF := IntervalBaseCode Thresholds.
Module IF := IntervalPayload WordLanguage Thresholds SF.
Module WTF := WrappedTable WordLanguage WF.
Module KTF := KnownBitsTable WordLanguage Config KF.
Module GTF := CongruenceTable WordLanguage GF.
Module ITF := IntervalWordTable WordLanguage Thresholds SF IF.
Module WDomain := WordDomain WordLanguage WF WTF.
Module KDomain := WordDomain WordLanguage KF KTF.
Module GDomain := WordDomain WordLanguage GF GTF.
Module IDomain := WordDomain WordLanguage IF ITF.
Module WRF := WrappedBits WordLanguage Config WF KF WDomain.Domain KDomain.Domain.
Module IRF := IntervalCongr WordLanguage Thresholds SF IF GF IDomain.Domain GDomain.Domain.
Module BRF := IntervalBits WordLanguage Config Thresholds SF IF KF IDomain.Domain KDomain.Domain.

Example certified_factory_computes :
  fst (WRF.reduce (TVal 4%positive (WItv 4 7), TVal 4%positive (Tnum 0 1))) =
    TVal 4%positive (WItv 4 7).
Proof. vm_compute. reflexivity. Qed.
Module WPin <: WRAPPED_BITS_PIN WordLanguage Config WF KF WDomain.Domain KDomain.Domain WRF := WRF.
Module IPin <: INTERVAL_CONGR_PIN WordLanguage IF GF IDomain.Domain GDomain.Domain IRF := IRF.
Module BPin <: INTERVAL_BITS_PIN WordLanguage Config IF KF IDomain.Domain KDomain.Domain BRF := BRF.
