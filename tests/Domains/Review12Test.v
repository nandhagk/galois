(** * Review round twelve observations

    These fixtures distinguish width classes and exercise the accepted view interface.
    For example, positive signs are singletons at width two and ranges at width three.
    Builds on: Sign, ZLang and Interval. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Op Word.
From Galois.Domains Require Import
  Sign SignSig Const ConstSig WordSig BitsLang ZLang Interval IntervalSig IntervalBack
  ValueSig Thresholds Congruence CongruenceSig Tagged.
Import List.ListNotations.

Module Signs := SignCode WordLanguageCode.
Module SignTable := SignTableCode WordLanguageCode Signs.
Module Ints := IntervalT ZLangT ThresholdsT.

Definition all_flags :=
  flat_map (fun n => flat_map (fun z => map (Sgn n z) [false; true]) [false; true])
    [false; true].

Definition sign_eqb (a b : sgn) :=
  Bool.eqb (neg a) (neg b) && Bool.eqb (zero a) (zero b) && Bool.eqb (pos a) (pos b).

Example symbolic_sign_reference :
  forallb (fun w => forallb (fun o => forallb (fun a => forallb (fun b =>
    sign_eqb (SignTable.sign_cmp_sym o w a b) (SignTable.sign_cmp o w a b))
      all_flags) all_flags) [bveq; bvne; bvult; bvule; bvslt; bvsle])
    [1%positive; 2%positive; 3%positive; 4%positive; 8%positive; 64%positive] = true.
Proof. vm_compute. reflexivity. Qed.

Example positive_width_two :
  SignTable.sign_cmp bveq 2%positive (Sgn false false true) (Sgn false false true) =
    Sgn true false false.
Proof. vm_compute. reflexivity. Qed.

Example positive_width_three :
  SignTable.sign_cmp bveq 3%positive (Sgn false false true) (Sgn false false true) =
    Sgn true true false.
Proof. vm_compute. reflexivity. Qed.

Example integer_view_dispatch :
  Ints.forward (ZConst 7%Z) [] = I (Fin 7%Z) (Fin 7%Z).
Proof. vm_compute. reflexivity. Qed.

Module RawConstants := ConstWordCode WordLanguageCode.
Module ShiftedConstants <: WORD_PAYLOAD_OPS WordLanguageCode.
  Definition p := flat Z.
  Definition pleb := RawConstants.pleb.
  Definition pjoin := RawConstants.pjoin.
  Definition pmeet := RawConstants.pmeet.
  Definition pbot := RawConstants.pbot.
  Definition ptop := RawConstants.ptop.
  Definition pis_bot := RawConstants.pis_bot.
  Definition pconst w z := FVal (Word.wrap w z - 1)%Z.
  Definition ppoint (_ : positive) (a : p) :=
    match a with FVal z => Some (z + 1)%Z | _ => None end.
  Definition pwparam := unit.
  Definition pwiden := RawConstants.pwiden.
  Definition pnarrow := RawConstants.pnarrow.
End ShiftedConstants.

Module ShiftedTable := ConstWordTableCode WordLanguageCode ShiftedConstants.

Definition shifted_gamma (a : flat Z) (z : Z) :=
  match a with FBot => False | FVal x => z = (x + 1)%Z | FTop => True end.

Example shifted_point_decodes :
  ShiftedConstants.ppoint 8%positive (FVal 0%Z) = Some 1%Z.
Proof. vm_compute. reflexivity. Qed.

Example shifted_shortcut_disagrees :
  ShiftedTable.shortcut bvand (8%positive, FVal 0%Z) (8%positive, FVal 0%Z) = Some 0%Z /\
  WordLanguageCode.eval_op bvand [(8%positive, 1%Z); (8%positive, 1%Z)] =
    Some (8%positive, 1%Z).
Proof. vm_compute. split; reflexivity. Qed.

Module ConstantPayload := ConstWordT WordLanguageT.
Module ConstantTable := ConstWordTableT WordLanguageT ConstantPayload.
Module ConstantDomain := WordDomainT WordLanguageT ConstantPayload ConstantTable.
Module SignPayload := SignT WordLanguageT.
Module SignEntries := SignTableT WordLanguageT SignPayload.
Module SignDomain := WordDomainT WordLanguageT SignPayload SignEntries.
Module CongruencePayload := CongruenceT WordLanguageT.
Module CongruenceEntries := CongruenceTableT WordLanguageT CongruencePayload.
Module CongruenceDomain := WordDomainT WordLanguageT CongruencePayload CongruenceEntries.
Module Scalar := IntervalBaseT ThresholdsT.
Module IntervalPayload := IntervalPayloadT WordLanguageT ThresholdsT Scalar.
Module IntervalEntries := IntervalWordTableT WordLanguageT ThresholdsT Scalar IntervalPayload.
Module IntervalDomain := WordDomainT WordLanguageT IntervalPayload IntervalEntries.

Example congruence_top_dispatch :
  CongruenceEntries.wfwd bvneg 8%positive [(4%positive, C 0 1%Z)] = Some (C 1%Z 0%Z).
Proof. vm_compute. reflexivity. Qed.

Example tagged_literal_dispatch :
  ConstantDomain.Domain.forward (BConst 8%positive 7%Z) [] =
    TVal 8%positive (FVal 7%Z).
Proof. vm_compute. reflexivity. Qed.
