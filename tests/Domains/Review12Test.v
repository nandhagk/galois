(** * Review round twelve observations

    These fixtures distinguish width classes and exercise the accepted view interface.
    For example, positive signs are singletons at width two and ranges at width three.
    Builds on: Sign, ZLang and Interval. *)

(* Groups:
   - Signs: symbolic and width-dependent comparisons of sign values.
   - Constants: the shifted constant payload and the constant table.
   - Congruence and tagged: dispatch through the congruence and tagged tables. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Op Word.
From Galois.Domains Require Import
  Sign SignSig Const ConstSig WordSig BitsLang ZLang Interval IntervalSig IntervalBack
  ValueSig Thresholds Congruence CongruenceSig Tagged Harness.
Import List.ListNotations.

(** * Fixtures *)

(** The sign table over the word language. *)
Module Signs := SignCode WordLanguageCode.
Module SignTable := SignTableCode WordLanguageCode Signs.
(** The interval domains over the integer language. *)
Module Ints := IntervalT ZLangT ThresholdsT.
Module IntegerCode := IntervalCode ZLangCode ThresholdsCode.

(** Every combination of sign flags. *)
Definition all_flags :=
  flat_map (fun n => flat_map (fun z => map (Sgn n z) [false; true]) [false; true])
    [false; true].

(** Two signs are equal when their three flags agree. *)
Definition sign_eqb (a b : sgn) :=
  Bool.eqb (neg a) (neg b) && Bool.eqb (zero a) (zero b) && Bool.eqb (pos a) (pos b).

(** The raw constant payload over the word language. *)
Module RawConstants := ConstWordCode WordLanguageCode.
(** A constant payload that shifts the decoded point by one. *)
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

(** The constant table built from the shifted payload. *)
Module ShiftedTable := ConstWordTableCode WordLanguageCode ShiftedConstants.

(** The concrete values that a shifted constant describes. *)
Definition shifted_gamma (a : flat Z) (z : Z) :=
  match a with FBot => False | FVal x => z = (x + 1)%Z | FTop => True end.

(** The constant payloads and tables over the timed and untimed word languages. *)
Module ConstantPayload := ConstWordT WordLanguageT.
Module UntimedConstantPayload := ConstWord WordLanguage.
Module UntimedConstantTable := ConstWordTable WordLanguage UntimedConstantPayload.

(** The meaning of a constant payload, for any word language. *)
Module ConstantMeaningClient (L : WORD_LANGUAGE) (W : CONST_WORD_PAYLOAD L).
  Definition raw_meaning := W.pgamma_const_def.
End ConstantMeaningClient.

Module UntimedConstantMeaning := ConstantMeaningClient WordLanguage UntimedConstantPayload.
Module TimedConstantMeaning := ConstantMeaningClient WordLanguageT ConstantPayload.
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
Module CongruenceCodePayload := CongruenceCode WordLanguageCode.
Module CongruenceCodeEntries := CongruenceTableCode WordLanguageCode CongruenceCodePayload.
Module ConstantCodeEntries := ConstWordTableCode WordLanguageCode RawConstants.
Module ConstantCodeBase := TaggedCode WordLanguageCode RawConstants.
Module ConstantCodeTable := TaggedTableCode WordLanguageCode RawConstants ConstantCodeEntries.
Module ConstantCodeDomain := HarnessCode BitsLangCode ConstantCodeBase ConstantCodeTable.

(** * Signs *)

Module SignTests.

  (** The symbolic sign comparison agrees with the reference at every width and operand. *)
  Example symbolic_sign_matches_reference :
    forallb (fun w => forallb (fun o => forallb (fun a => forallb (fun b =>
      sign_eqb (SignTable.sign_cmp_sym o w a b) (SignTable.sign_cmp o w a b))
        all_flags) all_flags) [bveq; bvne; bvult; bvule; bvslt; bvsle])
      [1%positive; 2%positive; 3%positive; 4%positive; 8%positive; 64%positive] = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Equality of two positive signs at width two gives the table's sign result. *)
  Example positive_equality_at_width_two :
    SignTable.sign_cmp bveq 2%positive (Sgn false false true) (Sgn false false true) =
      Sgn true false false.
  Proof. vm_compute. reflexivity. Qed.

  (** Equality of two positive signs at width three gives the table's sign result. *)
  Example positive_equality_at_width_three :
    SignTable.sign_cmp bveq 3%positive (Sgn false false true) (Sgn false false true) =
      Sgn true true false.
  Proof. vm_compute. reflexivity. Qed.

End SignTests.

(** * Constants *)

Module ConstantTests.

  (** The integer view of a constant is the singleton interval of its value. *)
  Example integer_view_of_constant_is_singleton :
    IntegerCode.forward (ZConst 7%Z) [] = I (Fin 7%Z) (Fin 7%Z).
  Proof. vm_compute. reflexivity. Qed.

  (** The shifted payload decodes the point of a value by adding one. *)
  Example shifted_point_adds_one :
    ShiftedConstants.ppoint 8%positive (FVal 0%Z) = Some 1%Z.
  Proof. vm_compute. reflexivity. Qed.

  (** The shifted shortcut gives zero for a bitwise and of two zero values. *)
  Example shifted_shortcut_gives_zero :
    ShiftedTable.shortcut bvand (8%positive, FVal 0%Z) (8%positive, FVal 0%Z) = Some 0%Z.
  Proof. vm_compute. reflexivity. Qed.

  (** The word language evaluates the same bitwise and of two one values to eight one. *)
  Example word_language_and_of_ones :
    WordLanguageCode.eval_op bvand [(8%positive, 1%Z); (8%positive, 1%Z)] =
      Some (8%positive, 1%Z).
  Proof. vm_compute. reflexivity. Qed.

  (** Wrapping a negative value of width eight reduces it into the range of that width. *)
  Example fast_wrap_negative_stays_in_range :
    ConstWordFast.wrap_fast 8%positive (-257)%Z = 255%Z.
  Proof. vm_compute. reflexivity. Qed.

  (** Wrapping a value beyond two to the 128 reduces it modulo the width. *)
  Example fast_wrap_large_reduces_modulo_width :
    ConstWordFast.wrap_fast 8%positive (2 ^ 128 + 7)%Z = 7%Z.
  Proof. vm_compute. reflexivity. Qed.

  (** A backward addition of two constants normalises them to their small residues. *)
  Example backward_two_normalises_constants :
    ConstantCodeEntries.backward_two bvadd 8%positive (FVal (2 ^ 128 + 3)%Z)
      [(8%positive, FTop); (8%positive, FVal (2 ^ 128 + 1)%Z)] =
      Some [FVal 2%Z; FVal 1%Z].
  Proof. vm_compute. reflexivity. Qed.

End ConstantTests.

(** * Congruence and tagged *)

Module DispatchTests.

  (** Negating a constant congruence of width eight gives the congruence of its negation. *)
  Example congruence_negation_dispatch :
    CongruenceCodeEntries.wfwd bvneg 8%positive [(4%positive, C 0 1%Z)] =
      Some (C 1%Z 0%Z).
  Proof. vm_compute. reflexivity. Qed.

  (** A tagged literal of width eight forwards to the value that it holds. *)
  Example tagged_literal_forwards_value :
    ConstantCodeDomain.forward (BConst 8%positive 7%Z) [] =
      TVal 8%positive (FVal 7%Z).
  Proof. vm_compute. reflexivity. Qed.

End DispatchTests.

