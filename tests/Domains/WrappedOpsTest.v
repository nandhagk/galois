(** * Circular transfer observations

    Circular transfers split operands at numeric poles before evaluation.
    For example, signed division can produce an arc that crosses zero.
    Builds on: WrappedOps and BitsLang.

    Groups:
    - [ForwardTests] Forward transfers of masks, division, truncation and extension.
    - [BackwardTests] Backward transfers that assume a comparison or an addition.
    - [RangeTests] The unsigned range of a tagged value. *)

From Stdlib Require Import ZArith List.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import BitsLang WordSig ValueSig WrappedSig Wrapped WrappedOps Tagged.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

(** The circular domain over the word language. *)
Module W := WrappedCode WordLanguageCode.
(** The circular table over the word language. *)
Module T := WrappedTableCode WordLanguageCode W.
(** Widths used by the examples. *)
Local Abbreviation w8 := 8%positive.
Local Abbreviation w1 := 1%positive.
Local Abbreviation w4 := 4%positive.
Local Abbreviation w16 := 16%positive.
(** The range payload and its table, over the word language. *)
Module RangePayload := Wrapped WordLanguage.
Module RangeTable := WrappedTable WordLanguage RangePayload.
Module RangeDomain := WordDomain WordLanguage RangePayload RangeTable.
Module Range := WrappedRange WordLanguage RangePayload RangeDomain.Domain.

(** * Forward *)

Module ForwardTests.

  (** Joining the two arms of a masked select gives the arc that covers both. *)
  Example ite_joins_masked_arcs :
    T.wfwd bvite w8
      [(w1, WFull); (w8, WItv 250 3); (w8, WItv 1 9)] =
      Some (WItv 250 9).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The same masked select at width 64 joins the same two arcs. *)
  Example ite_joins_masked_arcs_width_64 :
    T.wfwd bvite 64%positive
      [(w1, WFull); (64%positive, WItv 250 3); (64%positive, WItv 1 9)] =
      Some (WItv 250 9).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Signed division of an arc that crosses zero gives the arc of the quotients. *)
  Example signed_division_crosses_zero :
    T.wfwd bvsdiv w8 [(w8, WItv 250 255); (w8, WItv 2 2)] = Some (WItv 253 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Signed remainder of an arc that crosses zero gives the arc of the remainders. *)
  Example signed_remainder_crosses_zero :
    T.wfwd bvsrem w8 [(w8, WItv 250 255); (w8, WItv 2 2)] = Some (WItv 255 0).
  Proof. vm_compute. reflexivity. Qed.

  (** Truncating an arc to four bits wraps its span modulo sixteen. *)
  Example truncation_wraps_span :
    T.wfwd (bvtrunc w4) w4 [(w8, WItv 250 255)] = Some (WItv 10 15).
  Proof. vm_compute. reflexivity. Qed.

  (** Sign extension keeps the negative arc as the upper values of the wider word. *)
  Example sign_extension_keeps_negative_arc :
    T.wfwd (bvsext w8) w16 [(w8, WItv 250 255)] = Some (WItv 65530 65535).
  Proof. vm_compute. reflexivity. Qed.

End ForwardTests.

(** * Backward *)

Module BackwardTests.

  (** Assuming an unsigned comparison holds narrows the first operand to the values below. *)
  Example assume_unsigned_less_than_narrows :
    T.wbwd bvult w1 (WItv 1 1) [(w8, WItv 0 20); (w8, WItv 10 10)] =
      Some [WItv 0 9; WItv 10 10].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a modular sum narrows the operand by the other operand's value. *)
  Example assume_modular_add_narrows :
    T.wbwd bvadd w8 (WItv 5 5) [(w8, WItv 250 3); (w8, WItv 10 10)] =
      Some [WItv 251 251; WItv 10 10].
  Proof. vm_compute. reflexivity. Qed.

  (** Assuming a truncation keeps an arc that fits the narrow word. *)
  Example assume_truncation_fitting_keeps_arc :
    T.wbwd (bvtrunc w4) w4 (WItv 3 5) [(w8, WItv 0 10)] = Some [WItv 3 5].
  Proof. vm_compute. reflexivity. Qed.

End BackwardTests.

(** * Range *)

Module RangeTests.

  (** The unsigned range of an arc with out-of-range endpoints is reduced modulo the width. *)
  Example range_reduces_endpoints_modulo_width :
    Range.range (TVal w8 (WItv 260 270)) = (Fin 4, Fin 14).
  Proof. vm_compute. reflexivity. Qed.

  (** An arc that crosses zero has the full unsigned range. *)
  Example range_of_arc_crossing_zero_is_full :
    Range.range (TVal w8 (WItv 250 3)) = (Fin 0, Fin 255).
  Proof. vm_compute. reflexivity. Qed.

  (** A negative singleton is the top unsigned value. *)
  Example range_of_negative_singleton_is_top :
    Range.range (TVal w8 (WItv (-1) (-1))) = (Fin 255, Fin 255).
  Proof. vm_compute. reflexivity. Qed.

  (** An arc that wraps all the way round has the full unsigned range. *)
  Example range_of_full_arc_is_full :
    Range.range (TVal w8 (WItv 10 9)) = (Fin 0, Fin 255).
  Proof. vm_compute. reflexivity. Qed.

  (** An empty payload has the empty range, from positive to negative infinity. *)
  Example range_of_empty_payload_is_empty :
    Range.range (TVal w8 WBot) = (PosInf, NegInf).
  Proof. vm_compute. reflexivity. Qed.

  (** An unknown tag has the whole range, from negative to positive infinity. *)
  Example range_of_unknown_tag_is_whole :
    Range.range TAny = (NegInf, PosInf).
  Proof. vm_compute. reflexivity. Qed.

End RangeTests.
