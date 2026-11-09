(** * Scalar encoding tests

    These examples pin scalar layouts, decoder rejection and tick charges.
    For example, signed negative three has a different code from positive three.
    Builds on: BaseEncoding and CostMonad. *)

From Stdlib Require Import Bool List NArith ZArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
Import List.ListNotations.

Local Open Scope positive_scope.

Example scalar_roundtrips :
  (decode positive_codec (encode positive_encoding 3),
    decode N_codec (encode N_encoding 2%N),
    decode nat_codec (encode nat_encoding 2%nat),
    decode Z_codec (encode Z_encoding (-3)%Z),
    decode bool_codec (encode bool_encoding true),
    decode unit_codec (encode unit_encoding tt)) =
  (Some 3%positive, Some 2%N, Some 2%nat, Some (-3)%Z, Some true, Some tt).
Proof.
  vm_compute. reflexivity.
Qed.

Example scalar_rejects :
  (decode bool_codec 3, decode unit_codec 2,
    Pos.eqb (encode Z_encoding 3%Z) (encode Z_encoding (-3)%Z)) = (None, None, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example scalar_zero_boundary :
  (encode positive_encoding 1, encode N_encoding 0%N, encode nat_encoding 0%nat,
    encode Z_encoding 0%Z, encode bool_encoding false, encode unit_encoding tt) =
  (1%positive, 1%positive, 1%positive, 1%positive, 1%positive, 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example scalar_ticks : Cost.ticks (encode_c nat_encoding 4%nat) = 1%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition expensive_positive : codec positive :=
  Codec (Encoding (Cost.lift (fun _ => 1000%N) (fun p => p))) (@Some positive).

Example arbitrary_component_ticks :
  Cost.ticks (encode_c (codec_enc expensive_positive) 1) = 1000%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example imported_positive_scalar_value p : encode (codec_enc positive_codec) p = p.
Proof.
  apply positive_encoding_equation.
Qed.

Example imported_positive_scalar_cost p :
  Cost.ticks (encode_c (codec_enc positive_codec) p) = 1%N.
Proof.
  apply positive_encoding_cost.
Qed.

Example imported_positive_scalar_width p :
  key_bits (codec_enc positive_codec) p = N.pos (Pos.size p).
Proof.
  apply positive_encoding_bits.
Qed.

Example imported_unit_scalar_value x : encode (codec_enc unit_codec) x = 1%positive.
Proof.
  apply unit_encoding_equation.
Qed.

Example imported_unit_scalar_cost x : Cost.ticks (encode_c (codec_enc unit_codec) x) = 1%N.
Proof.
  apply unit_encoding_cost.
Qed.

Example imported_unit_scalar_width x : key_bits (codec_enc unit_codec) x = 1%N.
Proof.
  apply unit_encoding_bits.
Qed.

Example positive_scalar_boundary_widths :
  (key_bits positive_encoding 1, key_bits positive_encoding 2) = (1%N, 2%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example scalar_adapter_charges :
  (Cost.ticks (encode_c positive_encoding 7), Cost.ticks (encode_c unit_encoding tt)) = (1%N, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.
