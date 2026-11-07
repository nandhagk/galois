(** * Encoded equality tests

    Equality tests distinguish matching, different and boundary keys.
    For example, lists compare by their injective serialized codes.
    Builds on: BaseEq and BaseCode. *)

From Stdlib Require Import Bool List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq.
Import List.ListNotations.

Local Open Scope positive_scope.

Example equality_accepts : eqb (codec_enc (list_codec nat_codec)) [1; 2]%nat [1; 2]%nat = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_rejects : eqb (codec_enc (list_codec nat_codec)) [1; 2]%nat [2; 1]%nat = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_empty_boundary : eqb (codec_enc (list_codec nat_codec)) [] [] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_ticks : Cost.ticks (eqb_c positive_encoding 1 2) = 5%N.
Proof.
  vm_compute. reflexivity.
Qed.
