(** * Known-bit mask and carry fixtures

    These examples check normalized masks, contradictory facts and closed-form arithmetic.
    For example, seven or fifteen plus one exposes uncertainty in the fourth and fifth bits.
    Builds on: DomainsTnum and DomainsTnumArith. *)

From Stdlib Require Import ZArith Bool.
From Galois.Domains Require Import KnownBitsSig KnownBits BitsLang.

Local Open Scope Z_scope.

Example tnum_masks_modulo :
  tnum_leb 8%positive (Tnum (-16) 257) (Tnum 240 1) = true /\
  tnum_leb 8%positive (Tnum 240 1) (Tnum (-16) 257) = true.
Proof.
  vm_compute. auto.
Qed.

Example tnum_raw_equivalence_is_not_record_equality :
  tnum_leb 4%positive (Tnum 16 0) tnum_top = true /\
  tnum_leb 4%positive tnum_top (Tnum 16 0) = true /\
  Tnum 16 0 <> tnum_top.
Proof.
  vm_compute. split; [reflexivity|]. split; [reflexivity|discriminate].
Qed.

Example tnum_conflicting_bit : ~ tnum_gamma 8%positive (Tnum 1 1) 0.
Proof.
  vm_compute. intros [_ Hbad]. discriminate.
Qed.

Example tnum_carry_propagation :
  tnum_add 8%positive (Tnum 240 7) (tnum_const 8%positive 1) = Tnum 231 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example tnum_borrow_propagation :
  tnum_sub 8%positive (Tnum 246 8) (tnum_const 8%positive 1) = Tnum 240 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example tnum_one_bit_negation :
  tnum_neg 1%positive (tnum_const 1%positive 1) = Tnum 0 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example tnum_linux_carry :
  tnum_add 8%positive (Tnum 240 7) (tnum_const 8%positive 1) =
    tnum_linux_add 8%positive (Tnum 240 7) (tnum_const 8%positive 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example tnum_division_zero_boundary :
  tnum_udiv 8%positive (Tnum 240 0) (tnum_const 8%positive 0) = tnum_top /\
  tnum_udiv 8%positive (Tnum 240 0) (Tnum 0 1) = Tnum 240 0 /\
  tnum_urem 8%positive (Tnum 240 0) = Tnum 240 0.
Proof.
  vm_compute. auto.
Qed.

Module LowMultiplier <: TNUM_CONFIG.
  Definition multiplier := MulLow.
End LowMultiplier.
Module MaskCode := KnownBitsCode WordLanguageCode LowMultiplier.

(** The old unguarded join returned Tnum 0 0 for this input. *)
Example tnum_raw_widen_stable :
  MaskCode.pwiden tt 4%positive (Tnum 16 0) (Tnum 0 0) = Tnum 16 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example contradictory_mask_is_least :
  MaskCode.pleb 2%positive (Tnum 1 1) (Tnum 2 0) = true.
Proof. vm_compute. reflexivity. Qed.

(** Full uncertainty in the amount includes every shift up to saturation. *)
Example tnum_fast_variable_unknown_amounts :
  MaskCode.tnum_variable Op.bvshl 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvlshr 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 240 0 /\
  MaskCode.tnum_variable Op.bvashr 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 240 0 /\
  MaskCode.tnum_variable Op.bvshl 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvlshr 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvashr 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** A constant one-bit amount copies the endpoint masks and the inserted zero bits. *)
Example tnum_fast_variable_constant_amounts :
  MaskCode.tnum_variable Op.bvshl 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
    Tnum 225 30 /\
  MaskCode.tnum_variable Op.bvlshr 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
    Tnum 248 7 /\
  MaskCode.tnum_variable Op.bvashr 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
    Tnum 248 7 /\
  MaskCode.tnum_variable Op.bvshl 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
    Tnum 481 30 /\
  MaskCode.tnum_variable Op.bvlshr 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
    Tnum (2 ^ 63 + 120) 7 /\
  MaskCode.tnum_variable Op.bvashr 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
    Tnum 120 7.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Sparse amount masks retain the facts shared by their odd shift counts. *)
Example tnum_fast_variable_sparse_amounts :
  MaskCode.tnum_variable Op.bvshl 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 1 0 /\
  MaskCode.tnum_variable Op.bvlshr 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 248 0 /\
  MaskCode.tnum_variable Op.bvashr 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 248 0 /\
  MaskCode.tnum_variable Op.bvshl 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum 1 0 /\
  MaskCode.tnum_variable Op.bvlshr 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum (2 ^ 63) 0 /\
  MaskCode.tnum_variable Op.bvashr 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Zero-bit cutoffs and either empty operand keep their specified boundary behavior. *)
Example tnum_fast_variable_boundaries :
  MaskCode.tnum_variable Op.bvshl 1%positive (Tnum 0 1) (Tnum 0 0) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvshl 8%positive (Tnum 7 7) (Tnum 0 0) = Tnum 255 255 /\
  MaskCode.tnum_variable Op.bvlshr 8%positive (Tnum 0 0) (Tnum 7 7) = Tnum 255 255.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Every bit position varies when an unknown amount rotates these mixed masks. *)
Example tnum_fast_rotation_unknown_amounts :
  MaskCode.tnum_variable Op.bvrotl 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvrotr 8%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvrotl 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvrotr 64%positive (Tnum 240 15) (Tnum 0 0) = Tnum 0 0.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** A constant rotation moves the two masks and wraps their boundary bits. *)
Example tnum_fast_rotation_constant_amounts :
  MaskCode.tnum_variable Op.bvrotl 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
    Tnum 225 30 /\
  MaskCode.tnum_variable Op.bvrotr 8%positive (Tnum 240 15) (tnum_const 8%positive 1) =
    Tnum 120 135 /\
  MaskCode.tnum_variable Op.bvrotl 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
    Tnum 480 30 /\
  MaskCode.tnum_variable Op.bvrotr 64%positive (Tnum 240 15) (tnum_const 64%positive 1) =
    Tnum 120 (2 ^ 63 + 7).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** The possible odd rotations have no common known bit in either direction. *)
Example tnum_fast_rotation_sparse_amounts :
  MaskCode.tnum_variable Op.bvrotl 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvrotr 8%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvrotl 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvrotr 64%positive (Tnum 240 15) (Tnum 248 1) = Tnum 0 0.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Unit widths stay fixed, while non-power-of-two widths retain the complete traversal. *)
Example tnum_fast_rotation_boundaries :
  MaskCode.tnum_variable Op.bvrotl 1%positive (Tnum 0 1) (Tnum 0 0) = Tnum 0 1 /\
  MaskCode.tnum_variable Op.bvrotr 1%positive (Tnum 0 1) (Tnum 0 0) = Tnum 0 1 /\
  MaskCode.tnum_variable Op.bvrotl 7%positive (Tnum 112 15) (Tnum 0 0) = Tnum 0 0 /\
  MaskCode.tnum_variable Op.bvrotr 7%positive (Tnum 112 15) (Tnum 0 0) = Tnum 0 0.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.
