(** * Known-bit mask and carry fixtures

    These examples check normalized masks, contradictory facts and closed-form arithmetic.
    For example, seven or fifteen plus one exposes uncertainty in the fourth and fifth bits.
    Builds on: DomainsTnum and DomainsTnumArith. *)

From Stdlib Require Import ZArith Bool.
From Galois.Lattice Require Import LatticeCore.
From Galois.Domains Require Import DomainsTnum DomainsTnumArith.

Local Open Scope Z_scope.

Example tnum_masks_modulo :
  leb (tnum_lattice 8%positive) (Tnum (-16) 257) (Tnum 240 1) = true /\
  leb (tnum_lattice 8%positive) (Tnum 240 1) (Tnum (-16) 257) = true.
Proof.
  vm_compute. auto.
Qed.

Example tnum_raw_equivalence_is_not_record_equality :
  leb (tnum_lattice 4%positive) (Tnum 16 0) tnum_top = true /\
  leb (tnum_lattice 4%positive) tnum_top (Tnum 16 0) = true /\
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
