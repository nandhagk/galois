(** * Certification tests

    These examples exercise acceptance, rejection and the fallback.
    For example, the evenness checker accepts zero.
    Builds on: BaseCertify and Rocq natural numbers. *)

From Stdlib Require Import Arith.
From Galois.Base Require Import BaseCertify.

Definition even_sound (n : nat) (H : Nat.even n = true) : Nat.Even n :=
  proj1 (Nat.even_spec n) H.

Definition even_fallback : {n : nat | Nat.Even n} :=
  exist _ 0 (even_sound 0 eq_refl).

Example certify_accepts :
  option_map (@proj1_sig nat Nat.Even) (certify Nat.Even Nat.even even_sound 2) = Some 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example certify_rejects :
  option_map (@proj1_sig nat Nat.Even) (certify Nat.Even Nat.even even_sound 1) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example certify_fallback_boundary :
  proj1_sig (certify_or Nat.Even Nat.even even_sound even_fallback 1) = 0.
Proof.
  vm_compute. reflexivity.
Qed.
