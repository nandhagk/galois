(** * Linear certificate fixtures

    These examples exercise raw coefficients, admissible weights and integer cuts.
    For example, a rational contradiction accepts a conclusion even at zero scale.
    Builds on: Key, LinForm, LinCertSig and LinCert. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Relational Require Import LinForm LinCertSig LinCert.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Certificates := LinCertCode PosKeyCode.

Definition eq_x : lcons positive := LCons _ [(1%positive, 1)] REq 2.
Definition le_x : lcons positive := LCons _ [(1%positive, 1)] RLe 2.
Definition twice_x : lcons positive := LCons _ [(1%positive, 2)] RLe 3.
Definition cancelled : lcons positive :=
  LCons _ [(1%positive, 1); (1%positive, -1)] REq 1.

Example empty_combination :
  Certificates.combine [] [] = Some (LCons _ [] REq 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example too_few_weights : Certificates.combine [eq_x] [] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example too_many_weights : Certificates.combine [] [1] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example negative_equality_weight :
  Certificates.combine [eq_x] [-3] = Some (LCons _ [(1%positive, -3)] REq (-6)).
Proof.
  vm_compute. reflexivity.
Qed.

Example negative_inequality_weight : Certificates.combine [le_x] [-1] = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example unused_inequality_is_equality :
  Certificates.combine [le_x] [0] = Some (LCons _ [] REq 0).
Proof.
  vm_compute. reflexivity.
Qed.

Definition five_zero_equalities : list (lcons positive) :=
  [LCons _ [(1%positive, 1)] REq 0; LCons _ [(2%positive, 1)] REq 0;
   LCons _ [(3%positive, 1)] REq 0; LCons _ [(4%positive, 1)] REq 0;
   LCons _ [(5%positive, 1)] REq 0].

Example sparse_combination_skips_unused_rows :
  Certificates.combine five_zero_equalities [0; 0; 3; 0; 0] =
    Some (LCons _ [(3%positive, 3)] REq 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example sparse_certificate_checks_scaled_conclusion :
  Certificates.check_entails five_zero_equalities (LCons _ [(3%positive, 1)] REq 0)
    (Cert [0; 0; 3; 0; 0] 3 false) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example sparse_certificate_rejects_wrong_scale :
  Certificates.check_entails five_zero_equalities (LCons _ [(3%positive, 1)] REq 0)
    (Cert [0; 0; 3; 0; 0] 1 false) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example duplicate_cancellation : Certificates.check_empty [cancelled] [1] = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example reordered_coefficients :
  Certificates.check_entails
    [LCons _ [(1%positive, 2); (2%positive, 3)] REq 7]
    (LCons _ [(2%positive, 1); (1%positive, 2); (2%positive, 2)] REq 7)
    (Cert [1] 1 false) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example contradiction_accepts_zero_scale :
  Certificates.check_entails [cancelled] (LCons _ [] REq 5) (Cert [1] 0 false) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example contradiction_accepts_negative_scale :
  Certificates.check_entails [cancelled] eq_x (Cert [1] (-2) true) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rational_model_is_not_empty :
  Certificates.check_empty [LCons _ [(1%positive, 2)] REq 1] [1] = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example exact_scaled_equality :
  Certificates.check_entails [eq_x] eq_x (Cert [3] 3 false) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example weakened_inequality :
  Certificates.check_entails [eq_x] (LCons _ [(1%positive, 1)] RLe 3)
    (Cert [1] 1 false) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example inequality_cannot_certify_equality :
  Certificates.check_entails [le_x] eq_x (Cert [1] 1 false) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example integer_cut_rounds_down :
  Certificates.check_entails [twice_x] (LCons _ [(1%positive, 1)] RLe 1)
    (Cert [1] 2 true) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rational_check_does_not_cut :
  Certificates.check_entails [twice_x] (LCons _ [(1%positive, 1)] RLe 1)
    (Cert [1] 2 false) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example unscaled_acceptance_is_rejected :
  Certificates.check_entails [eq_x] eq_x (Cert [1] 0 false) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example distinct_keys_do_not_cancel :
  Certificates.check_empty [LCons _ [(1%positive, 1); (2%positive, -1)] REq 1]
    [1] = false.
Proof.
  vm_compute. reflexivity.
Qed.
