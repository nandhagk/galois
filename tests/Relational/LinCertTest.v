(** * Linear certificate fixtures

    These examples exercise raw coefficients, admissible weights and integer cuts.
    For example, a rational contradiction accepts a conclusion even at zero scale.
    Builds on: Key, LinForm, LinCertSig and LinCert.

    Groups:
    - [CombineTests] Building a row from a list of weights.
    - [EntailTests] Checking a certificate against a conclusion.
    - [EmptyTests] Whether the rows of a system have a model.
    - [ContradictionTests] Accepting any conclusion from an inconsistent system.
    - [CutTests] Rounding the bounds of an integer certificate. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Relational Require Import LinForm LinCertSig LinCert.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Certificates := LinCertCode PosKeyCode.

(** The equality x = 2. *)
Definition eq_x : lcons positive := LCons _ [(1%positive, 1)] REq 2.

(** The inequality x <= 2. *)
Definition le_x : lcons positive := LCons _ [(1%positive, 1)] RLe 2.

(** The inequality 2x <= 3, whose rational bound is 3/2. *)
Definition twice_x : lcons positive := LCons _ [(1%positive, 2)] RLe 3.

(** The equality x - x = 1, which has no variable left after its coefficients cancel. *)
Definition cancelled : lcons positive :=
  LCons _ [(1%positive, 1); (1%positive, -1)] REq 1.

(** Five equalities x_i = 0, one per variable from 1 to 5. *)
Definition five_zero_equalities : list (lcons positive) :=
  [LCons _ [(1%positive, 1)] REq 0; LCons _ [(2%positive, 1)] REq 0;
   LCons _ [(3%positive, 1)] REq 0; LCons _ [(4%positive, 1)] REq 0;
   LCons _ [(5%positive, 1)] REq 0].

(** * Combination *)

Module CombineTests.

  (** Combining no rows with no weights gives the zero equality. *)
  Example empty_list_gives_zero_equality :
    Certificates.combine [] [] = Some (LCons _ [] REq 0).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A weight list shorter than the row list is rejected. *)
  Example missing_weight_is_rejected :
    Certificates.combine [eq_x] [] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A weight list longer than the row list is rejected. *)
  Example extra_weight_is_rejected :
    Certificates.combine [] [1] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative weight on an equality scales both its coefficients and its bound. *)
  Example negative_weight_scales_equality :
    Certificates.combine [eq_x] [-3] = Some (LCons _ [(1%positive, -3)] REq (-6)).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative weight is rejected on an inequality, which takes only nonnegative weights. *)
  Example negative_weight_on_inequality_is_rejected :
    Certificates.combine [le_x] [-1] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A zero weight on an inequality leaves the zero equality. *)
  Example zero_weight_on_inequality_gives_zero_equality :
    Certificates.combine [le_x] [0] = Some (LCons _ [] REq 0).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Only the rows with a nonzero weight contribute to the combined row. *)
  Example sparse_combination_skips_unused_rows :
    Certificates.combine five_zero_equalities [0; 0; 3; 0; 0] =
      Some (LCons _ [(3%positive, 3)] REq 0).
  Proof.
    vm_compute. reflexivity.
  Qed.

End CombineTests.

(** * Entailment *)

Module EntailTests.

  (** A sparse certificate accepts a scaled copy of one of its equalities. *)
  Example sparse_certificate_accepts_scaled_conclusion :
    Certificates.check_entails five_zero_equalities (LCons _ [(3%positive, 1)] REq 0)
      (Cert [0; 0; 3; 0; 0] 3 false) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The same sparse certificate rejects a scale that does not match the weight. *)
  Example sparse_certificate_rejects_wrong_scale :
    Certificates.check_entails five_zero_equalities (LCons _ [(3%positive, 1)] REq 0)
      (Cert [0; 0; 3; 0; 0] 1 false) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Coefficients may appear in any order, and a repeated key adds up. *)
  Example reordered_coefficients_are_accepted :
    Certificates.check_entails
      [LCons _ [(1%positive, 2); (2%positive, 3)] REq 7]
      (LCons _ [(2%positive, 1); (1%positive, 2); (2%positive, 2)] REq 7)
      (Cert [1] 1 false) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An equality certifies itself when it is scaled by its own weight. *)
  Example exact_scaled_equality_is_accepted :
    Certificates.check_entails [eq_x] eq_x (Cert [3] 3 false) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An equality certifies a weaker inequality with the same left-hand side. *)
  Example weakened_inequality_is_accepted :
    Certificates.check_entails [eq_x] (LCons _ [(1%positive, 1)] RLe 3)
      (Cert [1] 1 false) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An inequality does not certify an equality, even with a matching certificate. *)
  Example inequality_cannot_certify_equality :
    Certificates.check_entails [le_x] eq_x (Cert [1] 1 false) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A certificate with scale zero is rejected when the conclusion is not a contradiction. *)
  Example unscaled_acceptance_is_rejected :
    Certificates.check_entails [eq_x] eq_x (Cert [1] 0 false) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A certificate gathers repeated keys of the cached row before checking the conclusion. *)
  Example cached_gather_sums_repeated_keys :
    Certificates.check_entails
      [LCons _ [(1%positive, 2); (1%positive, -1); (2%positive, 3)] REq 7]
      (LCons _ [(2%positive, 1); (1%positive, 1); (2%positive, 2)] REq 7)
      (Cert [1] 1 false) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EntailTests.

(** * Emptiness *)

Module EmptyTests.

  (** Canceling the repeated key of a row leaves a row with no variable. *)
  Example duplicate_keys_cancel :
    Certificates.check_empty [cancelled] [1] = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A rational solution of 2x = 1 is a model, so the system is not empty. *)
  Example rational_model_is_not_empty :
    Certificates.check_empty [LCons _ [(1%positive, 2)] REq 1] [1] = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two different keys do not cancel, so the row is not a contradiction. *)
  Example distinct_keys_do_not_cancel :
    Certificates.check_empty [LCons _ [(1%positive, 1); (2%positive, -1)] REq 1]
      [1] = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EmptyTests.

(** * Contradiction *)

Module ContradictionTests.

  (** A contradiction certifies any conclusion, including with scale zero. *)
  Example zero_scale_accepts_contradiction :
    Certificates.check_entails [cancelled] (LCons _ [] REq 5) (Cert [1] 0 false) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A contradiction certifies any conclusion, including with a negative scale. *)
  Example negative_scale_accepts_contradiction :
    Certificates.check_entails [cancelled] eq_x (Cert [1] (-2) true) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ContradictionTests.

(** * Cuts *)

Module CutTests.

  (** An integer cut rounds the bound 3/2 of 2x <= 3 down to x <= 1. *)
  Example integer_cut_rounds_down :
    Certificates.check_entails [twice_x] (LCons _ [(1%positive, 1)] RLe 1)
      (Cert [1] 2 true) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without an integer cut the same certificate does not reach x <= 1. *)
  Example rational_check_does_not_cut :
    Certificates.check_entails [twice_x] (LCons _ [(1%positive, 1)] RLe 1)
      (Cert [1] 2 false) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CutTests.
