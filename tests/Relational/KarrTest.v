(** * Linear equality fixtures

    These examples exercise elimination, affine hulls and raw coefficient normalization.
    For example, the hull of (0, 0) and (1, 1) retains x = y.
    Builds on: Key, ZLang, Linearize, LinCert and Karr. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Domains Require Import LangSig ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinCertSig Linearize LinCert Karr.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Forms := LinearizeCode PosKeyCode ZLangCode.
Module Certificates := LinCertCode PosKeyCode.
Module Equalities := KarrCode PosKeyCode ZLangCode Forms Certificates.

Definition x0 : lcons positive := LCons _ [(1%positive, 1)] REq 0.
Definition x1 : lcons positive := LCons _ [(1%positive, 1)] REq 1.
Definition y0 : lcons positive := LCons _ [(2%positive, 1)] REq 0.
Definition y1 : lcons positive := LCons _ [(2%positive, 1)] REq 1.
Definition same : lcons positive := LCons _ [(1%positive, 1); (2%positive, -1)] REq 0.

Example reached_empty_is_top : Equalities.leb (Reached [x1]) (Reached []) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example independent_equations_do_not_entail :
  Equalities.leb (Reached [x1]) (Reached [y1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example row_combination_is_detected :
  Equalities.leb (Reached [x1; y1]) (Reached [same]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example infeasible_left_is_below_unrelated_rows :
  Equalities.leb (Reached [x0; x1]) (Reached [y1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example infeasible_left_is_below_unreached :
  Equalities.leb (Reached [x0; x1]) Unreached = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example duplicate_keys_cancel_before_elimination :
  Equalities.is_bot
    (Reached [LCons _ [(1%positive, 1); (1%positive, -1)] REq 1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example literal_inequality_is_retained :
  let r := LCons _ [(1%positive, 1)] RLe 3 in
  Equalities.leb (Reached [r]) (Reached [r]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example inequality_is_not_treated_as_equality :
  Equalities.leb (Reached [LCons _ [(1%positive, 1)] RLe 1]) (Reached [x1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example unsupported_inequality_residual_is_rejected_before_checking :
  Equalities.target_certificate [LCons _ [(1%positive, 1)] RLe 0]
    (LCons _ [(1%positive, 2)] RLe 0) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrong_equality_residual_is_rejected_before_checking :
  Equalities.target_certificate [x0] x1 = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example stronger_inequality_residual_is_rejected_before_checking :
  Equalities.target_certificate [x1] (LCons _ [(1%positive, 1)] RLe 0) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example scaled_rational_row_is_detected :
  Equalities.leb (Reached [LCons _ [(1%positive, 2)] REq 1])
    (Reached [LCons _ [(1%positive, 4)] REq 2]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rational_solution_is_not_an_integer_contradiction :
  Equalities.is_bot (Reached [LCons _ [(1%positive, 2)] REq 1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example affine_hull_retains_the_diagonal :
  Equalities.leb (Equalities.join (Reached [x0; y0]) (Reached [x1; y1]))
    (Reached [same]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example affine_hull_drops_the_endpoint :
  Equalities.leb (Equalities.join (Reached [x0; y0]) (Reached [x1; y1]))
    (Reached [x0]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example havoc_preserves_an_eliminated_consequence :
  Equalities.leb (Equalities.havoc 1%positive (Reached [same; x1]))
    (Reached [y1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example havoc_frees_the_selected_variable :
  Equalities.leb (Equalities.havoc 1%positive (Reached [same; x1]))
    (Reached [x1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example substitution_merges_repeated_keys :
  Equalities.subst 1%positive (Lin _ [(2%positive, 1)] 3)
    (LCons _ [(1%positive, 2); (2%positive, 1)] REq 8) =
    LCons _ [(2%positive, 3)] REq 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example unsupported_assignment_uses_havoc :
  Equalities.assign 1%positive (Leaf 2%positive) (Reached [x1; y1]) =
    Equalities.havoc 1%positive (Reached [x1; y1]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Three nonunit pivots require exact division by earlier pivots. *)
Definition coupled : list (lcons positive) :=
  [LCons _ [(1%positive, 2); (2%positive, 1); (3%positive, 1)] REq 3;
   LCons _ [(1%positive, 1); (2%positive, 3); (3%positive, 2)] REq 5;
   LCons _ [(1%positive, 3); (3%positive, 4)] REq (-1)].

Example three_pivots_recover_the_unique_solution :
  Equalities.leb (Reached coupled)
    (Reached [x1; LCons _ [(2%positive, 1)] REq 2;
      LCons _ [(3%positive, 1)] REq (-1)]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example three_pivots_detect_a_late_contradiction :
  Equalities.is_bot
    (Reached (coupled ++ [LCons _ [(1%positive, 5); (2%positive, -2);
      (3%positive, 3)] REq 0])) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example pivot_exchange_preserves_the_solution :
  Equalities.leb
    (Reached [LCons _ [(2%positive, 2); (3%positive, 1)] REq 3;
      LCons _ [(1%positive, 3); (3%positive, 2)] REq 1;
      LCons _ [(1%positive, 1); (2%positive, 1)] REq 3])
    (Reached [x1; LCons _ [(2%positive, 1)] REq 2;
      LCons _ [(3%positive, 1)] REq (-1)]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example negative_pivots_preserve_the_solution :
  Equalities.leb
    (Reached [LCons _ [(1%positive, -2); (2%positive, -1);
      (3%positive, -1)] REq (-3);
      LCons _ [(1%positive, 1); (2%positive, 3); (3%positive, 2)] REq 5;
      LCons _ [(1%positive, 3); (3%positive, 4)] REq (-1)])
    (Reached [x1; LCons _ [(2%positive, 1)] REq 2;
      LCons _ [(3%positive, 1)] REq (-1)]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example canceled_private_pivots_leave_the_real_equations :
  Equalities.leb
    (Reached [LCons _ [(4%positive, 1); (4%positive, -1);
      (1%positive, 2); (2%positive, 1)] REq 4;
      LCons _ [(5%positive, 1); (5%positive, -1);
        (1%positive, 1); (2%positive, 3)] REq 7])
    (Reached [x1; LCons _ [(2%positive, 1)] REq 2]) = true.
Proof.
  vm_compute. reflexivity.
Qed.
